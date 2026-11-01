#!/usr/bin/env python3
"""Refresh paper text using Pandoc, or only the index from existing records.

The companion papers retain their imported bytes and provenance. This command
does not publish a revision, rebuild a PDF, or establish a mathematical claim.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import posixpath
import re
import subprocess
from urllib.parse import unquote, urlsplit
from pathlib import Path

if __package__:
    from . import paper_corpus_renderer as renderer
    from . import build_publication_taxonomy as taxonomy
    from .check_paper_corpus import reading_route_errors
else:
    import paper_corpus_renderer as renderer
    import build_publication_taxonomy as taxonomy
    from check_paper_corpus import reading_route_errors


def safe_path(root: Path, value: str, *, suffix: str) -> Path:
    relative = Path(value)
    if relative.is_absolute() or ".." in relative.parts or relative.suffix != suffix:
        raise ValueError(f"invalid corpus path: {value}")
    current = root
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError(f"symlink in corpus path: {value}")
    current.resolve().relative_to(root.resolve())
    return current


def digest(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def refresh_route(record: dict) -> None:
    route = record.get("first_pass")
    if route is None:
        return
    sections = {section["id"]: section for section in record["sections"]}
    entries = route.get("sections", [])
    if "stated_at" in route:
        entries = [*entries, route["stated_at"]]
    for entry in entries:
        section = sections.get(entry["id"])
        if section is None:
            raise ValueError(f"{record['paper_id']}: reading section {entry['id']} disappeared")
        entry["line"] = section["line"]
        if "title" in entry:
            entry["title"] = section["title"]
        entry.pop("resolved", None)
        entry.pop("reason", None)
    route["unresolved_count"] = 0


def mirror_provenance_context(record: dict, source: bytes, checkout: Path) -> dict[str, str]:
    """Read only the mirrored manuscript's recorded Git edition, never HEAD."""
    commit = record.get("canonical_source_commit", "")
    url = urlsplit(record.get("canonical_source_url") or "")
    match = re.fullmatch(r"/[^/]+/[^/]+/blob/([0-9a-f]{40})/(.+)", unquote(url.path))
    if (url.scheme != "https" or url.netloc != "github.com" or not match
            or not re.fullmatch(r"[0-9a-f]{40}", commit or "") or match[1] != commit):
        raise ValueError(f"{record['paper_id']}: missing or inconsistent immutable source pin")
    source_name = Path(match[2])
    if source_name.is_absolute() or ".." in source_name.parts:
        raise ValueError("invalid pinned source path")

    def read(name: Path, *, required: bool = False) -> bytes | None:
        result = subprocess.run(["git", "--no-replace-objects", "-C", str(checkout), "show", f"{commit}:{name.as_posix()}"],
                                capture_output=True, check=False)
        if result.returncode:
            if required:
                raise ValueError(f"{record['paper_id']}: pinned source unavailable in --source-checkout")
            return None
        return result.stdout

    if read(source_name, required=True) != source:
        raise ValueError(f"{record['paper_id']}: source checkout does not match recorded mirrored TeX bytes")
    # The original build root is the nearest ancestor declaring one of the
    # reviewed shared files. All reads stay within the very same Git commit.
    shared_root = None
    context = {}
    for parent in source_name.parents:
        found = {name: body for name in renderer._PROVENANCE_CONTEXT_FILES
                 if (body := read(parent / name)) is not None}
        if found:
            shared_root = parent
            context = {name: body.decode("utf-8") for name, body in found.items()}
            break
    if shared_root is None:
        return {}
    # Explicit relative inputs are accepted only when their original source
    # location resolves to that known shared file, not an arbitrary sibling.
    for name, body in [(source_name, source.decode("utf-8")),
                       *((shared_root / key, value) for key, value in list(context.items()))]:
        visible = renderer._provenance_visible(body)
        for item in re.findall(r"\\(?:input|include)\s*\{([^}]+)\}", visible):
            reference = item if Path(item).suffix else item + ".tex"
            basename = Path(reference).name
            if basename not in renderer._PROVENANCE_CONTEXT_FILES:
                continue
            target = (shared_root / basename if reference == basename else
                      Path(posixpath.normpath(str(name.parent / reference))))
            if target != shared_root / basename:
                raise ValueError(f"unsupported pinned provenance context path: {reference}")
            if basename in context:
                context[reference] = context[basename]
    return context


_DISCLOSURE_PARAGRAPH = re.compile(
    r"(?m)^\*(?:" + "|".join(re.escape(label) for label in renderer.PROVENANCE_NOTE_LABELS)
    + r")\*[^\n]*(?:\n(?!\n)[^\n]+)*"
)


def disclosure_only_text(record: dict, existing: str, source_note: str | None) -> tuple[str, list[dict]]:
    """Place the verified opening source-body note, preserving every other byte."""
    if (not source_note or "\n" in source_note.strip()
            or _DISCLOSURE_PARAGRAPH.fullmatch(source_note.strip()) is None):
        raise ValueError("disclosure-only refresh requires exactly one source-derived opening prose paragraph")
    source_note = source_note.strip()
    anchor = f'<a id="{Path(record["local_full_text"]).stem}"></a>'
    front_pattern = re.escape(anchor) + r"\n\n# [^\n]+\n\n"
    boundary = re.match(front_pattern, existing)
    if boundary is None or existing.count(anchor) != 1:
        raise ValueError("missing or ambiguous reading-copy opening title boundary")
    prior = list(_DISCLOSURE_PARAGRAPH.finditer(existing))
    if len(prior) > 1 or (prior and prior[0].start() != boundary.end()):
        raise ValueError("ambiguous or misplaced existing disclosure paragraph")
    end = prior[0].end() if prior else boundary.end()
    note = source_note + ("" if prior else "\n\n")
    markdown = existing[:boundary.end()] + note + existing[end:]
    sections = copy.deepcopy(record["sections"])
    lines = markdown.splitlines()
    original_lines = existing.splitlines()
    for section in sections:
        if section.get("line") is None:
            continue
        recorded_line = section["line"]
        if not 1 <= recorded_line <= len(original_lines):
            raise ValueError(f"missing recorded section anchor: {section['id']}")
        anchor_line = original_lines[recorded_line - 1]
        if f'id="{section["id"]}"' not in anchor_line:
            raise ValueError(f"missing recorded section anchor: {section['id']}")
        positions = [i + 1 for i, line in enumerate(lines) if line == anchor_line]
        if len(positions) != 1:
            raise ValueError(f"missing or ambiguous existing section anchor: {section['id']}")
        section["line"] = positions[0]
    return markdown, sections


def refresh(root: Path, *, write: bool, paper_ids: list[str] | None = None,
            index_only: bool = False, mirror_text_ids: list[str] | None = None,
            native_note_ids: list[str] | None = None, source_checkout: Path | None = None) -> dict:
    root = root.resolve()
    if source_checkout is not None and mirror_text_ids is None:
        raise ValueError("--source-checkout requires --mirror-text")
    corpus_path = safe_path(root, "docs/papers/corpus.json", suffix=".json")
    original = json.loads(corpus_path.read_text(encoding="utf-8"))
    corpus = copy.deepcopy(original)
    records = corpus["papers"]
    if index_only:
        if paper_ids or mirror_text_ids is not None or native_note_ids is not None:
            raise ValueError("--index-only cannot select manuscripts")
        output = safe_path(root, "docs/papers/README.md", suffix=".md")
        payload = renderer._readme([r for r in records if r.get("title")],
                                   corpus["this_repository"], root).encode()
        changed = [] if output.is_file() and output.read_bytes() == payload else ["docs/papers/README.md"]
        if write and changed:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(payload)
        return {"status": "written" if write else ("stale" if changed else "current"),
                "index_only": True, "changed": changed,
                "proof_or_pdf_rebuild_performed": False}
    native = {r["paper_id"] for r in records
              if r.get("relation_to_this_repository") == "native"}
    mirror_mode = mirror_text_ids is not None
    native_note_mode = native_note_ids is not None
    disclosure_mode = mirror_mode or native_note_mode
    if mirror_mode and native_note_mode:
        raise ValueError("--mirror-text cannot mix with --native-note")
    if native_note_mode:
        if paper_ids or not native_note_ids:
            raise ValueError("--native-note requires a nonempty native selection without --paper")
        selected = set(native_note_ids)
        for paper_id in selected:
            matches = [r for r in records if r.get("paper_id") == paper_id]
            if len(matches) != 1 or matches[0].get("relation_to_this_repository") != "native":
                raise ValueError(f"unknown or non-native note selection: {paper_id}")
    elif mirror_mode:
        if paper_ids or not mirror_text_ids:
            raise ValueError("--mirror-text requires a nonempty selection without --paper")
        selected = set(mirror_text_ids)
        for paper_id in selected:
            matches = [r for r in records if r.get("paper_id") == paper_id]
            if len(matches) != 1 or matches[0].get("relation_to_this_repository") != "mirror":
                raise ValueError(f"unknown or non-mirror paper selection: {paper_id}")
    else:
        selected = set(paper_ids) if paper_ids else native
        if selected - native:
            raise ValueError(f"unknown or non-native paper selection: {sorted(selected - native)}")
        if not selected:
            raise ValueError("this corpus has no native papers to refresh")
    targets = {}
    for record in records:
        pdf = record.get("local_pdf")
        if pdf:
            safe_path(root, pdf, suffix=".pdf")
            targets[Path(pdf).name] = posixpath.relpath(pdf, "docs/papers/full-text")
    plan: list[tuple[Path, bytes]] = []
    for record in records:
        if record.get("paper_id") not in selected:
            continue
        source = safe_path(root, record["local_source"], suffix=".tex")
        output = safe_path(root, record["local_full_text"], suffix=".md")
        output.relative_to(root / "docs/papers/full-text")
        source_bytes = source.read_bytes()
        if disclosure_mode:
            if digest(source_bytes) != record.get("source_sha256"):
                raise ValueError(f"{record['paper_id']}: source differs from its recorded hash")
            if record.get("local_pdf"):
                pdf = safe_path(root, record["local_pdf"], suffix=".pdf").read_bytes()
                if digest(pdf) != record.get("pdf_sha256"):
                    raise ValueError(f"{record['paper_id']}: PDF differs from its recorded hash")
        context = None
        if mirror_mode:
            context = (mirror_provenance_context(record, source_bytes, source_checkout)
                       if source_checkout is not None else {})
        converted = (renderer._convert(source, output.stem, provenance_context=context)
                     if mirror_mode else renderer._convert(source, output.stem))
        if disclosure_mode:
            markdown, sections = disclosure_only_text(record, output.read_bytes().decode("utf-8"), converted.get("opening_provenance_note"))
            record.update(sections=sections, section_count=len(sections))
        else:
            markdown = renderer._rewrite_exported_pdf_links(converted["markdown"], targets)
            if not converted.get("title"):
                raise ValueError(f"{record['paper_id']}: manuscript title is missing")
            source_digest = digest(source_bytes)
            if source_digest != record.get("source_sha256"):
                if record.get("canonical_source_commit"):
                    record["previous_published_source"] = {
                        key: record.get(key) for key in
                        ("canonical_source_commit", "canonical_source_url", "source_sha256")
                    }
                record["canonical_source_commit"] = None
                record["canonical_source_pin_status"] = "local_unpublished"
                record["canonical_source_url"] = None
                record["canonical_source_raw_url"] = None
            record.update(title=converted["title"], title_source="manuscript",
                          source_sha256=source_digest, sections=converted["sections"],
                          section_count=len(converted["sections"]),
                          citations_rendered=converted["citations_rendered"])
            if converted.get("subtitle"):
                record["subtitle"] = converted["subtitle"]
            else:
                record.pop("subtitle", None)
            fallback = record.get("fallback_title_drift")
            if fallback:
                if fallback["registry_fallback"] == converted["title"]:
                    record.pop("fallback_title_drift")
                else:
                    fallback["manuscript_title"] = converted["title"]
            if record.get("local_pdf"):
                pdf = safe_path(root, record["local_pdf"], suffix=".pdf").read_bytes()
                record.update(pdf_sha256=digest(pdf), pdf_byte_count=len(pdf))
        refresh_route(record)
        errors = reading_route_errors(record, markdown)
        if errors:
            raise ValueError(f"{record['paper_id']}: {'; '.join(errors)}")
        plan.append((output, markdown.encode()))
    # A note-only refresh must not reclassify an older reading-copy edition.
    # Its existing taxonomy and publication fields are outside this operation.
    if not disclosure_mode:
        corpus = taxonomy.build(corpus, root)
    records = corpus["papers"]
    if disclosure_mode:
        # Rendering a pinned copy must not become a publication or source update.
        mutable = {"sections", "section_count", "citations_rendered", "first_pass"}
        for before, after in zip(original["papers"], records, strict=True):
            if before.get("paper_id") not in selected:
                if before != after:
                    raise ValueError("disclosure-only refresh would change another paper record")
            elif ({key: value for key, value in before.items() if key not in mutable}
                  != {key: value for key, value in after.items() if key not in mutable}):
                raise ValueError(f"{before['paper_id']}: disclosure-only refresh would change source or publication metadata")
    plan.extend([
        (corpus_path, (json.dumps(corpus, indent=2) + "\n").encode()),
        (safe_path(root, "docs/papers/README.md", suffix=".md"),
         renderer._readme([r for r in records if r.get("title")],
                          corpus["this_repository"], root).encode()),
    ])
    changed = []
    for path, payload in plan:
        if path.is_file() and path.read_bytes() == payload:
            continue
        changed.append(str(path.relative_to(root)))
        if write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
    return {"status": "written" if write else ("stale" if changed else "current"),
            **({"mirror_text_papers": sorted(selected)} if mirror_mode else
               {"native_note_papers": sorted(selected)} if native_note_mode else
               {"native_papers": sorted(selected)}), "changed": changed,
            "proof_or_pdf_rebuild_performed": False}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--paper", action="append", help="refresh one existing native paper id")
    selection.add_argument("--native-note", action="append", help="refresh only an existing native paper disclosure from unchanged recorded source and PDF bytes")
    selection.add_argument("--mirror-text", action="append", help="refresh only an existing mirror disclosure from unchanged recorded source and PDF bytes")
    parser.add_argument("--source-checkout", type=Path, help="read shared note definitions from the mirror's exact pinned Git commit")
    parser.add_argument("--index-only", action="store_true", help="render only the paper index from existing corpus records, without Pandoc")
    args = parser.parse_args()
    try:
        result = refresh(args.root, write=args.write, paper_ids=args.paper,
                         index_only=args.index_only, mirror_text_ids=args.mirror_text,
                         native_note_ids=args.native_note, source_checkout=args.source_checkout)
    except (OSError, ValueError, KeyError, RuntimeError) as error:
        parser.exit(2, f"paper refresh: {error}\n")
    print(json.dumps(result, indent=2))
    return int(args.check and bool(result["changed"]))


if __name__ == "__main__":
    raise SystemExit(main())
