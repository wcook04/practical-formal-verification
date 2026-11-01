"""The generated paper corpus must still describe this repository's manuscripts.

``docs/papers/`` is generated: available papers are copied or converted to
Markdown and indexed by a tool in the private system repository. Some registry
rows may remain explicitly unavailable when their source was not present at
export time.

What is checked is the thing that can be checked locally and cheaply, and it is
the failure that actually happens: someone edits a manuscript and the generated
text silently keeps describing the previous one. ``corpus.json`` records the
SHA-256 of every manuscript it was built from, so comparing hashes catches that.

The shipped checker is ``scripts/papers/check_paper_corpus.py``; it is copied into
this repository by the export, so this module invokes it rather than restating
its logic.
"""

from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
CORPUS_DIR = REPO_ROOT / "docs" / "papers"
CORPUS = CORPUS_DIR / "corpus.json"
CHECKER = REPO_ROOT / "scripts/papers/check_paper_corpus.py"


def test_corpus_is_present() -> None:
    assert CORPUS.is_file(), "docs/papers/corpus.json is missing; re-run the export"
    assert CHECKER.is_file(), "scripts/papers/check_paper_corpus.py is missing"


def test_shipped_checker_reports_the_corpus_is_current() -> None:
    result = subprocess.run(
        [sys.executable, str(CHECKER)],
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr


def test_every_recorded_manuscript_hash_matches() -> None:
    """The same comparison, made here so a failure names the paper directly."""
    corpus = json.loads(CORPUS.read_text(encoding="utf-8"))
    checked = 0
    for paper in corpus["papers"]:
        if paper.get("availability") == "unavailable_at_build":
            continue
        source = REPO_ROOT / paper["local_source"]
        assert source.is_file(), f"{paper['paper_id']}: {paper['local_source']} is missing"
        digest = "sha256:" + hashlib.sha256(source.read_bytes()).hexdigest()
        assert digest == paper["source_sha256"], (
            f"{paper['paper_id']}: {paper['local_source']} has changed since the "
            "corpus was generated; re-run the export in the private system repository"
        )
        checked += 1
    assert checked > 0, "the corpus contains no locally checkable manuscripts"
    assert checked == sum("local_source" in paper for paper in corpus["papers"])


def test_unavailable_rows_are_explicit_and_non_deceptive() -> None:
    """An absent registered paper must not look like a locally inspectable one."""
    corpus = json.loads(CORPUS.read_text(encoding="utf-8"))
    unavailable = [
        paper
        for paper in corpus["papers"]
        if paper.get("availability") == "unavailable_at_build"
    ]
    for paper in unavailable:
        assert paper.get("reason")
        assert "local_source" not in paper
        assert "local_full_text" not in paper


@pytest.mark.parametrize("relation", ["native", "mirror"])
def test_every_paper_declares_where_its_authority_lives(relation: str) -> None:
    """A mirror that does not say it is a mirror would move authority by copying."""
    corpus = json.loads(CORPUS.read_text(encoding="utf-8"))
    matching = [
        paper
        for paper in corpus["papers"]
        if paper.get("relation_to_this_repository") == relation
    ]
    assert matching, f"no paper is marked {relation!r}"
    for paper in matching:
        assert paper["home_repository"]
        assert paper["not_authority_for"]
        if relation == "mirror":
            assert paper["home_repository"] != "plectis"
            assert "mirror_note" in paper
        else:
            assert paper["home_repository"] == "plectis"


def test_section_line_numbers_point_at_their_anchors() -> None:
    """The index is only useful if its line numbers are true."""
    corpus = json.loads(CORPUS.read_text(encoding="utf-8"))
    for paper in corpus["papers"]:
        if paper.get("availability") == "unavailable_at_build":
            continue
        lines = (REPO_ROOT / paper["local_full_text"]).read_text(
            encoding="utf-8"
        ).splitlines()
        for section in paper["sections"]:
            line = section.get("line")
            if line is None:
                continue
            assert f'id="{section["id"]}"' in lines[line - 1], (
                f"{paper['paper_id']}: section {section['id']} is recorded at line "
                f"{line}, which does not carry its anchor"
            )


# Derived from each exact source_sha256 and, for mirrors, the known shared
# definitions read from canonical_source_commit with Git replacements disabled.
# This records normalized paragraph digests, not substitute disclosure prose.
# It lets an offline clone detect both omission and profile substitution even
# though original upstream shared preambles are not shipped with mirror TeX.
_SOURCE_DISCLOSURE_DIGESTS = {
    # erdos-68-factorial-denominator-irrationality
    'sha256:7a9b37c07700cdf95a6614c2e98d9b6a01e62eeec14d39b03a3fd623fa900f81': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos68-factorial-reasoning-surface
    'sha256:a1e8e011af99f3c74e9facc32be9c5cebcb8f5977652e5c47b57a1de4d0e7169': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos-243-reciprocal-tail-rigidity
    'sha256:1e9a3ab22bf1b3bb60d60d587ce1d17121c39b6a5db79404e0275e5f38d72be6': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos243-reciprocal-tail-reasoning-surface
    'sha256:5cb3f168714dd3d9658a7830be41d213b9493c4bc3046421b40586cc676bc5ea': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos-249-binary-totient-series
    'sha256:b1f44a81d1e5e4eda4f6c4ee8955bc2e22779fc10e2d370581356aaed668a8fe': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos249-totient-reasoning-surface
    'sha256:8e35779332d1eb61f6f745b9c7d49613ceb654f2dc92262d62563941c683b7bc': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos-251-prime-gap-dyadic-series
    'sha256:ddc51a73fab16e533cf890e113f01cfa34658f1197ac85de3940da066cbdd41c': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos251-prime-gap-reasoning-surface
    'sha256:d151bccef2113d3131ad8f8980bc1a9336e79ccf12e5a20a2490040638728c38': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos-257-mersenne-support-subseries
    'sha256:fc88570d017fbc97be2553c27cb3c6ed218ddc46b0fa311860814914537808e8': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos257-mersenne-reasoning-surface
    'sha256:688a8e8dcd728c79b89d58aec10c6203429d9223e0fa44adcbb8bde7e312091b': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos269-running-lcm-reasoning-surface
    'sha256:8ad4751fea8b1611a65400e2ad283725e155b0ee0499fe5ca6e727a24645971d': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos-269-three-prime-running-lcm
    'sha256:bc1d183a2accf273b46c64c014c1f9f0b3c5f0d009a7548d0dec6632094d6726': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos-1041-lemniscate-newton-flow
    'sha256:a5a6f75b996d2d8b6751e064414516d42c6ded18ac8c0818431bfd715fab1744': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos1041-lemniscate-reasoning-surface
    'sha256:91cac94ec9296e643a61bd89580a294c44fbae5cf17afd6975682a3b2522f76b': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos-1049-rational-base-lambert
    'sha256:7444fdc6ce71c5b49487e0bfc58bdbd974d75918b5e0b7cafee946a551f556b9': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # erdos1049-rational-base-lambert-reasoning-surface
    'sha256:feb1594783aaa4db000596f35cfc4bb09cef6c804455dbe4da84015fd23fc3cf': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # optimal-sparse-perturbations
    'sha256:15e5174aa5a2cf6268cd28f0fc353e212ba2fff64561c230325d36d56f90e34d': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # claim-faithful-publication-systems
    'sha256:fefda86309ab84283d9fb87bfa0a4334796eb8a4ab2562ef16664095225beb7d': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # cold-clone-to-proof-receipt
    'sha256:c1803808df7ee8142298820360a887283ee2ace7c61b9930ad99477a188bea5a': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '068971525603e6515efe024187479e05d206cbf7b64c3be5fe28541853039b6c'),
    # open-source-mathematics-strategy
    'sha256:3548d9c753a2ccf2d61166fee710d72a50fc4df86937a96f40694df0c79e0f12': ('a08529a329578d172a9a2e602bacba4a8cc760cd', '703983ffb8dc92571e73fece11ee63faf40770009ec82165e51cc547c2c7f619'),
    # plectis-public-system
    'sha256:d5961a0dfc2db8091d50059f011a1823cd3bc5fc8fb1a3d3919b15066bdb1511': (None, '35756ffb24dff3b1c643132d3d0f6bc919a677918418b1a54526e98113bcd050'),
}


def disclosure_paragraph(markdown: str) -> str:
    paragraphs = [part for part in markdown.split("\n\n")
                  if re.match(r"\*+(?:Authorship and AI use\.|AI assistance\.)", part)]
    assert len(paragraphs) == 1, "expected exactly one explicit production disclosure paragraph"
    return " ".join(paragraphs[0].replace("*", "").split())


def test_every_source_disclosure_survives_in_its_reading_copy() -> None:
    corpus = json.loads(CORPUS.read_text(encoding="utf-8"))
    checked = set()
    for paper in corpus["papers"]:
        if not paper.get("local_source"):
            continue
        source = (REPO_ROOT / paper["local_source"]).read_text(encoding="utf-8")
        assert re.search(r"\\(?:provenancenote|noteprovenance|paperprovenance)\b", source), paper["paper_id"]
        pin, expected = _SOURCE_DISCLOSURE_DIGESTS[paper["source_sha256"]]
        assert paper.get("canonical_source_commit") == pin, paper["paper_id"]
        text = (REPO_ROOT / paper["local_full_text"]).read_text(encoding="utf-8")
        note = disclosure_paragraph(text)
        assert hashlib.sha256(note.encode()).hexdigest() == expected, paper["paper_id"]
        checked.add(paper["source_sha256"])
    assert checked == set(_SOURCE_DISCLOSURE_DIGESTS)


@pytest.mark.parametrize("markdown", [
    "# Paper\n\nDiscussion of AI elsewhere is not a disclosure.\n",
    "*Authorship and AI use.* One note.\n\n*Authorship and AI use.* Another note.\n",
])
def test_disclosure_guard_rejects_missing_or_duplicate_notes(markdown: str) -> None:
    with pytest.raises(AssertionError, match="exactly one"):
        disclosure_paragraph(markdown)


def test_disclosure_guard_rejects_a_different_review_profile() -> None:
    source = "sha256:d5961a0dfc2db8091d50059f011a1823cd3bc5fc8fb1a3d3919b15066bdb1511"
    substituted = disclosure_paragraph("*AI assistance.* An independently reviewed manuscript.\n")
    assert hashlib.sha256(substituted.encode()).hexdigest() != _SOURCE_DISCLOSURE_DIGESTS[source][1]


@pytest.mark.skipif(not shutil.which("pandoc"), reason="Pandoc required for real source conversion")
@pytest.mark.parametrize("paper_id", ["plectis-public-system", "open-source-mathematics-strategy"])
def test_explicit_source_note_survives_actual_pandoc(paper_id: str) -> None:
    # These manuscripts carry their exact note argument locally; no upstream
    # shared context or canned production profile is needed for the comparison.
    corpus = json.loads(CORPUS.read_text(encoding="utf-8"))
    paper = next(row for row in corpus["papers"] if row["paper_id"] == paper_id)
    source = REPO_ROOT / paper["local_source"]
    command = (
        "import sys; from pathlib import Path; "
        "sys.path.insert(0, sys.argv[1]); import paper_corpus_renderer as r; "
        "print(r._convert(Path(sys.argv[2]), sys.argv[3])['markdown'])"
    )
    rendered = subprocess.run([sys.executable, "-c", command, str(REPO_ROOT / "scripts/papers"),
                               str(source), Path(paper["local_full_text"]).stem],
                              capture_output=True, text=True, check=True).stdout
    actual = (REPO_ROOT / paper["local_full_text"]).read_text(encoding="utf-8")
    assert disclosure_paragraph(actual) == disclosure_paragraph(rendered)


def test_every_reading_copy_is_indexed_by_the_corpus() -> None:
    corpus = json.loads(CORPUS.read_text(encoding='utf-8'))
    indexed = {paper['local_full_text'] for paper in corpus['papers']
               if paper.get('local_full_text')}
    actual = {path.relative_to(REPO_ROOT).as_posix()
              for path in (CORPUS_DIR/'full-text').rglob('*.md')}
    assert actual == indexed, {
        'unindexed_reading_copies': sorted(actual-indexed),
        'missing_reading_copies': sorted(indexed-actual),
    }
