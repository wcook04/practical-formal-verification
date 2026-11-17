#!/usr/bin/env python3
"""Check Compatibility's source binding; optionally rebuild its complete Dafny proof.

The default checks retained source/generated hashes only. Supply --dafny to
verify the relation, witness and verdict proofs, regenerate and compare the
deployed Python, then reject all five negative proof fixtures. No prover is needed to use
the installed Compatibility operation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
VERSION = "4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2"
GENERATED_FILES = frozenset({
    "Compatibility.py", "Replay.py", "Verdict.py", "module_.py", "__main__.py",
    "System_/__init__.py", "_dafny/__init__.py",
})
PROOF = runpy.run_path(str(ROOT / "scripts/check/check_component_kernels.py"))
SOURCES = {"Replay.dfy": "source_sha256",
           "Compatibility.dfy": "dependency_source_sha256",
           "negative/CompatibilityOutputMutant.dfy": "negative_source_sha256",
           "negative/ReplayStaleInputMutant.dfy": "replay_negative_source_sha256",
           "negative/ReplayMissedDifferenceMutant.dfy": "completeness_negative_source_sha256",
           "Verdict.dfy": "verdict_source_sha256",
           "VerdictExists.dfy": "verdict_exists_source_sha256",
           "negative/VerdictMissedLaterDifferenceMutant.dfy": "verdict_negative_source_sha256",
           "negative/VerdictAnyShortestWordMutant.dfy": "verdict_order_negative_source_sha256"}
INCLUDES = {"Replay.dfy": ("Compatibility.dfy",),
            "negative/ReplayStaleInputMutant.dfy": ("../Compatibility.dfy",),
            "negative/ReplayMissedDifferenceMutant.dfy": ("../Compatibility.dfy",),
            "Verdict.dfy": ("Replay.dfy",),
            "VerdictExists.dfy": ("Verdict.dfy",),
            "negative/VerdictMissedLaterDifferenceMutant.dfy": ("../Replay.dfy",),
            "negative/VerdictAnyShortestWordMutant.dfy": ("../Replay.dfy",)}
# Expected (verified, errors) for each Dafny run that the verdict checker adds.
VERDICT_COUNTS = {"verdict_build_verified_tasks": 69,
                  "verdict_exists_verified_tasks": 91,
                  "verdict_negative_verified_tasks": 26,
                  "verdict_negative_errors": 2,
                  "verdict_order_negative_verified_tasks": 26,
                  "verdict_order_negative_errors": 3}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _source_snapshot(formal: Path, metadata: dict) -> dict[str, bytes]:
    snapshot = {}
    for name, key in SOURCES.items():
        source = PROOF["_source_text"](formal / name,
                                       includes=INCLUDES.get(name, ())).encode("utf-8")
        if hashlib.sha256(source).hexdigest() != metadata[key]:
            raise ValueError("formal source identity changed: " + name)
        snapshot[name] = source
    return snapshot


def check_binding(root: Path, generated: Path) -> dict:
    formal = root / "formal/compatibility"
    metadata = PROOF["_read_json"](formal / "metadata.json")
    manifest = PROOF["_read_json"](generated / "GENERATED_SHA256.json")
    if (type(metadata["schema_version"]) is not int or metadata["schema_version"] != 1
            or metadata["source"] != "Replay.dfy"
            or metadata["dependency_source"] != "Compatibility.dfy"
            or metadata["negative_source"] != "negative/CompatibilityOutputMutant.dfy"
            or metadata["replay_negative_source"] != "negative/ReplayStaleInputMutant.dfy"
            or metadata["completeness_negative_source"] != "negative/ReplayMissedDifferenceMutant.dfy"
            or metadata["dafny_version"] != VERSION
            or metadata["verified_tasks"] != 41
            or metadata["negative_verified_tasks"] != 13
            or metadata["negative_errors"] != 1
            or metadata["replay_negative_verified_tasks"] != 37
            or metadata["replay_negative_errors"] != 9
            or metadata["completeness_negative_verified_tasks"] != 40
            or metadata["completeness_negative_errors"] != 1
            or any(metadata[key] != value for key, value in VERDICT_COUNTS.items())
            or set(manifest) != GENERATED_FILES
            or metadata["generated_python"] != manifest):
        raise ValueError("unexpected toolchain or generated-file manifest")
    sources = _source_snapshot(formal, metadata)
    for name, expected in manifest.items():
        if digest(generated / name) != expected:
            raise ValueError("generated Python identity changed: " + name)
    source = sources["Compatibility.dfy"].decode("utf-8")
    expected_mutant = source.replace(
        "newOutput[t][a] == oldOutput[s][a] &&",
        "true && // MUTANT: matching output obligation removed", 1)
    if (source.count("newOutput[t][a] == oldOutput[s][a] &&") != 1 or expected_mutant
            != sources["negative/CompatibilityOutputMutant.dfy"].decode("utf-8")):
        raise ValueError("negative fixture must remove only output equality")
    replay = sources["Replay.dfy"].decode("utf-8")
    stale_guard = "approved.next[s][word[0]] < 0\n      then false"
    if replay.count(stale_guard) != 1:
        raise ValueError("expected one stale-input replay guard")
    expected_replay_mutant = replay.replace(
        'include "Compatibility.dfy"', 'include "../Compatibility.dfy"').replace(
        stale_guard, "approved.next[s][word[0]] < 0\n      then true", 1)
    if (expected_replay_mutant == replay or expected_replay_mutant
            != sources["negative/ReplayStaleInputMutant.dfy"].decode("utf-8")):
        raise ValueError("negative replay fixture must change only the stale-input decision")
    difference_decision = ("approved.output[s][word[0]] != candidate.output[t][word[0]]\n"
                           "      then true")
    if replay.count(difference_decision) != 1:
        raise ValueError("expected one replay discrepancy decision")
    expected_completeness_mutant = replay.replace(
        'include "Compatibility.dfy"', 'include "../Compatibility.dfy"').replace(
        difference_decision, difference_decision.removesuffix("true") + "t == candidate.initial", 1)
    if (expected_completeness_mutant == replay or expected_completeness_mutant
            != sources["negative/ReplayMissedDifferenceMutant.dfy"].decode("utf-8")):
        raise ValueError("negative completeness fixture must change only the discrepancy decision")
    verdict = sources["Verdict.dfy"].decode("utf-8")
    never_closed = ("        else if labels[s][t] == Never then\n"
                    "          labels[approved.next[s][a]][candidate.next[t][a]] == Never\n")
    smaller_inputs = ("    else if !SmallerInputsRuledOut(approved, candidate, labels,"
                      " s, t, word[0], |word|)\n      then false\n")
    for name, before, after in (
            ("negative/VerdictMissedLaterDifferenceMutant.dfy", never_closed,
             "        else if labels[s][t] == Never then\n          true\n"),
            ("negative/VerdictAnyShortestWordMutant.dfy", smaller_inputs, "")):
        expected = verdict.replace('include "Replay.dfy"', 'include "../Replay.dfy"')
        if verdict.count(before) != 1 or expected.replace(before, after, 1) != sources[name].decode("utf-8"):
            raise ValueError("negative verdict fixture must change only its declared test: " + name)
    if not (generated / "Dafny-LICENSE.txt").is_file():
        raise ValueError("Dafny runtime licence is missing")
    # Check the whole importable inventory and the loader's reviewed byte pins.
    # Hashing the named .py files alone misses a same-named package shadow.
    loader = runpy.run_path(str(root / "src/plectis/_sealed_kernel.py"))
    loader["read_kernel_snapshot"](generated, "Compatibility")
    return {"source_sha256": metadata["source_sha256"],
            "dependency_source_sha256": metadata["dependency_source_sha256"],
            "negative_source_sha256": metadata["negative_source_sha256"],
            "replay_negative_source_sha256": metadata["replay_negative_source_sha256"],
            "completeness_negative_source_sha256": metadata["completeness_negative_source_sha256"],
            **{key: metadata[key] for key in SOURCES.values() if key.startswith("verdict")},
            "generated_python": manifest}


def run(argv: list[str], *, cwd: Path, env: dict[str, str]) -> subprocess.CompletedProcess:
    return PROOF["_run"](argv, cwd=cwd, env=env)


def reprove(root: Path, generated: Path, executable: str, *, expected_binding=None) -> dict:
    binding = check_binding(root, generated)
    if expected_binding is not None and expected_binding != binding:
        raise ValueError("compatibility binding changed before proof snapshot")
    sources = _source_snapshot(root / "formal/compatibility", binding)
    found = shutil.which(executable)
    if found is None:
        raise ValueError("Dafny executable not found: " + executable)
    dafny = str(Path(found).resolve())
    env = os.environ.copy()
    env.setdefault("DOTNET_GCHeapHardLimit", "0x20000000")
    formal = root / "formal/compatibility"
    version = run([dafny, "--version"], cwd=formal, env=env)
    if version.returncode or version.stdout.strip() != VERSION:
        raise ValueError("replay requires the exact pinned Dafny 4.11.0 build")
    with tempfile.TemporaryDirectory(prefix="plectis-compatibility-proof-") as directory:
        work = Path(directory)
        for name, source in sources.items():
            target = work / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(source)
        # Verdict.dfy includes Replay.dfy and Compatibility.dfy: 41 tasks for
        # those two files and 28 for the verdict checker.
        build = run([dafny, "build", "--target:py", "--verify-included-files",
                     str(work / "Verdict.dfy"),
                     "--verification-time-limit", "120", "--cores", "1"],
                    cwd=work, env=env)
        PROOF["_proof_result"](build, VERDICT_COUNTS["verdict_build_verified_tasks"], 0)
        rebuilt = work / "Verdict-py"
        files = {p.relative_to(rebuilt).as_posix() for p in rebuilt.rglob("*.py")}
        if files != GENERATED_FILES:
            raise ValueError("compiler generated an unexpected file set")
        for name in files:
            if (rebuilt / name).read_bytes() != (generated / name).read_bytes():
                raise ValueError("deployed Python differs from verified build: " + name)
        mutation = run([dafny, "verify",
                        str(work / "negative/CompatibilityOutputMutant.dfy"),
                        "--verification-time-limit", "30", "--cores", "1"],
                       cwd=work, env=env)
        PROOF["_proof_result"](mutation, 13, 1, negative=True)
        replay_mutation = run([dafny, "verify", "--verify-included-files",
                               str(work / "negative/ReplayStaleInputMutant.dfy"),
                               "--verification-time-limit", "30", "--cores", "1"],
                              cwd=work, env=env)
        PROOF["_proof_result"](replay_mutation, 37, 9, negative=True)
        completeness_mutation = run([dafny, "verify", "--verify-included-files",
                                     str(work / "negative/ReplayMissedDifferenceMutant.dfy"),
                                     "--verification-time-limit", "30", "--cores", "1"],
                                    cwd=work, env=env)
        PROOF["_proof_result"](completeness_mutation, 40, 1, negative=True)
        exists = run([dafny, "verify", "--verify-included-files",
                      str(work / "VerdictExists.dfy"),
                      "--verification-time-limit", "120", "--cores", "1"],
                     cwd=work, env=env)
        PROOF["_proof_result"](exists, VERDICT_COUNTS["verdict_exists_verified_tasks"], 0)
        for name, prefix in (("negative/VerdictMissedLaterDifferenceMutant.dfy", "verdict_negative"),
                             ("negative/VerdictAnyShortestWordMutant.dfy", "verdict_order_negative")):
            mutant = run([dafny, "verify", str(work / name),
                          "--verification-time-limit", "120", "--cores", "1"],
                         cwd=work, env=env)
            PROOF["_proof_result"](mutant, VERDICT_COUNTS[prefix + "_verified_tasks"],
                                   VERDICT_COUNTS[prefix + "_errors"], negative=True)
    return {"dafny_version": VERSION, "clean_verified_tasks": 41, "clean_errors": 0,
            "negative_verified_tasks": 13, "negative_errors": 1,
            "replay_negative_verified_tasks": 37,
            "replay_negative_errors": 9,
            "completeness_negative_verified_tasks": 40,
            "completeness_negative_errors": 1,
            **VERDICT_COUNTS,
            "regenerated_python_byte_identical": True}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-root", type=Path)
    parser.add_argument("--dafny", help="Official pinned Dafny 4.11.0 executable")
    args = parser.parse_args()
    root = args.root.resolve()
    generated = (args.generated_root or root / "src/plectis/compatibility/_generated").resolve()
    try:
        binding = check_binding(root, generated)
        proof = (reprove(root, generated, args.dafny, expected_binding=binding)
                 if args.dafny else {})
    except (OSError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        print(json.dumps({"status": "fail", "error": str(error)}))
        return 1
    print(json.dumps({"status": "pass", "mode": "formal_replay" if proof else "hash_binding_only",
                      **binding, **proof,
                      "authority_ceiling": "supplied finite deterministic partial Mealy tables",
                      "anti_claim": "Accepted relations preserve all finite old-admissible traces; the replay checker detects exactly the words with a differing approved-admissible prefix; an accepted verdict is the unique first shortest difference or the absence of any. No proof of parser, search, encoding, concrete-program correspondence, liveness or external effects.",
                      "secret_exclusion_scan": "not_performed_by_this_checker",
                      "receipt_paths": []}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
