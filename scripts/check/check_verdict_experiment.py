#!/usr/bin/env python3
"""Reprove the verdict checker and run six searches against its compiled form.

`plectis.compatibility.compare` calls the same checker on its own search. This
script shows that other searches can take its place: three honest ones are
always accepted, and three wrong ones are refused whenever their answer is
wrong. Requires the pinned Dafny build; there is no handwritten Python copy
of the checker to fall back on.
"""

from __future__ import annotations

import argparse
import itertools
import json
import os
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
VERSION = "4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2"
FORMAL = ROOT / "formal/compatibility"
SOURCE = "Verdict.dfy"
# Each broken checker must fail with exactly these counts.
MUTANTS = {"negative/VerdictMissedLaterDifferenceMutant.dfy": (26, 2),
           "negative/VerdictAnyShortestWordMutant.dfy": (27, 2)}
VERIFIED = 28
EXISTS_VERIFIED = 22

DRIVER = r'''
import json, sys
import _dafny, Replay, Verdict
seq = _dafny.Seq
def matrix(rows): return seq([seq(row) for row in rows])
answers = []
for case in json.load(sys.stdin):
    old = Replay.Model_Model(matrix(case["old"][0]), matrix(case["old"][1]),
                             case["old"][2], case["inputs"])
    new = Replay.Model_Model(matrix(case["new"][0]), matrix(case["new"][1]),
                             case["new"][2], case["inputs"])
    verdict = (Verdict.Verdict_Compatible() if case["word"] is None
               else Verdict.Verdict_Differs(seq(case["word"])))
    answer = Verdict.default__.Check(old, new, matrix(case["labels"]), verdict)
    assert type(answer) is bool
    answers.append(answer)
json.dump(answers, sys.stdout)
'''


def run(argv, cwd, env=None, stdin=None):
    return subprocess.run(argv, cwd=cwd, env=env, input=stdin, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          check=False, timeout=900)


def counts(result):
    found = re.search(r"finished with (\d+) verified, (\d+) errors?", result.stdout)
    if not found:
        raise ValueError("no Dafny verdict in output:\n" + result.stdout[-2000:])
    return int(found.group(1)), int(found.group(2))


def oracle(old, new, inputs):
    """First shortest differing word by direct enumeration, or None."""
    def differs(word):
        s, t = old[2], new[2]
        for a in word:
            if old[0][s][a] < 0:
                return False
            if new[0][t][a] < 0 or old[1][s][a] != new[1][t][a]:
                return True
            s, t = old[0][s][a], new[0][t][a]
        return False
    for length in range(1, len(old[0]) * len(new[0]) + 1):
        for word in itertools.product(range(inputs), repeat=length):
            if differs(word):
                return list(word)
    return None


def machines(states, inputs):
    cells = [(-1, -1)] + [(n, o) for n in range(states) for o in range(2)]
    for rows in itertools.product(itertools.product(cells, repeat=inputs),
                                  repeat=states):
        for initial in range(states):
            yield ([[c[0] for c in row] for row in rows],
                   [[c[1] for c in row] for row in rows], initial)


def cases():
    small = list(machines(2, 1))
    for old in small:
        for new in small:
            yield old, new, 1
    rng = random.Random(20261117)
    for _ in range(1500):
        inputs = rng.choice((2, 3))
        def machine():
            states = rng.choice((2, 3))
            cells = [(-1, -1)] + [(n, o) for n in range(states) for o in range(2)]
            rows = [[rng.choice(cells) for _ in range(inputs)] for _ in range(states)]
            return ([[c[0] for c in row] for row in rows],
                    [[c[1] for c in row] for row in rows], rng.randrange(states))
        yield machine(), machine(), inputs
    # Eighteen steps before the only difference.
    chain = [[i + 1] for i in range(18)] + [[18]]
    yield ((chain, [[0]] * 19, 0), (chain, [[0]] * 18 + [[1]], 0), 1)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dafny", metavar="PATH", required=True)
    args = parser.parse_args(argv)
    found = shutil.which(args.dafny)
    if found is None:
        raise SystemExit("Dafny executable not found")
    dafny = str(Path(found).resolve())
    env = os.environ.copy()
    env.setdefault("DOTNET_GCHeapHardLimit", "0x20000000")
    if run([dafny, "--version"], ROOT, env).stdout.strip() != VERSION:
        raise SystemExit("requires the pinned official Dafny 4.11.0 build")
    sys.path.insert(0, str(ROOT / "examples/operations"))
    import verdict_searches as searches

    with tempfile.TemporaryDirectory(prefix="verdict-") as directory:
        work = Path(directory)
        shutil.copytree(FORMAL, work / "formal")
        limits = ["--verification-time-limit", "120", "--cores", "1"]
        build = run([dafny, "build", "--target:py", str(work / "formal" / SOURCE),
                     *limits], work, env)
        if build.returncode or counts(build) != (VERIFIED, 0):
            raise SystemExit("verdict checker did not verify:\n" + build.stdout[-3000:])
        exists = run([dafny, "verify", str(work / "formal" / "VerdictExists.dfy"),
                      *limits], work, env)
        if exists.returncode or counts(exists) != (EXISTS_VERIFIED, 0):
            raise SystemExit("existence proof did not verify:\n" + exists.stdout[-3000:])
        for name, expected in MUTANTS.items():
            negative = run([dafny, "verify", str(work / "formal" / name), *limits],
                           work, env)
            if counts(negative) != expected:
                raise SystemExit(f"{name}: expected {expected}, got {counts(negative)}")

        problems = list(cases())
        truth = [oracle(*problem) for problem in problems]
        batch, owners = [], []
        for index, (old, new, inputs) in enumerate(problems):
            for search in searches.HONEST + searches.WRONG:
                word, labels = search(old, new, inputs)
                batch.append({"old": old, "new": new, "inputs": inputs,
                              "word": word, "labels": labels})
                owners.append((search.__name__, index, word))
        compiled = work / "formal" / "Verdict-py"
        checked = run([sys.executable, "-I", "-B", "-c",
                       "import sys; sys.path.insert(0, sys.argv[1]); "
                       "exec(sys.argv[2])",
                       str(compiled), DRIVER], work, stdin=json.dumps(batch))
        try:
            answers = json.loads(checked.stdout)
        except ValueError:
            raise SystemExit("compiled checker failed:\n" + checked.stdout[-3000:])

    report = {name: {"accepted": 0, "rejected": 0, "wrong_accepted": 0}
              for name in [s.__name__ for s in searches.HONEST + searches.WRONG]}
    for (name, index, word), accepted in zip(owners, answers):
        row = report[name]
        row["accepted" if accepted else "rejected"] += 1
        if accepted and word != truth[index]:
            row["wrong_accepted"] += 1
    honest = [s.__name__ for s in searches.HONEST]
    wrong = [s.__name__ for s in searches.WRONG]
    if any(report[name]["rejected"] or report[name]["wrong_accepted"]
           for name in honest):
        raise SystemExit("an honest search was rejected: " + json.dumps(report))
    if any(report[name]["wrong_accepted"] or not report[name]["rejected"]
           for name in wrong):
        raise SystemExit("a wrong search got through: " + json.dumps(report))
    print(json.dumps({"problems": len(problems),
                      "compatible": sum(word is None for word in truth),
                      "searches": report}, indent=2))
    print("Verdict checker: verified with its existence proof, broken checkers "
          "rejected, every accepted verdict equals the enumerated answer")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
