"""compare() returns only what a generated checker accepts, whatever searched."""
import copy
import json
from pathlib import Path
import random
import runpy
import subprocess
import sys

import pytest

from plectis.compatibility import compare
from plectis.compatibility import _api


ROOT = Path(__file__).resolve().parents[1]
SEARCHES = runpy.run_path(str(ROOT / "examples/operations/verdict_searches.py"))


def later_difference():
    """The candidate answers input a differently, but only in state later."""
    old = {"name": "old", "initial": "s", "inputs": ["z", "a", "next"],
           "states": {"s": {"next": {"next": "later", "output": "ok"},
                            "a": {"next": "s", "output": "ok"},
                            "z": {"next": "s", "output": "ok"}},
                      "later": {"a": {"next": "later", "output": "good"}}}}
    new = copy.deepcopy(old)
    new["states"]["later"]["a"]["output"] = "bad"
    return old, new


def through(search):
    """Run one of the integer-table example searches in place of _search."""
    def proposal(approved, candidate):
        tables = _api._encode(approved, candidate, set())
        actions = sorted(set(approved["inputs"]) | set(candidate["inputs"]))
        word, labels = search(
            (tables["old_next"], tables["old_output"], tables["old_initial"]),
            (tables["new_next"], tables["new_output"], tables["new_initial"]),
            tables["inputs"])
        named = {(s, t): labels[i][j]
                 for i, s in enumerate(sorted(approved["states"]))
                 for j, t in enumerate(sorted(candidate["states"]))}
        if word is None:
            return None, {pair for pair, bound in named.items() if bound == -1}
        return [actions[a] for a in word], named
    return proposal


def random_machine(rng, name):
    states = ["p", "q", "r"][:rng.choice((2, 3))]
    return {"name": name, "initial": rng.choice(states), "inputs": ["a", "b"],
            "states": {state: {action: {"next": rng.choice(states),
                                        "output": rng.choice(("x", "y"))}
                               for action in ("a", "b") if rng.random() < 0.8}
                       for state in states}}


def test_a_compatible_proposal_for_a_later_difference_is_refused(monkeypatch):
    old, new = later_difference()
    assert compare(old, new)["continuation"] == ["next", "a"]
    monkeypatch.setattr(_api, "_search", lambda *args: (
        None, {("s", "s"), ("later", "later")}))
    with pytest.raises(RuntimeError, match="rejected the searched relation"):
        compare(old, new)


def test_a_real_shortest_difference_that_loses_the_tie_is_refused(monkeypatch):
    old = {"name": "old", "initial": "s", "inputs": ["b", "a"],
           "states": {"s": {"a": {"next": "s", "output": "ok"},
                            "b": {"next": "s", "output": "ok"}}}}
    new = copy.deepcopy(old)
    new["states"]["s"]["a"]["output"] = new["states"]["s"]["b"]["output"] = "bad"
    assert compare(old, new)["continuation"] == ["a"]
    assert _api.check_counterexample(old, new, ["b"])
    monkeypatch.setattr(_api, "_search", lambda *args: (["b"], {("s", "s"): 1}))
    with pytest.raises(RuntimeError, match="rejected the searched counterexample"):
        compare(old, new)


@pytest.mark.parametrize("word, labels", [
    (["z", "next", "a"], {("s", "s"): 3, ("later", "later"): 1}),  # real, too long
    (["next", "a"], {}),                                       # right word, no evidence
    (["next", "a"], {("s", "s"): 2, ("later", "later"): 2}),    # right word, false bound
    (["next", "a"], {("s", "s"): True, ("later", "later"): 1}),  # malformed bound
    ("next", {("s", "s"): 2, ("later", "later"): 1}),            # malformed word
])
def test_a_refused_proposal_never_becomes_another_answer(monkeypatch, word, labels):
    old, new = later_difference()
    monkeypatch.setattr(_api, "_search", lambda *args: (word, labels))
    with pytest.raises(RuntimeError, match="rejected the searched counterexample"):
        compare(old, new)


def test_a_search_that_edits_its_machines_does_not_change_what_is_checked(monkeypatch):
    old, new = later_difference()

    def edits_then_claims_compatible(approved, candidate):
        candidate["states"]["later"]["a"]["output"] = "good"
        return None, {("s", "s"), ("later", "later")}

    monkeypatch.setattr(_api, "_search", edits_then_claims_compatible)
    with pytest.raises(RuntimeError, match="rejected the searched relation"):
        compare(old, new)


def test_different_evidence_for_the_same_word_is_accepted(monkeypatch):
    old, new = later_difference()
    expected = compare(old, new)
    # The default search leaves the two unreachable pairs at 0. Both differ
    # on their first input, so 1 is also a true bound for them.
    monkeypatch.setattr(_api, "_search", lambda *args: (
        ["next", "a"], {("s", "s"): 2, ("later", "later"): 1, ("later", "s"): 1,
                        ("s", "later"): 1}))
    assert compare(old, new) == expected


def test_six_replacement_searches_through_compare(monkeypatch):
    """Honest searches agree with the default. A wrong one agrees or is refused."""
    rng = random.Random(20261117)
    pairs = [later_difference()] + [
        (random_machine(rng, "old"), random_machine(rng, "new")) for _ in range(40)]
    default = [compare(old, new) for old, new in pairs]
    assert {result["accepted"] for result in default} == {True, False}
    refused = dict.fromkeys(SEARCHES["WRONG"], 0)
    for search in SEARCHES["HONEST"] + SEARCHES["WRONG"]:
        monkeypatch.setattr(_api, "_search", through(search))
        for (old, new), expected in zip(pairs, default):
            try:
                result = compare(old, new)
            except RuntimeError:
                assert search in refused
                refused[search] += 1
                continue
            # Certificates may differ between searches; the verdict may not.
            assert result["accepted"] is expected["accepted"]
            assert result.get("continuation") == expected.get("continuation")
    assert all(refused.values())


def test_declaration_order_does_not_change_the_verdict():
    rng = random.Random(7)
    for _ in range(12):
        old, new = random_machine(rng, "old"), random_machine(rng, "new")
        expected = compare(old, new)

        def reordered(machine):
            states = list(machine["states"].items())
            rng.shuffle(states)
            return json.dumps({"states": {state: dict(reversed(list(edges.items())))
                                          for state, edges in states},
                               "inputs": list(reversed(machine["inputs"])),
                               "initial": machine["initial"], "name": machine["name"]})

        result = compare(reordered(old), reordered(new))
        assert result["accepted"] is expected["accepted"]
        assert result.get("continuation") == expected.get("continuation")


def test_candidate_additions_stay_compatible_and_removals_differ():
    old, _ = later_difference()
    new = copy.deepcopy(old)
    new["inputs"].append("extra")
    new["states"]["later"]["extra"] = {"next": "s", "output": "anything"}
    assert compare(old, new)["accepted"]
    del new["states"]["later"]["a"]
    assert compare(old, new) == {
        "accepted": False, "continuation": ["next", "a"], "reason": "missing_input",
        "approved_outputs": ["ok", "good"], "candidate_outputs": ["ok"]}


def test_a_difference_three_thousand_inputs_away_is_admitted():
    """The compiled word check loops; Python's recursion limit is not raised."""
    length = 3000
    old = {"name": "chain", "initial": "0", "inputs": ["advance"],
           "states": {str(i): {"advance": {"next": str(min(i + 1, length)),
                                           "output": "last" if i == length else "ok"}}
                      for i in range(length + 1)}}
    new = {"name": "loop", "initial": "x", "inputs": ["advance"],
           "states": {"x": {"advance": {"next": "x", "output": "ok"}}}}
    result = compare(old, new)
    assert result["continuation"] == ["advance"] * (length + 1)
    assert result["reason"] == "output_mismatch"


def test_worker_rejects_malformed_labels():
    old, new = later_difference()
    request = _api._encode(old, new, set())
    request.pop("relation")
    request["word"] = [1, 0]
    worker = ROOT / "src/plectis/compatibility/_worker.py"

    def run(labels):
        result = subprocess.run([sys.executable, "-I", "-B", str(worker)],
                                input=json.dumps(dict(request, labels=labels)),
                                text=True, stdout=subprocess.PIPE, check=False)
        return result.returncode, json.loads(result.stdout)

    assert run([[1, 0], [0, 2]]) == (0, {"accepted": True})
    assert run([[1, 0], [0, 1]]) == (0, {"accepted": False})
    assert run([[1, 0]]) == (0, {"accepted": False})
    for labels in ([[True, 0], [0, 2]], [[1.0, 0], [0, 2]], "labels", [1, 0]):
        code, response = run(labels)
        assert code == 2 and "error" in response
