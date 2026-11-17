"""Unproved adapter and counterexample search for the finite Mealy checker.

Adapted from supplied research return p12's artifacts/refinement/refine.py and
check_certificate.py (23 October 2026); p15's artifact/review_transfer.py and
SPECIFICATION.md informed strict input and non-vacuity checks. Round-two p14's
Replay.dfy and preflight.py inform independent negative-witness checking.
Certificate acceptance, counterexample confirmation and the admission of a
first shortest difference use generated Dafny checkers; the Python search,
encoding and explanation remain unproved.
"""

from collections import deque
import hashlib
import json
from pathlib import Path
import subprocess
import sys


class InvalidMachine(ValueError):
    """The supplied value is outside the explicit finite-machine format."""


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key: " + key)
        result[key] = value
    return result


def _bad_constant(value):
    raise ValueError("non-finite JSON number: " + value)


def _canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=True,
                      allow_nan=False, separators=(",", ":"))


def _object(value):
    if type(value) is str:
        value = json.loads(value, object_pairs_hook=_unique_object,
                           parse_constant=_bad_constant)
    if type(value) is not dict:
        raise ValueError("expected a JSON object or object text")
    if any(type(key) is not str for key in value):
        raise ValueError("JSON object keys must be strings")
    return value


def _label(value, field):
    if type(value) is not str or not value:
        raise ValueError(field + " must be a nonempty string")


def _machine(value):
    """Validate without Python's bool/int or implicit JSON coercions."""
    try:
        value = _object(value)
        if set(value) != {"name", "initial", "inputs", "states"}:
            raise ValueError("machine fields must be name, initial, inputs, states")
        _label(value["name"], "name")
        _label(value["initial"], "initial")
        inputs, states = value["inputs"], value["states"]
        if type(inputs) is not list:
            raise ValueError("inputs must be a list")
        for action in inputs:
            _label(action, "input")
        if len(set(inputs)) != len(inputs):
            raise ValueError("inputs must be unique")
        if type(states) is not dict or not states:
            raise ValueError("states must be a nonempty object")
        for state in states:
            _label(state, "state")
        if value["initial"] not in states:
            raise ValueError("initial state is absent")
        for transitions in states.values():
            if type(transitions) is not dict:
                raise ValueError("state transitions must be objects")
            for action, transition in transitions.items():
                if type(action) is not str or action not in inputs:
                    raise ValueError("transition uses an undeclared input")
                if (type(transition) is not dict
                        or set(transition) != {"next", "output"}):
                    raise ValueError("transition fields must be next and output")
                if (type(transition["next"]) is not str
                        or transition["next"] not in states):
                    raise ValueError("transition target is absent")
                if type(transition["output"]) is not str:
                    raise ValueError("output must be a string observation label")
        # The snapshot detaches all mutable caller aliases after validation.
        return json.loads(_canonical(value))
    except (ValueError, TypeError, KeyError, OverflowError) as error:
        raise InvalidMachine(str(error)) from error


def _digest(machine):
    return hashlib.sha256(_canonical(machine).encode("ascii")).hexdigest()


def _certificate(approved, candidate, pairs):
    return {"schema_version": 1,
            "approved_sha256": _digest(approved),
            "candidate_sha256": _digest(candidate),
            "relation": [list(pair) for pair in sorted(pairs)]}


def _encode(approved, candidate, pairs):
    actions = sorted(set(approved["inputs"]) | set(candidate["inputs"]))
    labels = sorted({edge["output"] for machine in (approved, candidate)
                     for transitions in machine["states"].values()
                     for edge in transitions.values()})
    output_ids = {label: index for index, label in enumerate(labels)}

    def table(machine):
        names = sorted(machine["states"])
        ids = {name: index for index, name in enumerate(names)}
        next_rows, output_rows = [], []
        for state in names:
            transitions = machine["states"][state]
            next_rows.append([ids[transitions[a]["next"]] if a in transitions else -1
                              for a in actions])
            output_rows.append([output_ids[transitions[a]["output"]]
                                if a in transitions else -1 for a in actions])
        return names, next_rows, output_rows, ids[machine["initial"]]

    old_names, old_next, old_output, old_initial = table(approved)
    new_names, new_next, new_output, new_initial = table(candidate)
    relation = [[(s, t) in pairs for t in new_names] for s in old_names]
    return {"old_next": old_next, "old_output": old_output,
            "old_initial": old_initial, "new_next": new_next,
            "new_output": new_output, "new_initial": new_initial,
            "inputs": len(actions), "relation": relation}


def _generated_check(request, *, result_field="accepted"):
    worker = Path(__file__).with_name("_worker.py")
    try:
        result = subprocess.run([sys.executable, "-I", "-B", str(worker)],
                                input=_canonical(request), text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                check=False, timeout=30)
        response = _object(result.stdout)
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        raise RuntimeError("generated compatibility checker failed") from error
    if (result.returncode or set(response) != {result_field}
            or type(response[result_field]) is not bool):
        raise RuntimeError("generated compatibility checker returned invalid output")
    return response[result_field]


def check_certificate(approved, candidate, certificate):
    """Check a hash-bound relation with the generated proved checker.

    Malformed or stale certificates return False. Checker/tooling failure raises
    RuntimeError; it never becomes an accepted certificate or a Python fallback.
    Models and certificates may be objects or strict JSON object text.
    """
    try:
        approved, candidate = _machine(approved), _machine(candidate)
        certificate = _object(certificate)
        if (set(certificate) != {"schema_version", "approved_sha256",
                                 "candidate_sha256", "relation"}
                or type(certificate["schema_version"]) is not int
                or certificate["schema_version"] != 1
                or type(certificate["approved_sha256"]) is not str
                or type(certificate["candidate_sha256"]) is not str
                or certificate["approved_sha256"] != _digest(approved)
                or certificate["candidate_sha256"] != _digest(candidate)):
            return False
        relation = certificate["relation"]
        if type(relation) is not list:
            return False
        pairs = set()
        for pair in relation:
            if (type(pair) is not list or len(pair) != 2
                    or type(pair[0]) is not str or type(pair[1]) is not str
                    or pair[0] not in approved["states"]
                    or pair[1] not in candidate["states"]):
                return False
            pairs.add(tuple(pair))
        if len(pairs) != len(relation):
            return False
    except (ValueError, TypeError, KeyError, OverflowError):
        return False
    return _generated_check(_encode(approved, candidate, pairs))


def check_counterexample(approved, candidate, word):
    """Confirm a proposed discrepancy against both current finite models.

    True means an approved-admissible prefix of the supplied input word has
    a missing candidate transition or a different observation. Empty, stale,
    disabled or unknown inputs are not evidence unless an earlier prefix
    already differed. False does not establish compatibility.

    Malformed models or words return False. Words must be lists of nonempty
    string input labels. Models may also be strict JSON object text. Tooling
    failure raises RuntimeError; it never becomes a counterexample verdict.
    """
    try:
        approved, candidate = _machine(approved), _machine(candidate)
        if (type(word) is not list
                or any(type(action) is not str or not action for action in word)):
            return False
        # Detach the caller's list before encoding. Unknown labels remain stale
        # inputs in the executable checker, including after a valid bad prefix.
        word = list(word)
        request = _encode(approved, candidate, set())
        request.pop("relation")
        alphabet = sorted(set(approved["inputs"]) | set(candidate["inputs"]))
        indices = {action: index for index, action in enumerate(alphabet)}
        request["word"] = [indices.get(action, -1) for action in word]
    except (ValueError, TypeError, KeyError, OverflowError):
        return False
    return _generated_check(request, result_field="mismatch")


def _search(approved, candidate):
    """Propose a verdict with the evidence its checker needs. Unproved.

    Returns ``(None, pairs)`` when no difference is reachable, where ``pairs``
    is the relation offered to ``check_certificate``. Otherwise returns
    ``(word, labels)``: ``labels`` maps a pair of states to -1 when no input
    sequence from the pair reaches a difference, or to a number of inputs
    that no difference from the pair can be shorter than. Any search may
    replace this one. ``compare`` returns nothing this function proposes
    until a generated checker has accepted it.
    """
    start = (approved["initial"], candidate["initial"])
    before, distance, order = {start: []}, {}, [start]
    for pair in order:
        old, new = approved["states"][pair[0]], candidate["states"][pair[1]]
        for action in old:
            if action not in new or old[action]["output"] != new[action]["output"]:
                distance[pair] = 1
                continue
            following = (old[action]["next"], new[action]["next"])
            if following not in before:
                before[following] = []
                order.append(following)
            before[following].append(pair)
    queue = deque(distance)
    while queue:
        pair = queue.popleft()
        for earlier in before[pair]:
            if earlier not in distance:
                distance[earlier] = distance[pair] + 1
                queue.append(earlier)
    if start not in distance:
        return None, set(before)
    pair, word = start, []
    while True:
        old, new = approved["states"][pair[0]], candidate["states"][pair[1]]
        remaining = distance[pair] - 1
        for action in sorted(old):
            differs = (action not in new
                       or old[action]["output"] != new[action]["output"])
            if remaining == 0 and differs:
                return word + [action], {p: distance.get(p, -1) for p in before}
            following = None if differs else (old[action]["next"], new[action]["next"])
            if remaining and following and distance.get(following) == remaining:
                word.append(action)
                pair = following
                break


def _admits(approved, candidate, word, labels):
    """Ask the generated verdict checker about a proposed difference.

    True means ``word`` is the first shortest difference for these models.
    A malformed proposal returns False. Tooling failure raises RuntimeError.
    """
    try:
        if (type(word) is not list or type(labels) is not dict
                or any(type(action) is not str for action in word)
                or any(type(pair) is not tuple or len(pair) != 2
                       or pair[0] not in approved["states"]
                       or pair[1] not in candidate["states"]
                       or type(bound) is not int
                       for pair, bound in labels.items())):
            return False
        request = _encode(approved, candidate, set())
        request.pop("relation")
        alphabet = sorted(set(approved["inputs"]) | set(candidate["inputs"]))
        indices = {action: index for index, action in enumerate(alphabet)}
        request["word"] = [indices.get(action, -1) for action in word]
        # A pair the search did not label gets 0, which claims nothing.
        request["labels"] = [[labels.get((s, t), 0) for t in sorted(candidate["states"])]
                             for s in sorted(approved["states"])]
    except (ValueError, TypeError, KeyError, OverflowError):
        return False
    return _generated_check(request)


def _observations(machine, word):
    state, outputs = machine["initial"], []
    for action in word:
        edge = machine["states"][state].get(action)
        if edge is None:
            break
        outputs.append(edge["output"])
        state = edge["next"]
    return outputs


def compare(approved, candidate):
    """Return an accepted relation or the first shortest differing continuation.

    Every approved-enabled transition is an obligation, including transitions
    labelled error or unknown. Candidate additions are allowed. The search
    covers the finite reachable product, with no user-supplied depth cutoff.

    The search is not proved, and nothing it proposes is returned unchecked.
    A compatible result is returned only with a relation the generated
    relation checker accepts. A continuation is returned only when the
    generated verdict checker accepts it, which is proved to mean that it is
    a real difference, that no difference is shorter, and that no difference
    of the same length comes earlier when inputs are compared by sorted
    position. For a given pair of models at most one result can pass these
    checks. If the search proposes anything else, RuntimeError is raised.

    Model parsing, the sorting of input names into positions, ``reason`` and
    the two observation lists are tested, not formally proved.
    """
    approved, candidate = _machine(approved), _machine(candidate)
    # The search works on its own copies. Changing them cannot change the
    # machines that the checkers are given below.
    word, evidence = _search(_machine(approved), _machine(candidate))
    if word is None:
        certificate = _certificate(approved, candidate, evidence)
        if not check_certificate(approved, candidate, certificate):
            raise RuntimeError("generated checker rejected the searched relation")
        return {"accepted": True, "certificate": certificate}
    if not _admits(approved, candidate, word, evidence):
        raise RuntimeError("generated checker rejected the searched counterexample")
    word = list(word)
    reached = _observations(candidate, word)
    return {"accepted": False, "continuation": word,
            "reason": "missing_input" if len(reached) < len(word) else "output_mismatch",
            "approved_outputs": _observations(approved, word),
            "candidate_outputs": reached}
