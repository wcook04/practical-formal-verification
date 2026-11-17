# Preserve an approved finite interface

An accepted compatibility certificate establishes that the candidate admits
every finite input sequence admitted by the approved model, with exactly the
same output sequence. This includes arbitrarily long sequences through cycles;
there is no fixed trace-depth or state-count bound in the theorem. The
executable relation checker is generated from the proved Dafny source.

Use this when an application has a small, explicit state model of an interface
it already relies on. The application chooses what observations matter and
which model has been approved. A model can describe successful responses,
errors, and externally visible state changes, provided each observation is
represented by an output label.

```python
from plectis.compatibility import compare, check_certificate, check_counterexample

approved = {
    "name": "reviewed read interface",
    "initial": "idle",
    "inputs": ["read"],
    "states": {"idle": {"read": {"next": "idle", "output": "ready"}}},
}
candidate = {
    "name": "replacement",
    "initial": "waiting",
    "inputs": ["read", "inspect"],
    "states": {"waiting": {
        "read": {"next": "waiting", "output": "ready"},
        "inspect": {"next": "waiting", "output": "available"},
    }},
}
result = compare(approved, candidate)
assert result["accepted"]
assert check_certificate(approved, candidate, result["certificate"])

candidate["states"]["waiting"]["read"]["output"] = "broken"
rejected = compare(approved, candidate)
assert rejected["continuation"] == ["read"]
assert check_counterexample(approved, candidate, rejected["continuation"])
assert not check_certificate(approved, candidate, result["certificate"])
```

Run the [document-editing example](../../examples/operations/compatibility.py)
from a source checkout:

```bash
PYTHONPATH=src python3 examples/operations/compatibility.py
```

An added inspection operation passes. A candidate that acknowledges cancellation
but retains an edit fails with `begin, append, cancel, read`, exposing the
changed observation at the final read. These are supplied models; the example
does not extract or verify a real editor implementation.

## Model and result format

Each machine is a JSON object with exactly four fields:

| Field | Meaning |
|---|---|
| `name` | Nonempty identifying string; it has no approval authority. |
| `initial` | Name of a declared initial state. |
| `inputs` | List of unique, nonempty input names. An empty alphabet is allowed. |
| `states` | Nonempty object from state names to input/transition objects. |

Each transition has exactly `next` (a declared state name) and `output` (a string
observation label, including an empty string if desired). A missing transition
means an inadmissible input. An output literally named `error` or `unknown` is
an ordinary required observation. Refusing all useful inputs therefore cannot
pass a contract that admits them. State names and input names are nonempty
strings. State names may differ between models.

Both calls accept dictionaries or JSON object text. JSON text rejects duplicate
keys and non-finite numbers. Unknown fields and implicit Python conversions,
such as a tuple in place of a list, are rejected. `compare` raises
`InvalidMachine` for a malformed model.

`compare(approved, candidate)` returns a JSON-safe dictionary:

- `accepted: true` and a `certificate` containing schema version 1, SHA-256
  digests of both canonical parsed models, and unique `[old_state, new_state]`
  relation pairs. The returned relation has passed the generated checker.
- `accepted: false`, a shortest distinguishing `continuation`, a `reason`
  (`missing_input` or `output_mismatch`), and `approved_outputs` and
  `candidate_outputs`. A missing candidate transition leaves its output list
  one observation shorter. Equal-length alternatives use sorted input names.
  The continuation has passed the generated verdict checker, described below.

`check_certificate(approved, candidate, certificate)` returns a Boolean. It
rejects malformed, stale, incomplete, or behaviourally false certificates.
Model hashes identify canonical parsed objects, rather than raw JSON text or
deployed program bytes; changing a name also changes the binding. Merely
rehashing an incompatible model does not make its relation pass. Checker
execution failure raises `RuntimeError`; no alternative checker accepts it.

`check_counterexample(approved, candidate, word)` returns whether the proposed
input word exposes a missing candidate transition or a differing observation
on an approved-admissible prefix. It rechecks against these current models;
changing either model can make a retained word useless. Malformed models or
words return `False`; a checker execution failure raises `RuntimeError`.
`check_counterexample` accepts any word with a differing prefix, including a
long one. `compare` applies a stronger test to its own result: the generated
verdict checker must accept the continuation as the first shortest one.

## Exact proof boundary

[The Dafny proof](../../formal/compatibility/Compatibility.dfy) checks an initial
related pair and, at every related pair, every enabled approved transition.
The candidate must enable the same input, return the same output, and reach a
related successor. Induction on an arbitrary finite word proves the stated
trace result. Candidate-only inputs are allowed; the old contract supplies no
guarantee after a caller takes such an input. Even an empty approved input
domain is handled explicitly, rather than silently inferred from the candidate.

The search visits every reachable pair of states without a depth cutoff and
is not proved. It hands its result to a generated checker together with
evidence, and `compare` returns the result only if the checker accepts it.
For a compatible result the evidence is the relation, as before. For a
continuation the evidence is one integer for every pair of states: a number
of inputs that no difference from that pair can be shorter than, or -1 for a
pair from which no difference is reachable.
[`Verdict.dfy`](../../formal/compatibility/Verdict.dfy) proves that an
accepted continuation is a real difference, that no difference is shorter,
and that no difference of the same length comes earlier in sorted input
order. It also proves that two accepted results for the same pair of models
are equal, so the search can be replaced by any other without changing what
`compare` returns. [The verdict note](../../formal/compatibility/VERDICT.md)
gives the statements and an experiment with six searches. If the checker
refuses what the search proposed, `compare` raises `RuntimeError`.

For `n` old states, `m` candidate states and `k` input labels, exploration
visits at most `n*m` pairs. Both generated checkers examine every pair, with
`O(n*m)` storage and `O(n*m*k)` work, in addition to parsing, sorting and
hashing. Before this checker a continuation cost only a replay of its own
inputs, so a short continuation between two large models now takes longer.

Dafny, Boogie, Z3, the Python compiler/runtime, JSON parsing and label encoding
remain trusted. "Sorted input order" in the proof means integer positions; the
adapter assigns them by sorting input names, and tests cover that step. There is no proved bridge from arbitrary Python, SQLite or
another concrete implementation to these tables. Tests of such a bridge are
finite observations. The model treats each transition as a completed
synchronous step; it proves no concrete termination, scheduling, fairness,
atomicity, infinite-trace property or arbitrary external effect. Choosing an
inadequate approved model preserves that inadequate model.

## Reproduce the evidence

Normal use needs only Python; the generated checker and its runtime are shipped
with the package. From this repository:

```bash
PYTHONPATH=src python3 -m pytest tests/test_compatibility.py tests/test_compatibility_verdict.py
python3 scripts/check/check_compatibility_kernel.py
python3 scripts/check/check_compatibility_kernel.py --dafny /path/to/dafny
```

The second command checks exact source/generated hashes only. The last command
requires the pinned official Dafny 4.11.0 build, verifies all 41 proof tasks,
regenerates the deployed Python byte-for-byte, and rejects the three variants
that remove output equality, admit a stale input or miss an output difference.
The independent small
oracle checks all 625 ordered pairs of two-state, one-input models; 247 pass.
Its four-step oracle bound is complete for that small experiment only.

[Formal metadata and provenance](../../formal/compatibility/README.md) retain
the source identities and the research-return basis. The model-level theorem
uses standard forward simulation; no general novelty claim is made.
