# Verdict checker: the search is replaceable

Status: experiment. `plectis.compatibility.compare` does not call this checker
yet, so the guarantees below do not apply to `compare` today.

## What is compared

Two finite state machines, an approved model and a candidate. Each takes one
input at a time and returns one output. A *difference* is a sequence of inputs
on which the candidate returns a different output from the approved model, or
has no transition for an input the approved model allows. `Replay.dfy` already
defines this as `Mismatch` and proves that definition exact.

`compare` reports one of two results: the models are compatible, or here is a
sequence of inputs on which they differ. Its documentation promises the
shortest such sequence, with ties going to the input that comes first in sorted
order. Until now a breadth-first search in Python produced that sequence, and
only tests covered "shortest" and "first in sorted order".

## What the search must now hand over

Any search, written any way, returns two things:

- a verdict: `Compatible`, or `Differs(word)` with the sequence of inputs;
- one integer for every pair of states (one state from each model). `-1` claims
  that no sequence of inputs starting from that pair reaches a difference. A
  number `n` claims that no sequence shorter than `n` does.

`Check` in `Verdict.dfy` takes the two models, the verdict and the integers and
returns true or false. It trusts none of the integers. For every pair of states
and every allowed input it tests that the integer for the pair is consistent
with the integer for the pair the input leads to. For a `Differs` verdict it
then follows the word one input at a time. At each step it tests that every
smaller allowed input leads to a pair whose integer is at least the number of
inputs still to come, so no smaller input can reach a difference in time.

## What is proved

Dafny 4.11.0 verifies these statements for all valid models of any size.

| Lemma | Statement |
|---|---|
| `CompatibleMeansNoDifference` | If `Check` accepts `Compatible`, no sequence of inputs is a difference. |
| `DiffersMeansFirstShortest` | If `Check` accepts `Differs(word)`, then `word` is a difference, no difference is shorter, and no difference of the same length comes earlier in input order. |
| `AcceptedVerdictIsUnique` | If `Check` accepts two verdicts for the same pair of models, with any two sets of integers, the verdicts are equal. |
| `EveryPairHasAVerdict` (`VerdictExists.dfy`) | For every valid pair of models there is a verdict and a set of integers that `Check` accepts. |

The last two together say that the accepted verdict is a function of the two
models. Two different searches cannot both be accepted with different answers,
and a correct search is never left without an answer that `Check` accepts. The
integers themselves are not unique: the three searches below hand over
different integers for the same models and are all accepted.

Dafny reports 23 verified obligations for `Verdict.dfy`, 22 for
`VerdictExists.dfy` and 86 when the two are verified together with the files
they include. `dafny audit` reports no assumptions.

## Two checkers that are wrong on purpose

Each file in `negative/` changes one condition in `Check`. Dafny must reject both.

| File | Change | Result |
|---|---|---|
| `VerdictMissedLaterDifferenceMutant.dfy` | A pair marked `-1` no longer has to lead to pairs marked `-1`. | 22 verified, 1 error: `CompatibleMeansNoDifference` fails. |
| `VerdictAnyShortestWordMutant.dfy` | The smaller inputs at each step are no longer tested. | 22 verified, 2 errors: "first in input order" fails. |

## Six searches run against the compiled checker

`examples/operations/verdict_searches.py` contains six searches. None is proved.

- `backward` measures the distance from every pair of states to a difference,
  then walks from the start towards the nearest one.
- `forward` searches breadth-first from the start, then computes the integers
  by repeated relaxation.
- `deepening` searches depth-first with a growing length limit and hands over
  only the lower bounds it established on the way.
- `largest_input_first` returns a shortest sequence but breaks ties the wrong way.
- `initial_state_only` looks for a difference in the initial states and
  otherwise reports `Compatible`. The broken replay checker in
  `ReplayMissedDifferenceMutant.dfy` makes the same mistake.
- `first_found` reports the first difference a depth-first walk meets.

`scripts/check/check_verdict_experiment.py` verifies the Dafny files, compiles
`Check` to Python with Dafny, and passes every search's output to the compiled
`Check`. It compares each accepted verdict with the answer found by listing
every sequence of inputs in order of length. The 4,001 problems are every pair
of two-state, one-input machines (2,500), 1,500 random pairs with two or three
states and two or three inputs, and one pair whose only difference is 19 inputs
from the start.

| Search | Accepted | Rejected | Accepted with a wrong verdict |
|---|---|---|---|
| `backward` | 4,001 | 0 | 0 |
| `forward` | 4,001 | 0 | 0 |
| `deepening` | 4,001 | 0 | 0 |
| `largest_input_first` | 3,298 | 703 | 0 |
| `initial_state_only` | 3,180 | 821 | 0 |
| `first_found` | 3,706 | 295 | 0 |

The three wrong searches are accepted on the problems where their answer
happens to be right and rejected on every problem where it is wrong.

```bash
python3 scripts/check/check_verdict_experiment.py --dafny /path/to/dafny
```

There is no handwritten Python copy of `Check`. Without the pinned Dafny build
the script stops.

## What is not proved

- `compare` still runs its own breadth-first search and does not call `Check`.
  Wiring it in needs the compiled checker added to the hash-bound generated
  files and the isolated worker, as for the existing checkers.
- The searches, the encoding of named states and inputs as integers, and the
  explanation text that `compare` returns stay outside the proof.
- "First in input order" refers to integer input indices. The Python adapter
  assigns those indices by sorting the input names, and that step is tested,
  not proved.
- Dafny, Boogie, Z3, the Dafny compiler and its Python runtime are trusted, as
  for the other formal cores in this repository.
- Whether a model describes a real program correctly is outside every proof here.

## Prior work

The proof technique is established. A program returns its answer together with
evidence, and a small verified checker tests the evidence; see Alkassar, Böhme,
Mehlhorn and Rizkallah, *A Framework for the Verification of Certifying
Computations*, which includes shortest-path lower bounds tested edge by edge.
The integers here are those lower bounds on the graph of state pairs. This file
makes no claim of a new method.
