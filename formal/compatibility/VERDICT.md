# The compatibility result is proved and the search is replaceable

`plectis.compatibility.compare` takes two finite state machines, an approved
model and a candidate, and returns one of two results. Either the candidate
gives every output the approved model gives, or `compare` returns the shortest
sequence of inputs on which it does not, and among sequences of that length
the one that comes first when inputs are compared in sorted order.

The search that finds this result is ordinary Python and is not proved. It
passes its result, with some evidence, to a small checker written in Dafny,
and `compare` returns the result only if the checker accepts it. Dafny proves
what acceptance means:

1. An accepted "compatible" result means no sequence of inputs is a difference.
2. An accepted sequence is a real difference, no difference is shorter, and no
   difference of the same length comes earlier in input order.
3. Two accepted results for the same pair of models are equal.
4. Every valid pair of models has a result the checker accepts.

By 3 and 4 the accepted result depends only on the two models. Any search can
take the place of the built-in one, and if its result is accepted it is the
same result.

The technique is that of certifying algorithms and is not new. The proofs
are about the two models as supplied. They say nothing about whether a model
describes a real program.

## The gap this closes

The earlier contract for this comparison had gaps of the usual kind. The
first proof in `Replay.dfy` said that any difference the checker reported was
real. A deliberately broken checker, which looked for a difference only while
the candidate was in its initial state, still satisfied that proof. Adding the
converse, that the checker reports a difference whenever one exists, made
Dafny reject the broken version (`negative/ReplayMissedDifferenceMutant.dfy`).

That left the promise in `compare`'s own documentation. The replay checker
decides whether a given sequence is a difference. It does not say that the
sequence is the shortest one, or the first of the shortest ones, and until
17 November 2026 only tests covered those two words. The files described here
prove them.

## The comparison, with an example

Each model takes one input at a time and returns one output. A *difference*
is a sequence of inputs on which the candidate returns a different output
from the approved model, or has no transition for an input the approved model
allows. `Replay.dfy` defines this as `Mismatch`.

The comparison has a direction. An input that only the candidate allows is
never a difference. An input that the approved model allows and the candidate
lacks is one.

Here are two models with two states and two inputs. The candidate is the same
as the approved model except for one output, shown in bold.

| State | Input | Next state | Approved output | Candidate output |
|---|---|---|---|---|
| 0 | 0 | 0 | 5 | 5 |
| 0 | 1 | 1 | 5 | 5 |
| 1 | 0 | 1 | 6 | **9** |
| 1 | 1 | 1 | 5 | 5 |

Both models start in state 0. No single input shows the change, because both
return 5 for either input in state 0. The sequence 1, 0 does: after input 1
both models are in state 1, and input 0 then returns 6 from the approved
model and 9 from the candidate. Neither model changes state on input 0 in
state 0, so no sequence of two inputs that starts with input 0 is a
difference. The result is the sequence 1, 0.

## What a search has to hand over

A search returns a verdict and one integer for every pair of states, one state
from each model.

- The verdict is `Compatible`, or `Differs(word)` where `word` is the sequence
  of inputs.
- The integer for a pair is a claim by the search. `-1` claims that no
  sequence of inputs starting from that pair reaches a difference. A number
  `n` claims that no sequence shorter than `n` does. `0` therefore claims
  nothing.

For the example a search can hand over `Differs([1, 0])` and these integers:

| | Candidate in state 0 | Candidate in state 1 |
|---|---|---|
| **Approved in state 0** | 2 | 0 |
| **Approved in state 1** | 0 | 1 |

`Check` in `Verdict.dfy` takes the two models, the verdict and the integers
and returns true or false. It assumes none of the integers is right. It does
two things.

First, for every pair of states and every input the approved model allows
there, it compares the integer for the pair with the integer for the pair
that the input leads to. A pair where the two models differ on that input
must claim 0 or 1. A pair marked `-1` must lead to a pair marked `-1`. Any
other pair may claim at most one more than the pair it leads to, unless that
pair is marked `-1`. In the example the pair (0, 0) claims 2, and input 1
leads to the pair (1, 1), which claims 1.

Second, for a `Differs` verdict, it follows the word one input at a time. The
integer for the starting pair must equal the length of the word. At each step
every smaller input that the approved model allows must lead to a pair whose
integer is at least the number of inputs still to come, or is `-1`. In the
example the word starts with input 1 and has two inputs to come. The smaller
input 0 leads back to the pair (0, 0), which claims 2, so no sequence starting
with input 0 can be a difference of length two.

Dafny proves that `Check` returns true for exactly this example in the lemma
`BothVerdictsOccur`.

## What is proved

Dafny 4.11.0 verifies each statement for all valid models of any size. The
first three and the last two are in `Verdict.dfy`. The fourth is in
`VerdictExists.dfy`.

| Lemma | Statement |
|---|---|
| `CompatibleMeansNoDifference` | If `Check` accepts `Compatible`, no sequence of inputs is a difference. |
| `DiffersMeansFirstShortest` | If `Check` accepts `Differs(word)`, `word` is the first shortest difference. |
| `AcceptedVerdictIsUnique` | Two verdicts that `Check` accepts for the same models are equal. |
| `EveryPairHasAVerdict` | For every valid pair of models, `Check` accepts some verdict with some integers. |
| `AcceptedRelationIsCompatible` | A relation that `Compatibility.Check` accepts gives an accepted `Compatible` verdict. |
| `CompatibleGivesAcceptedRelation` | The pairs marked `-1` in an accepted `Compatible` verdict form such a relation. |

"First shortest" has the three parts listed at the top of this note: `word`
is a difference, no difference is shorter, and no difference of the same
length comes earlier in input order.

Uniqueness holds whatever integers came with each verdict. The integers
themselves are not unique. Three of the searches described below hand over
different integers for the same models, and `Check` accepts all three.

Existence is a statement about the models. It does not say that a particular
search finishes, or that the checker finishes within the time `compare`
allows it.

The last two rows connect this checker to the certificate `compare` already
returned for compatible models, which is a relation between states checked by
`Compatibility.Check`. That certificate keeps its format. By
`AcceptedRelationIsCompatible`, marking the relation's pairs `-1` and every
other pair `0` gives integers that `Check` accepts with `Compatible`.

Dafny reports 28 verified obligations for `Verdict.dfy`, 22 for
`VerdictExists.dfy` and 91 when the two are verified together with the files
they include. `dafny audit` reports no assumptions.

## What `compare` does with a proposal

| The search proposes | `compare` runs | If the answer is false |
|---|---|---|
| No difference, with a relation | `Compatibility.Check` on the relation | `RuntimeError` |
| A word, with integers | `Verdict.Check` on `Differs(word)` | `RuntimeError` |

A refused proposal never becomes a different answer about the models, and
there is no second checker to fall back on.

The checker that runs is the Python that Dafny generates from `Verdict.dfy`.
`metadata.json` records the hash of each generated file, and the worker that
runs the checker refuses files whose hashes differ. The command under
"Reproduce" below reproves the sources and requires the regenerated Python to
equal the packaged files byte for byte.

`tests/test_compatibility_verdict.py` replaces the search inside `compare`
and then calls `compare`. Each of these proposals is refused:

- "Compatible", for two models that differ only in a later state.
- A real shortest difference that loses the tie on input order.
- A real difference that is longer than the shortest one.
- The right word with integers that do not hold.

## Two checkers that are wrong on purpose

Each file in `negative/` removes one condition from `Check`. Dafny must fail
to verify both.

| File | Condition removed | Result |
|---|---|---|
| `VerdictMissedLaterDifferenceMutant.dfy` | A pair marked `-1` must lead to pairs marked `-1`. | 26 verified, 2 errors |
| `VerdictAnyShortestWordMutant.dfy` | The smaller inputs at each step are ruled out. | 27 verified, 2 errors |

Without the first condition Dafny cannot prove that an accepted `Compatible`
verdict rules out every difference. Without the second it cannot prove "first
in input order".

## Six other searches

`examples/operations/verdict_searches.py` contains six searches, separate
from the one inside `compare`. None is proved. Three are written to be right
and work in different ways. Three are wrong on purpose.

| Search | How it works |
|---|---|
| `backward` | Measures the distance from every pair of states to a difference, then walks from the start. |
| `forward` | Searches breadth-first from the start, then computes the integers by repeated relaxation. |
| `deepening` | Searches depth-first with a growing length limit and hands over only the bounds it established. |
| `largest_input_first` | Wrong: returns a shortest difference but breaks ties towards the largest input. |
| `initial_state_only` | Wrong: looks for a difference in the initial states and otherwise says `Compatible`. |
| `first_found` | Wrong: returns the first difference a depth-first walk meets. |

`initial_state_only` makes the same mistake as the broken replay checker
described under "The gap this closes".

`scripts/check/check_verdict_experiment.py` compiles `Check` to Python with
Dafny and passes every search's output to it. It compares each accepted
verdict with the answer found by listing every sequence of inputs in order of
length. There are 4,001 problems: all 2,500 pairs of machines with two states
and one input, 1,500 random pairs with two or three states and two or three
inputs, and one pair whose only difference is 19 inputs from the start.

| Search | Accepted | Refused | Accepted with a wrong verdict |
|---|---|---|---|
| `backward` | 4,001 | 0 | 0 |
| `forward` | 4,001 | 0 | 0 |
| `deepening` | 4,001 | 0 | 0 |
| `largest_input_first` | 3,298 | 703 | 0 |
| `initial_state_only` | 3,180 | 821 | 0 |
| `first_found` | 3,706 | 295 | 0 |

Each wrong search is accepted on the problems where its answer happens to be
right and refused on every problem where its answer is wrong.

The same six searches are also run through `compare` itself on 41 pairs of
models in `tests/test_compatibility_verdict.py`. The first three return what
the built-in search returns. Each wrong one is refused at least once and
never returns anything else.

## Reproduce

Both commands need the official Dafny 4.11.0 build named in `metadata.json`.
There is no handwritten Python copy of `Check`, so without Dafny the second
command stops.

```bash
python3 scripts/check/check_compatibility_kernel.py --dafny /path/to/dafny
python3 scripts/check/check_verdict_experiment.py --dafny /path/to/dafny
```

The first reproves every Dafny file in this directory, compares the
regenerated Python with the packaged files and requires all five broken
checkers to fail. The second runs the six searches.

## What is not proved

- The searches. That is the design: a search only proposes.
- The translation between the named states and inputs that `compare` accepts
  and the integers the checker works on. "First in input order" in the proof
  means integer positions. The Python adapter assigns positions by sorting
  the input names, and tests cover that step.
- The `reason` field and the two lists of outputs that `compare` returns
  beside the sequence. Tests cover them.
- Running time. The checker examines every pair of states. On the laptop used
  here, a difference between two models of 1,501 states each took about 11
  seconds to check. The checker is stopped after 30 seconds, and `compare`
  then raises `RuntimeError`.
- Dafny, Boogie, Z3, the Dafny compiler and its Python runtime are trusted, as
  for the other proofs in this repository.
- Whether a model describes a real program correctly.

## Prior work

A program that returns its answer together with evidence, and a small
verified checker that tests the evidence, is a certifying algorithm. See
Alkassar, Böhme, Mehlhorn and Rizkallah, *A Framework for the Verification of
Certifying Computations*, which includes shortest-path lower bounds tested
edge by edge. The integers here are lower bounds of that kind on the graph of
state pairs. This note makes no claim of a new method.
