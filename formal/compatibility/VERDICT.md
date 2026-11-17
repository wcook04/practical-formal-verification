# What is proved about `compare`, and what is only tested

`plectis.compatibility.compare(approved, candidate)` takes two finite state
machines. Its documentation says it returns one of two answers:

- every input sequence that the approved machine can run gets the same
  outputs from the candidate, or
- the shortest input sequence for which that fails, and if several have that
  length, the first in lexicographic order of inputs.

A call can also raise `RuntimeError`, as described below.

Until 17 November 2026 a Python breadth-first search produced the answer and
only tests covered "shortest" and "first". The search is still unverified
Python. It now also produces a certificate, and a checker written in Dafny
decides whether the answer may be returned. This is a certifying algorithm
in the sense of Alkassar, Böhme, Mehlhorn and Rizkallah, *A Framework for the
Verification of Certifying Computations*, and the certificate is a table of
shortest-path lower bounds of the kind used there. The method is not new.

The four levels of support are different and are kept apart in this note.

| Statement | Support |
|---|---|
| If the Dafny function `Check` returns true, the answer is the one specified above. Exactly one answer passes. | Proved in Dafny, for machines given as integer tables. |
| The Python that runs is what Dafny 4.11.0 generates from that source. | Regenerated and compared byte for byte. The Dafny compiler is trusted. |
| `compare` converts its named machines to integer tables correctly, and builds the rest of its return value correctly. | Tests only. |
| A machine describes some real program. | Not addressed. |

## Machines and differences

A machine is a deterministic, partial Mealy machine: a finite set of states,
an initial state, a finite set of inputs, and for each state and input either
no transition or one next state and one output. In Dafny it is
`Replay.Model(next, output, initial, inputs)`, where states and inputs are
integers from 0 and `next[s][a] == -1` means state `s` has no transition on
input `a`. `ValidPair(approved, candidate)` says that both tables have the
right shape, every next state is in range, and both machines use the same
number of inputs. No theorem below assumes anything else about the machines.

A *difference from the state pair (s, t)* is an input sequence that the
approved machine can run from `s` up to some input on which the candidate,
run from `t`, either has no transition or returns a different output. This
is `Replay.MismatchFrom`:

```dafny
function MismatchFrom(approved: Model, candidate: Model, s: int, t: int,
                      word: seq<int>): bool
{
  if |word| == 0 then false
  else if word[0] < 0 || approved.inputs <= word[0] || approved.next[s][word[0]] < 0
    then false
  else if candidate.next[t][word[0]] < 0 ||
          approved.output[s][word[0]] != candidate.output[t][word[0]]
    then true
  else MismatchFrom(approved, candidate, approved.next[s][word[0]],
                     candidate.next[t][word[0]], word[1..])
}
```

A *difference* between the two machines is a difference from their two
initial states (`Replay.Mismatch`).

The definition is one-directional. An input that only the candidate has is
never a difference, so "no difference" means the candidate simulates the
approved machine. It does not mean the two machines are equivalent.

## The answer and its certificate

```dafny
datatype Verdict = Compatible | Differs(word: seq<int>)
```

The certificate is one integer for every pair of states, `labels[s][t]`, with
this intended meaning:

- `-1` (written `Never`): there is no difference from (s, t).
- `n >= 0`: every difference from (s, t) has length at least `n`.

A label of 0 is therefore always true and carries no information. Labels need
not be exact, and different searches produce different labels for the same
machines.

`Check` does not assume the labels are right. It tests them one transition at
a time (`LabelsHold`), and for a `Differs` answer it also walks the word
(`FirstWord`). Here `DiffersNow(s, t, a)` means that the candidate in state
`t` has no transition on `a`, or returns a different output from the approved
machine in state `s`. Preconditions and some parameter types are left out of
the listing below. The source has them.

```dafny
predicate LabelsHold(approved: R.Model, candidate: R.Model, labels: seq<seq<int>>)
{
  Shape(approved, candidate, labels) &&   // one label per pair, each >= -1
  forall s, t, a ::
    0 <= s < |approved.next| && 0 <= t < |candidate.next| &&
    0 <= a < approved.inputs && 0 <= approved.next[s][a] ==>
      if DiffersNow(approved, candidate, s, t, a) then
        0 <= labels[s][t] <= 1
      else if labels[s][t] == Never then
        labels[approved.next[s][a]][candidate.next[t][a]] == Never
      else
        labels[approved.next[s][a]][candidate.next[t][a]] == Never ||
        labels[s][t] <= 1 + labels[approved.next[s][a]][candidate.next[t][a]]
}

predicate FirstWord(approved, candidate, labels, s, t, word)
{
  if |word| == 0 || word[0] < 0 || approved.inputs <= word[0] ||
     approved.next[s][word[0]] < 0
    then false
  else if !SmallerInputsRuledOut(approved, candidate, labels, s, t, word[0], |word|)
    then false
  else if DiffersNow(approved, candidate, s, t, word[0])
    then |word| == 1
  else FirstWord(approved, candidate, labels, approved.next[s][word[0]],
                 candidate.next[t][word[0]], word[1..])
}

function Check(approved: R.Model, candidate: R.Model, labels: seq<seq<int>>,
               verdict: Verdict): bool {
  R.ValidPair(approved, candidate) &&
  LabelsHold(approved, candidate, labels) &&
  match verdict
  case Compatible => labels[approved.initial][candidate.initial] == Never
  case Differs(word) =>
    labels[approved.initial][candidate.initial] == |word| &&
    FirstWord(approved, candidate, labels, approved.initial, candidate.initial, word)
}
```

`SmallerInputsRuledOut(s, t, first, remaining)` holds when every input
`a < first` that the approved machine has in state `s` satisfies two
conditions: `DiffersNow(s, t, a)` is false, and the pair that `a` leads to
has label `Never` or a label of at least `remaining`.

Why these local tests are enough:

- **`Never` is sound.** By `LabelsHold`, a pair labelled `Never` has no
  immediate difference and every transition from it leads to a pair labelled
  `Never`. By induction on the length of the word, no word from such a pair
  is a difference. `Compatible` requires the initial pair to be labelled
  `Never`.
- **Labels are lower bounds.** A pair with an immediate difference has label
  at most 1, and otherwise a label is at most one more than the label of each
  pair it leads to. By induction on the length of the word, a difference from
  (s, t) has length at least `labels[s][t]`.
- **The word is a shortest difference.** `FirstWord` follows the word and
  requires its last input, and no earlier one, to be an immediate difference.
  `Check` requires the initial label to equal the length of the word, so no
  difference is shorter.
- **The word is the first of the shortest.** Suppose the rest of the word has
  `r` inputs when it reaches (s, t). A smaller input `a` leads to a pair whose
  label is at least `r`, so a difference that continues with `a` has at least
  `r + 1` inputs from here. Its total length is then greater than the length
  of the word.

## What is proved

These are the statements in `Verdict.dfy` and `VerdictExists.dfy`, with
parameter types and proofs left out. `Before(x, y)` is strict lexicographic
order on sequences of equal length.

```dafny
lemma CompatibleMeansNoDifference(approved, candidate, labels, word: seq<int>)
  requires Check(approved, candidate, labels, Compatible)
  ensures !R.Mismatch(approved, candidate, word)

lemma DiffersMeansFirstShortest(approved, candidate, labels,
                                word: seq<int>, other: seq<int>)
  requires Check(approved, candidate, labels, Differs(word))
  ensures R.Mismatch(approved, candidate, word)
  ensures R.Mismatch(approved, candidate, other) ==>
            |word| <= |other| && !Before(other, word)

lemma AcceptedVerdictIsUnique(approved, candidate,
                              labels1, verdict1, labels2, verdict2)
  requires Check(approved, candidate, labels1, verdict1)
  requires Check(approved, candidate, labels2, verdict2)
  ensures verdict1 == verdict2

lemma EveryPairHasAVerdict(approved, candidate)
  returns (labels: seq<seq<int>>, verdict: Verdict)
  requires R.ValidPair(approved, candidate)
  ensures Check(approved, candidate, labels, verdict)
```

The first two are soundness. The third says the verdict that passes does not
depend on which labels came with it. The fourth says `Check` cannot be sound
by returning false for everything. Its proof labels each pair with its exact
distance to a difference, or `Never` if there is none, and builds the word by
taking at each step the smallest input that is an immediate difference or
leads one step closer.

Together the third and fourth say that for each valid pair of machines
exactly one `Verdict` passes `Check`. That is a statement about `Check`. It
does not say that a particular search finishes or that its labels pass.

The lemma `BothVerdictsOccur` proves the value of `Check` on the concrete
cases in the next section.

`dafny audit` reports no `assume` statements or unproved lemmas in these two
files. Dafny, Boogie and Z3 are still trusted.

## Three examples that Dafny evaluates

**A difference at the second input.** Two states, two inputs. The candidate
differs from the approved machine in one output.

| State | Input | Next state | Approved output | Candidate output |
|---|---|---|---|---|
| 0 | 0 | 0 | 5 | 5 |
| 0 | 1 | 1 | 5 | 5 |
| 1 | 0 | 1 | 6 | 9 |
| 1 | 1 | 1 | 5 | 5 |

Both start in state 0. The only difference of length two is 1, 0. `Check`
returns true for `Differs([1, 0])` with these labels:

| | Candidate state 0 | Candidate state 1 |
|---|---|---|
| **Approved state 0** | 2 | 0 |
| **Approved state 1** | 0 | 1 |

The pairs (0, 1) and (1, 0) cannot be reached from the initial pair, and
their labels are left at 0. For the same machines `Check` returns false for
`Compatible` with every label `Never`, and false for `Compatible` with every
label 0.

**A tie.** One state, two inputs, both transitions return to that state. The
approved outputs are 7 and 7 and the candidate outputs are 8 and 8, so each
single input is a difference. With the label 1, `Check` returns true for
`Differs([0])` and false for `Differs([1])`.

**No difference, with a cycle.** One state, one input, the transition returns
to that state, and both machines output 7. There are infinitely many input
sequences and none is a difference. `Check` returns true for `Compatible`
with the label `Never`.

## How `compare` uses the checker

`compare` first converts its two machines, which have named states and
inputs, to integer tables. Input names are sorted and numbered in that order,
so "first in lexicographic order" in the theorem becomes "first in sorted
order of input names" only if that conversion is right. The conversion is
tested and is not proved.

It then calls a private function, `_search`, and acts on what `_search`
proposes.

| `_search` proposes | Function that decides | If it returns false |
|---|---|---|
| A word and labels | `Verdict.Check` with `Differs(word)` | `RuntimeError` |
| No difference, and a relation between states | `Compatibility.Check` | `RuntimeError` |

Two Dafny checkers are in use, for a historical reason. `Compatibility.Check`
is the older checker of simulation relations, and `compare` already returned
such a relation as its certificate for a "no difference" answer. I kept that
format. Two lemmas in `Verdict.dfy` show that the two forms carry the same
evidence: `AcceptedRelationIsCompatible` says that labelling the pairs of an
accepted relation `Never` and all other pairs 0 passes `Verdict.Check` with
`Compatible`, and `CompatibleGivesAcceptedRelation` says that the pairs
labelled `Never` in an accepted `Compatible` certificate form a relation that
`Compatibility.Check` accepts. So the uniqueness theorem covers both answers.

`compare` raises `RuntimeError` when a checker returns false, when the
checker process fails, and when it runs for more than 30 seconds. It never
returns an answer in those cases, and it has no other way of producing one.

"The search is replaceable" means this and no more: no theorem mentions the
search, so whichever code produces the word and labels, an answer that
`compare` returns is the specified one. There is no public interface for
supplying a different search. The tests replace `_search` directly.

A returned difference also carries a `reason` field and the two machines'
outputs along the word. Those are computed in Python after the check and are
tested, not proved.

## Evidence from tests

None of this is needed for the theorems. It is evidence about the parts the
theorems do not cover, and a guard against a specification that proves less
than intended.

**Weakened checkers.** Five files in `negative/` each change one condition in
a checker, and the reproof below requires Dafny to fail on every one. Three
predate this work and concern `Compatibility.Check` and `Replay.Mismatch`.
Two concern `Verdict.Check`:

| File | Condition removed | What Dafny can no longer prove |
|---|---|---|
| `VerdictMissedLaterDifferenceMutant.dfy` | A `Never` pair leads only to `Never` pairs. | `NeverHasNoDifference`, which `CompatibleMeansNoDifference` uses |
| `VerdictAnyShortestWordMutant.dfy` | `SmallerInputsRuledOut` | `NoEarlierWord`, and that `Differs([1])` fails in the tie example |

**Six searches against the generated checker.**
`examples/operations/verdict_searches.py` has three searches written to be
correct (exact backward distances, forward breadth-first with relaxation, and
iterative deepening that keeps only the bounds it established) and three
written to be wrong (ties broken towards the largest input, looking only at
the initial states, and returning the first difference a depth-first walk
finds). `scripts/check/check_verdict_experiment.py` runs all six on 4,001
pairs of machines and passes each output to the Python generated from
`Check`.

The 4,001 pairs are:

- All 2,500 ordered pairs of machines with two states, one input and outputs
  in {0, 1}. Each of the two transitions is absent or has one of two next
  states and one of two outputs, and either state can be initial, which
  gives 50 machines.
- 1,500 pairs drawn with seed 20261117, each machine having two or three
  states, two or three inputs, outputs in {0, 1}, and each transition chosen
  uniformly from "absent" and every next state and output.
- One pair with 19 states whose only difference is 19 inputs long.

The reference answer for each pair comes from enumerating input sequences in
order of length and then lexicographic order, up to length |S| x |T|, the
number of state pairs. That bound is complete because a shortest difference
never visits the same pair of states twice.

| Search | Passed `Check` | Failed `Check` | Passed with an answer unequal to the reference |
|---|---|---|---|
| backward | 4,001 | 0 | 0 |
| forward | 4,001 | 0 | 0 |
| deepening | 4,001 | 0 | 0 |
| largest input first | 3,298 | 703 | 0 |
| initial states only | 3,180 | 821 | 0 |
| first found | 3,706 | 295 | 0 |

A wrong search passes on the pairs where its answer and labels happen to be
right. A right answer with labels that do not satisfy `LabelsHold` also
fails.

**Through `compare`.** `tests/test_compatibility_verdict.py` replaces
`_search` and calls `compare`. `compare` raises `RuntimeError` for each of
these proposals: "no difference" for two machines that differ only after the
first input, a shortest difference that is not the first, a difference that
is not shortest, and the right word with labels that fail. It also runs the
six searches on 41 pairs of machines with named states and inputs. With the
three correct searches `compare` returns the same answer as with `_search`.
With each wrong search it either returns that same answer or raises. The
same file tests that reordering the declarations of states and inputs does
not change the answer, and that a difference 3,001 inputs long passes.

## What is not proved

- The search, including whether it terminates.
- The conversion from named machines to integer tables, the `reason` field
  and the output lists. These are Python, covered by tests.
- Running time. `Check` examines every pair of states and every input. For
  two chain-shaped machines with 1,501 states and one input (about 2.25
  million pairs), the check took about 11 seconds on an Apple M4 laptop with
  Python 3.12. Above the 30-second limit `compare` raises.
- That the generated Python has the same behaviour as the Dafny function.
  The Dafny compiler and its Python runtime are trusted. The hash check
  described below detects a packaged file that differs from the recorded
  build. It is not a defence against someone who can change the recorded
  hashes as well.
- That a machine describes a real program.

## Reproduce

From the repository root, with the Dafny build
`4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2` from the official 4.11.0
release:

```bash
python3 scripts/check/check_compatibility_kernel.py --dafny /path/to/dafny
python3 scripts/check/check_verdict_experiment.py --dafny /path/to/dafny
```

The first command verifies `Compatibility.dfy`, `Replay.dfy`, `Verdict.dfy`
and `VerdictExists.dfy`, requires the five weakened checkers to fail,
regenerates the Python and requires it to equal the files in
`src/plectis/compatibility/_generated/` byte for byte. The second runs the
six searches. Neither has a fallback that works without Dafny.

`metadata.json` in this directory records the SHA-256 of every Dafny source
and generated file. The integration into `compare` was merged in pull request
143.
