# What is proved about `compare`, and what is only tested

`plectis.compatibility.compare(approved, candidate)` takes two finite state
machines. Its documentation says it returns one of two answers:

- every input sequence that the approved machine can run gets the same
  outputs from the candidate, or
- the shortest input sequence for which that fails, and if several have that
  length, the first in lexicographic order of inputs.

A call can also raise an exception, as described below.

Before 17 November 2026 a Python breadth-first search produced the answer,
and only tests covered "shortest" and "first". This note describes what
replaced those tests. The search is still unverified Python. It now also
produces a certificate, and `compare` returns the answer only if a function
generated from Dafny returns true for the answer and the certificate. That is
a certifying algorithm in the sense of Alkassar, Böhme, Mehlhorn and
Rizkallah, *A Framework for the Verification of Certifying Computations*, and
the certificate is a table of shortest-path lower bounds of the kind used
there. The method is not new. What was done here is to apply it to one
documented promise of an existing tool, and to prove that the checker passes
exactly one answer for each pair of machines.

The proofs are about a Dafny predicate. Whether a call to `compare` gives the
right answer depends on more than that, and this table lists what it depends
on and how each item is supported.

| Statement | Support |
|---|---|
| For every valid pair of integer-table machines, exactly one `Verdict` passes `Check`. It is the answer above. | Proved in Dafny. |
| The Python that runs is what Dafny 4.11.0 generates from that source. | Regenerated and compared byte for byte. The Dafny compiler is trusted. |
| `compare` checks the machines it was called with, correctly converted, and reports the checked answer. | Tests only. |
| The other fields `compare` returns with a difference are correct. | Tests only. |
| The definition of a difference used here is the right one for a given use. | Not addressed. |
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
The `output` entry of an absent transition is never read.

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

Preconditions are left out of this listing and of the ones below. The source
has them.

A *difference* between the two machines is a difference from their two
initial states (`Replay.Mismatch`).

Four consequences of this definition:

- Words are finite. Nothing here concerns infinite runs, fairness or liveness.
- Once an input gives a difference, the rest of the word is not examined. A
  difference followed by any further inputs is also a difference. The word
  that `Check` accepts ends at its first differing input.
- The definition is one-directional. Both tables are indexed by the same
  inputs, and an input that only the candidate has in some state is one with
  `approved.next[s][a] == -1` there. Such an input is never a difference.
- If the approved machine has no transition from its initial state, there is
  no difference, whatever the candidate does.

"No difference" therefore means that the candidate can run every finite
input sequence the approved machine can run, with the same outputs. For
deterministic machines that holds exactly when a simulation relation exists,
which is what the older checker `Compatibility.Check` tests. It does not mean
the two machines are equivalent.

## What this specification settles and what it leaves open

Every theorem below is relative to `Mismatch`. Together they say that `Check`
passes the first shortest `Mismatch`, or `Compatible` when there is none, and
nothing else. They do not say that `Mismatch` is the comparison a particular
user needs.

This file's own history is an example of that risk. The first contract for
the replay checker required every reported difference to be real and did not
require an existing difference to be reported. A checker that looked for a
difference only while the candidate was in its initial state satisfied it
(`negative/ReplayMissedDifferenceMutant.dfy`). The converse was added later.

The specification is also more restrictive than correctness needs. Any
shortest difference is a correct counterexample. `compare` already documented
one particular answer, the shortest and then the first by input order, so
that stored results and tests do not change between runs or implementations.
The proofs are of that documented promise. A specification that allowed any
shortest difference would be just as legitimate, and under it
`AcceptedVerdictIsUnique` would be false.

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
machine in state `s`. Some parameter types are left out of the listing.

```dafny
predicate DiffersNow(approved: R.Model, candidate: R.Model, s: int, t: int, a: int)
{
  candidate.next[t][a] < 0 || approved.output[s][a] != candidate.output[t][a]
}

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

predicate SmallerInputsRuledOut(approved, candidate, labels, s, t,
                                first: int, remaining: int)
{
  forall a :: 0 <= a < first && 0 <= approved.next[s][a] ==>
    !DiffersNow(approved, candidate, s, t, a) &&
    (labels[approved.next[s][a]][candidate.next[t][a]] == Never ||
     remaining <= labels[approved.next[s][a]][candidate.next[t][a]])
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

Why these local tests are enough:

- **`Never` is sound.** By `LabelsHold`, a pair labelled `Never` has no
  immediate difference and every transition from it leads to a pair labelled
  `Never`. By induction on the length of the word, no word from such a pair
  is a difference. `Compatible` requires the initial pair to be labelled
  `Never`.
- **Labels are lower bounds.** A difference of length `k` from a successor
  pair gives a difference of length `k + 1` from the pair itself, so a true
  lower bound for a pair can exceed a true lower bound for a successor by at
  most one. `LabelsHold` requires exactly that, and requires a label of at
  most 1 where there is an immediate difference. By induction on the length
  of the word, a difference from (s, t) has length at least `labels[s][t]`.
- **The word is a shortest difference.** `FirstWord` follows the word and
  requires its last input, and no earlier one, to be an immediate difference.
  `Check` requires the initial label to equal the length of the word, so no
  difference is shorter.
- **The word is the first of the shortest.** Suppose the walk has reached
  (s, t) and the word has `r` inputs left, counting the next one. Take an
  input `a` smaller than that next input. `SmallerInputsRuledOut` says that
  `a` is not an immediate difference and leads to a pair whose label is at
  least `r`. A difference that takes `a` here needs `a` and then at least `r`
  more inputs, which is `r + 1` from this point. The word needs `r`. So no
  difference of the word's length takes a smaller input at any step.

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
by returning false for everything. Its proof is ghost code. It defines the
label of each pair as its exact distance to a difference, or `Never` if there
is none, and defines the word by taking at each step the smallest input that
is an immediate difference or leads one step closer. It is not a program that
produces certificates.

Together the third and fourth say that for each valid pair of machines
exactly one `Verdict` passes `Check` with some labels. Many different labels
can pass with it. That is a statement about `Check`. It
does not say that a particular search finishes or that its labels pass.

The lemma `BothVerdictsOccur` proves the value of `Check` on the concrete
cases in the next section. These are proved statements about the Dafny
function. They are not runs of the generated Python.

`dafny audit` reports no `assume` statements or unproved lemmas in these two
files. Dafny, Boogie and Z3 are still trusted.

## Four examples proved in Dafny

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

The pairs (0, 1) and (1, 0) cannot be reached from the initial pair. Each
has a difference of length one, and its label is left at 0, which is a true
lower bound for any pair. `LabelsHold` tests those two pairs as well and they
pass.

For the same machines `Check` returns false for `Compatible` in two ways.
With every label `Never` it fails `LabelsHold`, because the pair (1, 1) has
an immediate difference and so cannot be labelled `Never`. With every label 0
it passes `LabelsHold` and fails because `Compatible` requires the initial
pair to be labelled `Never`.

**A tie.** One state, two inputs, both transitions return to that state. The
approved outputs are 7 and 7 and the candidate outputs are 8 and 8, so each
single input is a difference. With the label 1, `Check` returns true for
`Differs([0])` and false for `Differs([1])`.

**A missing transition.** One state, one input. The approved machine returns
to its state with output 7 and the candidate has no transition. With the
label 1, `Check` returns true for `Differs([0])`.

**No difference, with a cycle.** One state, one input, the transition returns
to that state, and both machines output 7. There are finite input sequences
of every length and none is a difference. `Check` returns true for `Compatible`
with the label `Never`.

## How `compare` uses the checkers

Everything in this section is Python and is covered by tests, not proofs.

`compare` first validates its two arguments and raises `InvalidMachine` if
either is malformed. It converts them to integer tables. The inputs are the
union of the two machines' input names, sorted with Python's `sorted`, which
orders strings by Unicode code point, and numbered in that order. "First in
lexicographic order" in the theorem is "first by that order of input names"
only if this conversion is right.

It then calls a private function, `_search`, on copies of the two machines,
and acts on what `_search` returns. The two kinds of proposal have different
shapes:

| `_search` returns | Function that decides | If it returns false |
|---|---|---|
| A word, and labels for some pairs of states | `Verdict.Check` with `Differs(word)` | `RuntimeError` |
| No word, and a set of pairs of states | `Compatibility.Check` on that relation | `RuntimeError` |

For a word, `compare` gives every pair that `_search` did not label the
label 0 before calling `Check`. The built-in `_search` labels the pairs
reachable from the initial pair with their exact distances.

Two Dafny checkers are in use, for a historical reason. `Compatibility.Check`
is the older checker of simulation relations, and `compare` already returned
such a relation as its certificate when there is no difference. I kept that
format. Two lemmas in `Verdict.dfy` relate acceptance by one checker to
acceptance by the other. `AcceptedRelationIsCompatible` says that if
`Compatibility.Check` accepts a relation, then labelling its pairs `Never`
and all other pairs 0 passes `Verdict.Check` with `Compatible`.
`CompatibleGivesAcceptedRelation` says that the pairs labelled `Never` in
labels that pass with `Compatible` form a relation that `Compatibility.Check`
accepts. So an answer that passes either checker is the one verdict of the
uniqueness theorem.

`compare` raises `RuntimeError` when a checker returns false, when the
checker process fails, and when the checker process runs for more than 30
seconds. In those cases it returns no answer, and it has no other way of
producing one. The 30 seconds apply to each checker process. The search has
no time limit.

What "the search is replaceable" means here is limited. No theorem mentions
the search. So if the conversion to integer tables is right, a verdict that
`compare` returns is the specified one, whichever code proposed it. It does
not follow that another search finishes, or that its labels pass. There is no
public interface for supplying a search, and the tests replace `_search`
directly. `_search` is given copies, so a search that edits its machines does
not change the machines that are checked. Code running in the same Python
process could interfere in other ways, for example by replacing the function
that calls the checker, and nothing here defends against that.

The two return values look like this:

```python
{"accepted": True, "certificate": {"schema_version": 1, "approved_sha256": "...",
                                   "candidate_sha256": "...", "relation": [["idle", "start"]]}}

{"accepted": False, "continuation": ["next", "a"], "reason": "output_mismatch",
 "approved_outputs": ["ok", "good"], "candidate_outputs": ["ok", "bad"]}
```

`continuation` is the word that passed `Verdict.Check`, with input names put
back. `reason` and the two lists of outputs are computed in Python afterwards
by running both machines on that word.

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
`examples/operations/verdict_searches.py` has three searches intended to be
correct, none of them proved (exact backward distances, forward breadth-first with relaxation, and
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
- One pair with 19 states whose shortest difference is 19 inputs long.

The reference answer is "no difference" for 1,067 of the pairs. Machines with
one input cannot have two differences of the same length, so only the 1,500
random pairs can exercise the tie rule.

The reference answer for each pair comes from enumerating input sequences in
order of length and then lexicographic order, up to length |S| x |T|, the
number of state pairs. That bound is complete because a shortest difference
never visits the same pair of states twice. The enumeration uses the same
definition of a difference as `Mismatch`, so agreement with it is evidence
about the searches and the checker. It is not evidence that the definition
is the right one.

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
is not shortest, the right word with labels that fail, and "no difference"
from a search that first edits its copy of the candidate. It also runs the
six searches on 41 pairs of machines with named states and inputs: one
written by hand and 40 random pairs with two or three states and two inputs. With the
three correct searches `compare` returns the same answer as with `_search`.
With each wrong search it either returns that same answer or raises. The
same file tests that reordering the declarations of states and inputs does
not change the answer. It also tests a difference 3,001 inputs long, which is
there because Python's default recursion limit is 1,000 and the generated
word check has to be a loop.

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

From the root of `github.com/wcook04/practical-formal-verification` on its
`main` branch, with the Dafny build
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
