// Verdict checker for the finite compatibility comparison, 17 November 2026.
// The search that produces a verdict stays outside the proof. This file
// proves what an accepted verdict means, whatever produced it.
// Replay.dfy and Compatibility.dfy are included unchanged.
include "../Replay.dfy"

module Verdict {
  import C = Compatibility
  import R = Replay

  // What a comparison reports: no difference on any input word, or one word
  // on which the candidate differs.
  datatype Verdict = Compatible | Differs(word: seq<int>)

  // A certificate gives every pair of states one integer.
  //   -1     no input word from this pair reaches a difference
  //   n >= 0 no input word shorter than n reaches a difference
  // Labels are claims by the search. LabelsHold checks them on every enabled
  // transition; nothing about them is trusted.
  const Never: int := -1

  predicate Shape(approved: R.Model, candidate: R.Model, labels: seq<seq<int>>) {
    |labels| == |approved.next| &&
    forall s :: 0 <= s < |labels| ==>
      |labels[s]| == |candidate.next| &&
      forall t :: 0 <= t < |labels[s]| ==> Never <= labels[s][t]
  }

  // The candidate lacks an input the approved model allows, or answers it
  // with a different output.
  predicate DiffersNow(approved: R.Model, candidate: R.Model, s: int, t: int, a: int)
    requires R.ValidPair(approved, candidate)
    requires 0 <= s < |approved.next| && 0 <= t < |candidate.next|
    requires 0 <= a < approved.inputs
  {
    candidate.next[t][a] < 0 || approved.output[s][a] != candidate.output[t][a]
  }

  predicate LabelsHold(approved: R.Model, candidate: R.Model, labels: seq<seq<int>>)
    requires R.ValidPair(approved, candidate)
  {
    Shape(approved, candidate, labels) &&
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

  // No allowed input smaller than `first` differs at once, and none leads to
  // a pair that can reach a difference in fewer than `remaining` inputs.
  predicate SmallerInputsRuledOut(approved: R.Model, candidate: R.Model,
                                  labels: seq<seq<int>>, s: int, t: int,
                                  first: int, remaining: int)
    requires R.ValidPair(approved, candidate)
    requires Shape(approved, candidate, labels)
    requires 0 <= s < |approved.next| && 0 <= t < |candidate.next|
    requires 0 <= first < approved.inputs
  {
    forall a :: 0 <= a < first && 0 <= approved.next[s][a] ==>
      !DiffersNow(approved, candidate, s, t, a) &&
      (labels[approved.next[s][a]][candidate.next[t][a]] == Never ||
       remaining <= labels[approved.next[s][a]][candidate.next[t][a]])
  }

  // The word walks to a difference, and at every step each smaller allowed
  // input is shown unable to reach a difference in the inputs that remain.
  predicate FirstWord(approved: R.Model, candidate: R.Model, labels: seq<seq<int>>,
                      s: int, t: int, word: seq<int>)
    requires R.ValidPair(approved, candidate)
    requires Shape(approved, candidate, labels)
    requires 0 <= s < |approved.next| && 0 <= t < |candidate.next|
    decreases |word|
  {
    // Written as a chain of tests so that the compiled checker loops over
    // the word instead of recursing once per input.
    if |word| == 0 || word[0] < 0 || approved.inputs <= word[0] ||
       approved.next[s][word[0]] < 0
      then false
    else if DiffersNow(approved, candidate, s, t, word[0])
      then |word| == 1
    else FirstWord(approved, candidate, labels, approved.next[s][word[0]],
                   candidate.next[t][word[0]], word[1..])
  }

  // The executable checker. A search may report a verdict only when this
  // returns true for the verdict and the labels it supplies.
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

  // Order on words of equal length: smaller at the first place they differ.
  ghost predicate Before(x: seq<int>, y: seq<int>)
    decreases |x|
  {
    |x| == |y| && |x| > 0 &&
    (x[0] < y[0] || (x[0] == y[0] && Before(x[1..], y[1..])))
  }

  lemma NeverHasNoDifference(approved: R.Model, candidate: R.Model, labels: seq<seq<int>>,
                             s: int, t: int, word: seq<int>)
    requires R.ValidPair(approved, candidate) && LabelsHold(approved, candidate, labels)
    requires 0 <= s < |approved.next| && 0 <= t < |candidate.next|
    requires labels[s][t] == Never
    ensures !R.MismatchFrom(approved, candidate, s, t, word)
    decreases |word|
  {
    if |word| > 0 && 0 <= word[0] < approved.inputs && 0 <= approved.next[s][word[0]] {
      var a := word[0];
      assert !DiffersNow(approved, candidate, s, t, a);
      NeverHasNoDifference(approved, candidate, labels, approved.next[s][a],
                           candidate.next[t][a], word[1..]);
    }
  }

  lemma LabelIsLowerBound(approved: R.Model, candidate: R.Model, labels: seq<seq<int>>,
                          s: int, t: int, word: seq<int>)
    requires R.ValidPair(approved, candidate) && LabelsHold(approved, candidate, labels)
    requires 0 <= s < |approved.next| && 0 <= t < |candidate.next|
    requires R.MismatchFrom(approved, candidate, s, t, word)
    ensures 0 <= labels[s][t] <= |word|
    decreases |word|
  {
    var a := word[0];
    if labels[s][t] == Never {
      NeverHasNoDifference(approved, candidate, labels, s, t, word);
    } else if !DiffersNow(approved, candidate, s, t, a) {
      LabelIsLowerBound(approved, candidate, labels, approved.next[s][a],
                        candidate.next[t][a], word[1..]);
    }
  }

  lemma FirstWordDiffers(approved: R.Model, candidate: R.Model, labels: seq<seq<int>>,
                         s: int, t: int, word: seq<int>)
    requires R.ValidPair(approved, candidate) && Shape(approved, candidate, labels)
    requires 0 <= s < |approved.next| && 0 <= t < |candidate.next|
    requires FirstWord(approved, candidate, labels, s, t, word)
    ensures R.MismatchFrom(approved, candidate, s, t, word)
    decreases |word|
  {
    if !DiffersNow(approved, candidate, s, t, word[0]) {
      FirstWordDiffers(approved, candidate, labels, approved.next[s][word[0]],
                       candidate.next[t][word[0]], word[1..]);
    }
  }

  lemma NoEarlierWord(approved: R.Model, candidate: R.Model, labels: seq<seq<int>>,
                      s: int, t: int, word: seq<int>, other: seq<int>)
    requires R.ValidPair(approved, candidate) && LabelsHold(approved, candidate, labels)
    requires 0 <= s < |approved.next| && 0 <= t < |candidate.next|
    requires FirstWord(approved, candidate, labels, s, t, word)
    requires R.MismatchFrom(approved, candidate, s, t, other)
    requires |other| == |word|
    ensures !Before(other, word)
    decreases |word|
  {
    var a, b := word[0], other[0];
    if b < a {
      assert !DiffersNow(approved, candidate, s, t, b);
      LabelIsLowerBound(approved, candidate, labels, approved.next[s][b],
                        candidate.next[t][b], other[1..]);
    } else if b == a && !DiffersNow(approved, candidate, s, t, a) {
      NoEarlierWord(approved, candidate, labels, approved.next[s][a],
                    candidate.next[t][a], word[1..], other[1..]);
    }
  }

  lemma SameLengthNeitherBeforeIsEqual(x: seq<int>, y: seq<int>)
    requires |x| == |y| && !Before(x, y) && !Before(y, x)
    ensures x == y
    decreases |x|
  {
    if |x| > 0 {
      SameLengthNeitherBeforeIsEqual(x[1..], y[1..]);
      assert x == [x[0]] + x[1..] && y == [y[0]] + y[1..];
    }
  }

  // An accepted Compatible verdict: the candidate differs on no input word.
  // Mismatch is the replay checker's definition, proved exact in Replay.dfy.
  lemma CompatibleMeansNoDifference(approved: R.Model, candidate: R.Model,
                                    labels: seq<seq<int>>, word: seq<int>)
    requires Check(approved, candidate, labels, Compatible)
    ensures !R.Mismatch(approved, candidate, word)
  {
    NeverHasNoDifference(approved, candidate, labels, approved.initial,
                         candidate.initial, word);
  }

  // An accepted Differs verdict: the word is a difference, no difference is
  // shorter, and no difference of the same length comes earlier in input order.
  lemma DiffersMeansFirstShortest(approved: R.Model, candidate: R.Model,
                                  labels: seq<seq<int>>, word: seq<int>, other: seq<int>)
    requires Check(approved, candidate, labels, Differs(word))
    ensures R.Mismatch(approved, candidate, word)
    ensures R.Mismatch(approved, candidate, other) ==>
              |word| <= |other| && !Before(other, word)
  {
    FirstWordDiffers(approved, candidate, labels, approved.initial, candidate.initial, word);
    if R.Mismatch(approved, candidate, other) {
      LabelIsLowerBound(approved, candidate, labels, approved.initial,
                        candidate.initial, other);
      if |other| == |word| {
        NoEarlierWord(approved, candidate, labels, approved.initial,
                      candidate.initial, word, other);
      }
    }
  }

  // Two searches, two certificates, one answer. Whatever produced them, two
  // accepted verdicts for the same pair of models are the same verdict.
  lemma AcceptedVerdictIsUnique(approved: R.Model, candidate: R.Model,
                                labels1: seq<seq<int>>, verdict1: Verdict,
                                labels2: seq<seq<int>>, verdict2: Verdict)
    requires Check(approved, candidate, labels1, verdict1)
    requires Check(approved, candidate, labels2, verdict2)
    ensures verdict1 == verdict2
  {
    match (verdict1, verdict2)
    case (Compatible, Compatible) =>
    case (Compatible, Differs(w)) =>
      DiffersMeansFirstShortest(approved, candidate, labels2, w, w);
      CompatibleMeansNoDifference(approved, candidate, labels1, w);
    case (Differs(w), Compatible) =>
      DiffersMeansFirstShortest(approved, candidate, labels1, w, w);
      CompatibleMeansNoDifference(approved, candidate, labels2, w);
    case (Differs(w1), Differs(w2)) =>
      DiffersMeansFirstShortest(approved, candidate, labels1, w1, w2);
      DiffersMeansFirstShortest(approved, candidate, labels2, w2, w1);
      SameLengthNeitherBeforeIsEqual(w1, w2);
  }

  // The relation certificate that Compatibility.Check accepts and the labels
  // above carry the same evidence. Marking a relation's pairs -1 and every
  // other pair 0 gives an accepted Compatible verdict, and the pairs marked
  // -1 in an accepted Compatible verdict form an accepted relation.
  ghost function LabelsOf(relation: seq<seq<bool>>): seq<seq<int>> {
    seq(|relation|, s requires 0 <= s < |relation| =>
      seq(|relation[s]|, t requires 0 <= t < |relation[s]| =>
        if relation[s][t] then Never else 0))
  }

  ghost function RelationOf(labels: seq<seq<int>>): seq<seq<bool>> {
    seq(|labels|, s requires 0 <= s < |labels| =>
      seq(|labels[s]|, t requires 0 <= t < |labels[s]| => labels[s][t] == Never))
  }

  lemma AcceptedRelationIsCompatible(approved: R.Model, candidate: R.Model,
                                     relation: seq<seq<bool>>)
    requires approved.inputs == candidate.inputs
    requires C.Check(approved.next, approved.output, approved.initial,
                     candidate.next, candidate.output, candidate.initial,
                     approved.inputs, relation)
    ensures Check(approved, candidate, LabelsOf(relation), Compatible)
  {
  }

  lemma CompatibleGivesAcceptedRelation(approved: R.Model, candidate: R.Model,
                                        labels: seq<seq<int>>)
    requires Check(approved, candidate, labels, Compatible)
    ensures C.Check(approved.next, approved.output, approved.initial,
                    candidate.next, candidate.output, candidate.initial,
                    approved.inputs, RelationOf(labels))
  {
  }

  // The checker is not vacuous. Each kind of verdict is accepted somewhere,
  // and a model compared with itself is always Compatible.
  lemma ModelIsCompatibleWithItself(model: R.Model)
    requires C.ValidMachine(model.next, model.output, model.initial, model.inputs)
    ensures Check(model, model, seq(|model.next|, s requires 0 <= s =>
                    seq(|model.next|, t requires 0 <= t => if s == t then Never else 0)),
                  Compatible)
  {
  }

  lemma BothVerdictsOccur()
    // Same outputs: compatible.
    ensures Check(R.Model([[0]], [[7]], 0, 1), R.Model([[0]], [[7]], 0, 1),
                  [[Never]], Compatible)
    // The second state answers input 0 differently: the first shortest
    // difference is input 1 then input 0, and [0, 0] is not a difference.
    ensures Check(R.Model([[0, 1], [1, 1]], [[5, 5], [6, 5]], 0, 2),
                  R.Model([[0, 1], [1, 1]], [[5, 5], [9, 5]], 0, 2),
                  [[2, 0], [0, 1]], Differs([1, 0]))
    ensures !Check(R.Model([[0, 1], [1, 1]], [[5, 5], [6, 5]], 0, 2),
                   R.Model([[0, 1], [1, 1]], [[5, 5], [9, 5]], 0, 2),
                   [[Never, Never], [Never, Never]], Compatible)
    // Labels of 0 state nothing, so they cannot support Compatible either.
    ensures !Check(R.Model([[0, 1], [1, 1]], [[5, 5], [6, 5]], 0, 2),
                   R.Model([[0, 1], [1, 1]], [[5, 5], [9, 5]], 0, 2),
                   [[0, 0], [0, 0]], Compatible)
    // A tie. Both single inputs are differences, and only input 0 is accepted.
    ensures Check(R.Model([[0, 0]], [[7, 7]], 0, 2), R.Model([[0, 0]], [[8, 8]], 0, 2),
                  [[1]], Differs([0]))
    ensures !Check(R.Model([[0, 0]], [[7, 7]], 0, 2), R.Model([[0, 0]], [[8, 8]], 0, 2),
                   [[1]], Differs([1]))
    // The candidate has no transition for the approved machine's only input.
    ensures Check(R.Model([[0]], [[7]], 0, 1), R.Model([[-1]], [[0]], 0, 1),
                  [[1]], Differs([0]))
  {
  }
}
