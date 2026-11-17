// Every valid pair of models has a verdict the checker accepts.
// Together with AcceptedVerdictIsUnique in Verdict.dfy: the accepted verdict
// is a total function of the two models. Ghost code only; nothing here runs.
include "Verdict.dfy"

module VerdictExists {
  import R = Replay
  import V = Verdict

  ghost predicate InRange(approved: R.Model, candidate: R.Model, s: int, t: int) {
    R.ValidPair(approved, candidate) &&
    0 <= s < |approved.next| && 0 <= t < |candidate.next|
  }

  ghost predicate DiffersWithin(approved: R.Model, candidate: R.Model,
                                s: int, t: int, n: int)
    requires InRange(approved, candidate, s, t)
  {
    exists word :: |word| <= n && R.MismatchFrom(approved, candidate, s, t, word)
  }

  ghost predicate CanDiffer(approved: R.Model, candidate: R.Model, s: int, t: int)
    requires InRange(approved, candidate, s, t)
  {
    exists n: nat :: DiffersWithin(approved, candidate, s, t, n)
  }

  ghost function LeastFrom(approved: R.Model, candidate: R.Model, s: int, t: int,
                           n: nat, bound: nat): (least: nat)
    requires InRange(approved, candidate, s, t)
    requires n <= bound && DiffersWithin(approved, candidate, s, t, bound)
    requires forall m :: 0 <= m < n ==> !DiffersWithin(approved, candidate, s, t, m)
    ensures DiffersWithin(approved, candidate, s, t, least)
    ensures forall m :: 0 <= m < least ==> !DiffersWithin(approved, candidate, s, t, m)
    decreases bound - n
  {
    if DiffersWithin(approved, candidate, s, t, n) then n
    else LeastFrom(approved, candidate, s, t, n + 1, bound)
  }

  // Number of inputs to the nearest difference, or Never.
  ghost function Distance(approved: R.Model, candidate: R.Model, s: int, t: int): (d: int)
    requires InRange(approved, candidate, s, t)
    ensures CanDiffer(approved, candidate, s, t) ==>
              1 <= d && DiffersWithin(approved, candidate, s, t, d) &&
              forall m :: 0 <= m < d ==> !DiffersWithin(approved, candidate, s, t, m)
    ensures !CanDiffer(approved, candidate, s, t) ==> d == V.Never
  {
    if CanDiffer(approved, candidate, s, t) then
      var bound: nat :| DiffersWithin(approved, candidate, s, t, bound);
      var least := LeastFrom(approved, candidate, s, t, 0, bound);
      assert least != 0 by {
        if least == 0 {
          var word :| |word| <= 0 && R.MismatchFrom(approved, candidate, s, t, word);
        }
      }
      least
    else V.Never
  }

  lemma Within(approved: R.Model, candidate: R.Model, s: int, t: int, word: seq<int>)
    requires InRange(approved, candidate, s, t)
    requires R.MismatchFrom(approved, candidate, s, t, word)
    ensures DiffersWithin(approved, candidate, s, t, |word|)
    ensures CanDiffer(approved, candidate, s, t)
    ensures Distance(approved, candidate, s, t) <= |word|
  {
    assert DiffersWithin(approved, candidate, s, t, |word|);
  }

  lemma Prepend(approved: R.Model, candidate: R.Model, s: int, t: int, a: int,
                rest: seq<int>)
    requires InRange(approved, candidate, s, t)
    requires 0 <= a < approved.inputs && 0 <= approved.next[s][a]
    requires !V.DiffersNow(approved, candidate, s, t, a)
    requires R.MismatchFrom(approved, candidate, approved.next[s][a],
                            candidate.next[t][a], rest)
    ensures R.MismatchFrom(approved, candidate, s, t, [a] + rest)
  {
    assert ([a] + rest)[0] == a && ([a] + rest)[1..] == rest;
  }

  ghost function TrueLabels(approved: R.Model, candidate: R.Model): (labels: seq<seq<int>>)
    requires R.ValidPair(approved, candidate)
    ensures V.Shape(approved, candidate, labels)
    ensures forall s, t :: InRange(approved, candidate, s, t) ==>
              labels[s][t] == Distance(approved, candidate, s, t)
  {
    seq(|approved.next|, s requires 0 <= s < |approved.next| =>
      seq(|candidate.next|, t requires 0 <= t < |candidate.next| =>
        Distance(approved, candidate, s, t)))
  }

  lemma OneStep(approved: R.Model, candidate: R.Model, s: int, t: int, a: int)
    requires InRange(approved, candidate, s, t)
    requires 0 <= a < approved.inputs && 0 <= approved.next[s][a]
    ensures V.DiffersNow(approved, candidate, s, t, a) ==>
              Distance(approved, candidate, s, t) == 1
    ensures !V.DiffersNow(approved, candidate, s, t, a) ==>
              InRange(approved, candidate, approved.next[s][a], candidate.next[t][a]) &&
              (CanDiffer(approved, candidate, approved.next[s][a], candidate.next[t][a]) ==>
                 CanDiffer(approved, candidate, s, t) &&
                 Distance(approved, candidate, s, t) <=
                   1 + Distance(approved, candidate, approved.next[s][a], candidate.next[t][a]))
  {
    if V.DiffersNow(approved, candidate, s, t, a) {
      assert R.MismatchFrom(approved, candidate, s, t, [a]);
      Within(approved, candidate, s, t, [a]);
    } else {
      var s', t' := approved.next[s][a], candidate.next[t][a];
      if CanDiffer(approved, candidate, s', t') {
        var d := Distance(approved, candidate, s', t');
        var rest :| |rest| <= d && R.MismatchFrom(approved, candidate, s', t', rest);
        Prepend(approved, candidate, s, t, a, rest);
        Within(approved, candidate, s, t, [a] + rest);
      }
    }
  }

  lemma TrueLabelsHold(approved: R.Model, candidate: R.Model)
    requires R.ValidPair(approved, candidate)
    ensures V.LabelsHold(approved, candidate, TrueLabels(approved, candidate))
  {
    forall s, t, a |
      0 <= s < |approved.next| && 0 <= t < |candidate.next| &&
      0 <= a < approved.inputs && 0 <= approved.next[s][a]
      ensures V.DiffersNow(approved, candidate, s, t, a) ==>
                Distance(approved, candidate, s, t) == 1
      ensures !V.DiffersNow(approved, candidate, s, t, a) ==>
                InRange(approved, candidate, approved.next[s][a], candidate.next[t][a]) &&
                (CanDiffer(approved, candidate, approved.next[s][a], candidate.next[t][a]) ==>
                   CanDiffer(approved, candidate, s, t) &&
                   Distance(approved, candidate, s, t) <=
                     1 + Distance(approved, candidate, approved.next[s][a], candidate.next[t][a]))
    {
      OneStep(approved, candidate, s, t, a);
    }
  }

  // Input a starts a word that reaches a difference as fast as possible.
  ghost predicate Leads(approved: R.Model, candidate: R.Model, s: int, t: int, a: int)
    requires InRange(approved, candidate, s, t)
  {
    0 <= a < approved.inputs && 0 <= approved.next[s][a] &&
    (V.DiffersNow(approved, candidate, s, t, a) ||
     (CanDiffer(approved, candidate, approved.next[s][a], candidate.next[t][a]) &&
      Distance(approved, candidate, approved.next[s][a], candidate.next[t][a]) <
        Distance(approved, candidate, s, t)))
  }

  lemma SomeInputLeads(approved: R.Model, candidate: R.Model, s: int, t: int)
    requires InRange(approved, candidate, s, t) && CanDiffer(approved, candidate, s, t)
    ensures exists a :: Leads(approved, candidate, s, t, a)
  {
    var d := Distance(approved, candidate, s, t);
    var word :| |word| <= d && R.MismatchFrom(approved, candidate, s, t, word);
    var a := word[0];
    if !V.DiffersNow(approved, candidate, s, t, a) {
      Within(approved, candidate, approved.next[s][a], candidate.next[t][a], word[1..]);
    }
    assert Leads(approved, candidate, s, t, a);
  }

  ghost function SmallestLeading(approved: R.Model, candidate: R.Model, s: int, t: int,
                                 a: nat, some: int): (first: int)
    requires InRange(approved, candidate, s, t)
    requires a <= some && Leads(approved, candidate, s, t, some)
    requires forall b :: 0 <= b < a ==> !Leads(approved, candidate, s, t, b)
    ensures Leads(approved, candidate, s, t, first)
    ensures forall b :: 0 <= b < first ==> !Leads(approved, candidate, s, t, b)
    decreases some - a
  {
    if Leads(approved, candidate, s, t, a) then a
    else SmallestLeading(approved, candidate, s, t, a + 1, some)
  }

  ghost function FirstInput(approved: R.Model, candidate: R.Model, s: int, t: int): (a: int)
    requires InRange(approved, candidate, s, t) && CanDiffer(approved, candidate, s, t)
    ensures Leads(approved, candidate, s, t, a)
    ensures forall b :: 0 <= b < a ==> !Leads(approved, candidate, s, t, b)
  {
    SomeInputLeads(approved, candidate, s, t);
    var some :| Leads(approved, candidate, s, t, some);
    SmallestLeading(approved, candidate, s, t, 0, some)
  }

  ghost function FirstShortest(approved: R.Model, candidate: R.Model, s: int, t: int): seq<int>
    requires InRange(approved, candidate, s, t) && CanDiffer(approved, candidate, s, t)
    decreases Distance(approved, candidate, s, t)
  {
    var a := FirstInput(approved, candidate, s, t);
    if V.DiffersNow(approved, candidate, s, t, a) then [a]
    else [a] + FirstShortest(approved, candidate, approved.next[s][a], candidate.next[t][a])
  }

  lemma FirstShortestIsAccepted(approved: R.Model, candidate: R.Model, s: int, t: int)
    requires InRange(approved, candidate, s, t) && CanDiffer(approved, candidate, s, t)
    ensures |FirstShortest(approved, candidate, s, t)| == Distance(approved, candidate, s, t)
    ensures V.FirstWord(approved, candidate, TrueLabels(approved, candidate), s, t,
                        FirstShortest(approved, candidate, s, t))
    decreases Distance(approved, candidate, s, t)
  {
    var a := FirstInput(approved, candidate, s, t);
    var word := FirstShortest(approved, candidate, s, t);
    var labels := TrueLabels(approved, candidate);
    OneStep(approved, candidate, s, t, a);
    if !V.DiffersNow(approved, candidate, s, t, a) {
      FirstShortestIsAccepted(approved, candidate, approved.next[s][a], candidate.next[t][a]);
      assert word[1..] ==
             FirstShortest(approved, candidate, approved.next[s][a], candidate.next[t][a]);
    }
    forall b | 0 <= b < a && 0 <= approved.next[s][b]
      ensures !V.DiffersNow(approved, candidate, s, t, b)
      ensures labels[approved.next[s][b]][candidate.next[t][b]] == V.Never ||
              |word| <= labels[approved.next[s][b]][candidate.next[t][b]]
    {
      assert !Leads(approved, candidate, s, t, b);
      OneStep(approved, candidate, s, t, b);
    }
  }

  // The checker accepts some verdict for every valid pair of models.
  lemma EveryPairHasAVerdict(approved: R.Model, candidate: R.Model)
    returns (labels: seq<seq<int>>, verdict: V.Verdict)
    requires R.ValidPair(approved, candidate)
    ensures V.Check(approved, candidate, labels, verdict)
  {
    labels := TrueLabels(approved, candidate);
    TrueLabelsHold(approved, candidate);
    var s, t := approved.initial, candidate.initial;
    if CanDiffer(approved, candidate, s, t) {
      FirstShortestIsAccepted(approved, candidate, s, t);
      verdict := V.Differs(FirstShortest(approved, candidate, s, t));
    } else {
      verdict := V.Compatible;
    }
  }
}
