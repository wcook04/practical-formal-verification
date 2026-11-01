<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Plectis

<a id="mathematical-research-and-the-system-behind-it"></a>

Plectis is research on eight problems posed by Paul Erdős: a short paper and a
longer record for each problem, Lean proofs of selected statements, experiments
and failed approaches. On the public maths map, every result in the sixteen
problem papers appears with its Lean statements and Comparator records.

**[Open the maths map](https://wcook04.github.io/practical-formal-verification/map/#mathematics)** · **[Inspect one result](#inspect-one-result)** · **[Formal Conjectures](#formal-conjectures-contributions)** · **[Papers](#problem-papers)** · **[Repository map](#repository-map)**

<a id="choose-a-way-in"></a>

## Use it

- **In a browser, with nothing to install:** open the [maths map](https://wcook04.github.io/practical-formal-verification/map/#mathematics), select
  Expand map and search for a theorem or a Lean declaration. Selecting a result
  shows its statement, its Lean statements and its Comparator record.
- **As a reader, without Lean:** start with [A reader's way in](docs/READING_GUIDE.md).
  The [glossary](https://wcook04.github.io/practical-formal-verification/docs/glossary.html) explains project terms.
- **In a terminal, with Git and Python 3.11 or later:** clone this repository and
  run `python3 scripts/verify_claims.py --claim finite_prime_weighted_support`.
  This prints one claim's statement, Lean declarations, Comparator interface,
  paper and limits. It finds the declarations in your checkout and does not run
  Lean. [REPRODUCIBILITY](docs/REPRODUCIBILITY.md)
  gives the clone command and the steps for rebuilding a proof in Lean.

[![Eight Erdős problem programmes: the interactive maths map connects papers, results and their formal evidence](.github/maths-map.png)](https://wcook04.github.io/practical-formal-verification/map/#mathematics)

<sub>The maths map on 9 October 2026. Select the image to open the current map.</sub>

## Inspect one result

[Problem 257](https://www.erdosproblems.com/257) asks whether the series

$$\sum_{a\in A} \frac{1}{2^a-1}$$

is irrational for **every infinite set $A$ of positive integers**. That question
remains open. Theorem 1.2 of the [#257 short paper](paper/257/erdos-257-mersenne-support-subseries.pdf)
proves irrationality at every integer base at least two for infinite sets that
meet a finite-prime weighted condition. The records for this theorem are:

- **Statement:** [Theorem 1.2 on the map](https://wcook04.github.io/practical-formal-verification/maths/universe.html#o=statement%3Aerdos-257-mersenne-support-subseries%23res%3Aweighted-support).
- **Lean proof:** [`divisibilityWeightedClaim`](lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L120).
  The [evidence record](evidence/erdos-257-mersenne-support-subseries.md#res-weighted-support)
  sets the printed theorem beside the Lean statements.
- **What Lean establishes:** that the exact formal statement in that file is proved.
- **What Comparator states:** [run 35935225572 passed](evidence/erdos-257-mersenne-support-subseries.md#res-weighted-support-comparator),
  comparing the proof with the same statement written separately from Mathlib,
  with only the axioms `propext`, `Quot.sound` and `Classical.choice` allowed.
- **What neither tool establishes:** whether the formal statement matches the
  intended mathematics, and novelty, priority or significance.
- **Who has reviewed it:** Bo Cowgill approved commit `40f7826a` of
  [Formal Conjectures request #6528](https://github.com/google-deepmind/formal-conjectures/pull/6528) on 10 October 2026. Later
  commits followed, and the request is open with review required. Palomar
  [registered](https://palomar-registry.org/entry?id=PALOMAR-2026-09-25-000009&version=1)
  a Lean selection containing this theorem. The paper has not been peer reviewed.

[Try three changed hypotheses](docs/reading-edition/weighted-257-task.md).

<a id="about-the-project"></a>

## Status and the use of AI

The one formal answer among the eight problems concerns #1041. Using the degree-seven polynomial constructed by the erdosproblems.com
contributor ani, Lean proves that every preconnected strict-lemniscate set
containing two distinct roots has one-dimensional Hausdorff measure greater
than two. This refutes the exact Formal Conjectures path-image-length
statement; the separate total-variation bound is also checked. The other
seven targets remain open. Independent human review of correspondence with
the 1958 wording has not been recorded. Comparator checks only selected exact
statements, axioms and kernel acceptance; it does not assess novelty or
historical correspondence.

[ani's original counterexample](https://www.erdosproblems.com/forum/thread/1041#post-8861)
is credited in the [#1041 case study](docs/case-studies/formal-conjectures-1041.md).
[Results and limits](docs/RESULTS.md) gives each problem's statements with their
assumptions, earlier work and remaining questions.

Will Cook directs this independent, AI-assisted prototype and is not a
mathematician. AI agents did most of the research and drafting. He built and
directed the infrastructure, reviewed claims when he could and has not
independently verified every claim. He maintains the sources and corrects the
public record. Novelty and significance need human judgement. The records include
calculations and routes that stopped, so that other people can question, repair
or reuse them. The [system paper](paper/systems/claim-faithful-publication-systems-paper.pdf)
describes how results, corrections and credit are recorded.

## Formal Conjectures contributions

[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) is Google DeepMind's open repository of conjectures
stated in Lean. [Five contributions](docs/verification/FORMAL_CONJECTURES_CROSSWALK.md#merged-mathematical-contributions)
from this project have merged into it. The [crosswalk](docs/verification/FORMAL_CONJECTURES_CROSSWALK.md)
lists each request with its reviews and compares the eight problems with the
Formal Conjectures statements.

- [#6505](https://github.com/google-deepmind/formal-conjectures/pull/6505) answers the exact #1041 formal statement in the
  negative, credited to ani, and corrects a hidden hypothesis in the file. The
  [case study](docs/case-studies/formal-conjectures-1041.md) follows it from
  statement to proof.
- [#6529](https://github.com/google-deepmind/formal-conjectures/pull/6529) adds Erdős's classical result for infinite sets with
  summable reciprocals, at integer bases at least two. Arbitrary infinite sets
  remain open.
- [#5034](https://github.com/google-deepmind/formal-conjectures/pull/5034), [#6506](https://github.com/google-deepmind/formal-conjectures/pull/6506) and
  [#6507](https://github.com/google-deepmind/formal-conjectures/pull/6507) record Lean proofs of solved variants of #258, #257
  and #1049. All three rest on one theorem, Erdős's result of 1948.

A merge records that a maintainer accepted that exact change and covers no other
claim here. [Fourteen more requests](docs/verification/FORMAL_CONJECTURES_CROSSWALK.md#open-requests) are open with
review required. An individual approval or comment applies to that request at
the commit the crosswalk names. These reviews cover selected contributions, and
no review covers the whole corpus.

## Problem papers

Each longer record adds calculations, failed approaches and unresolved steps to
its short paper. For a first look, read the
[#257 introductory paper](paper/257/erdos257-expository-sums-never-fractions.pdf):
examples, then a proof for infinite sets whose reciprocals have a finite sum, a
result Erdős stated in 1968.

| Problem | Topic | Papers |
|---|---|---|
| [#68](https://www.erdosproblems.com/68) | [Factorial-denominator irrationality](https://wcook04.github.io/practical-formal-verification/maths/problems/erdos_68.html) | [short paper](paper/68/erdos-68-factorial-denominator-irrationality.pdf) · [longer paper](paper/68/erdos68-factorial-reasoning-surface.pdf) |
| [#243](https://www.erdosproblems.com/243) | [Cubic-rate irrationality and reciprocal tails](https://wcook04.github.io/practical-formal-verification/maths/problems/erdos_243.html) | [short paper](paper/243/erdos-243-reciprocal-tail-rigidity.pdf) · [longer paper](paper/243/erdos243-reciprocal-tail-reasoning-surface.pdf) |
| [#249](https://www.erdosproblems.com/249) | [Binary totient series](https://wcook04.github.io/practical-formal-verification/maths/problems/erdos_249.html) | [short paper](paper/249/erdos-249-binary-totient-series.pdf) · [longer paper](paper/249/erdos249-totient-reasoning-surface.pdf) |
| [#251](https://www.erdosproblems.com/251) | [Prime-gap dyadic series](https://wcook04.github.io/practical-formal-verification/maths/problems/erdos_251.html) | [short paper](paper/251/erdos-251-prime-gap-dyadic-series.pdf) · [longer paper](paper/251/erdos251-prime-gap-reasoning-surface.pdf) |
| [#257](https://www.erdosproblems.com/257) | [Mersenne-support subseries](https://wcook04.github.io/practical-formal-verification/maths/problems/erdos_257.html) | [introductory paper](paper/257/erdos257-expository-sums-never-fractions.pdf) · [short paper](paper/257/erdos-257-mersenne-support-subseries.pdf) · [longer paper](paper/257/erdos257-mersenne-reasoning-surface.pdf) |
| [#269](https://www.erdosproblems.com/269) | [Three-prime running LCM](https://wcook04.github.io/practical-formal-verification/maths/problems/erdos_269.html) | [short paper](paper/269/erdos-269-three-prime-running-lcm.pdf) · [longer paper](paper/269/erdos269-running-lcm-reasoning-surface.pdf) |
| [#1041](https://www.erdosproblems.com/1041) | [Lemniscates and Newton flow](https://wcook04.github.io/practical-formal-verification/maths/problems/erdos_1041.html) | [short paper](paper/1041/erdos-1041-lemniscate-newton-flow.pdf) · [longer paper](paper/1041/erdos1041-lemniscate-reasoning-surface.pdf) |
| [#1049](https://www.erdosproblems.com/1049) | [Rational-base Lambert series](https://wcook04.github.io/practical-formal-verification/maths/problems/erdos_1049.html) | [short paper](paper/1049/erdos-1049-rational-base-lambert.pdf) · [longer paper](paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf) |

[Reading Eight Erdős Problems Together](paper/synthesis/optimal-sparse-perturbations.pdf)
connects the problems. Its main theorems are ordinary proofs; Lean checks
specified ingredients.

<!-- BEGIN generated_corpus_at_a_glance -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
<details>
<summary>Corpus inventory and counting limits</summary>

## Corpus at a glance

The reviewed layer a mathematician should judge: 160 curated claim records in 38 contribution families, reaching Lean source through 478 principal declaration links. `docs/SCOPE.md` gives its shape and `docs/RESULTS.md` gives the strongest checked result per problem. The website and the papers are the human reading path.

The rest is engineering inventory. About 87% of the 164,639 declarations (142,668 across 695 modules) are machine-emitted certificate shards: one integer checked prime, one position excluded. The remainder is not all hand-written either.

| Engineering inventory | Current size |
|---|---:|
| Lean modules (the two library roots) | 1,903 |
| Formal results and supporting lemmas | 160,373 |
| Curated claim records | 160 |
| Contribution families | 38 |

Generated shards are counted as formal source and never as separate
mathematical claims. Claim records cover every status, including cited and
open, and are partitioned once.
These are navigation counts, not novelty claims. They still need expert validation.

</details>
<!-- END generated_corpus_at_a_glance -->

<a id="what-the-checks-establish"></a>

## What Lean and Comparator verify

Lean checks whether a proof establishes the exact formal statement in its source.
The [source map](docs/SOURCE_MAP.md) connects paper passages to those declarations,
[claim records](docs/claims.json) list their status and limits, and
[prior art](docs/PRIOR_ART.md) identifies earlier results.

Comparator checks a solution against a separately declared formal statement,
with an explicit list of permitted axioms. [`formalization.yaml`](formalization.yaml)
lists the selected statements. The [verification dossier](docs/EXTERNAL_VERIFICATION.md)
records selected statements across all eight problems. Researchers judge
correspondence with the intended mathematics, novelty and usefulness, and
[methodology](docs/METHODOLOGY.md) explains the review required to change a claim.

## Contribute

Corrections, references, counterexamples and clearer explanations need no Lean.
Use the
[research-progress form](https://github.com/wcook04/plectis-erdos/issues/new?template=research_progress.yml),
[email Will](https://wcook04.github.io/practical-formal-verification/#contact) or [work on a paper](docs/CONTRIBUTE_BY_PAPER.md).
[CONTRIBUTING](CONTRIBUTING.md) covers the rest, and accepted contributions
receive credit under the [credit policy](docs/research-commons/CREDIT_POLICY.md).

<a id="read-inspect-or-continue"></a>

## Read or verify locally

[REPRODUCIBILITY](docs/REPRODUCIBILITY.md) starts with Git and Python 3.11+, then
explains how to install Lean and check a proof. Its
[claim check](docs/REPRODUCIBILITY.md#try-one-claim-without-lean) inspects source
links without compiling the proof. For research with a coding agent, see
[AGENTS.md](AGENTS.md) and the [agent workbench](docs/agents/AGENT_WORKBENCH.md).

## Repository map

| Location | Contents |
|---|---|
| [paper/](paper/README.md) | PDFs and manuscript sources by problem. |
| [lean/](lean/README.md) | Formal proofs in the `Erdos249257` and `ErdosProblems` libraries. |
| [docs/](docs/README.md) | Guides, claim records and source maps. |
| [evidence/](evidence/README.md) | One record per paper linking each result to Lean and Comparator. |
| [verification/](verification/README.md) | Selected formal statements, solutions and Comparator configuration. |
| [computations/](computations/README.md) | Exact arithmetic certificates and scripts. |
| [research/](research/README.md) | Experiments, examples and investigations. |
| [research_corpus/](research_corpus/README.md) | Dated research contributions and unresolved obligations. |
| [scripts/](scripts/README.md) | Query tools, generators of derived files and validation programs. |
| [skills/](skills/README.md) | Workflows for coding agents using this checkout. |

The [architecture guide](docs/ARCHITECTURE.md) explains how the folders fit
together. The checkout is hundreds of megabytes, and Lean builds download more.
The [security policy](.github/SECURITY.md) covers running code from it.

<!-- BEGIN generated_principal_declaration_anchors -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Following a result into Lean

The paper links each headline result to the relevant source. For a particular
topic, start with the [source map](docs/SOURCE_MAP.md); it gives the module
order without asking you to decode Lean declaration names first.
<!-- END generated_principal_declaration_anchors -->

<a id="videos"></a>

## Videos

There are videos of the [maths map](https://www.youtube.com/watch?v=u4f-fk1o13k),
[Erdős #257](https://www.youtube.com/watch?v=uWCqtRkJ8P0) and the
[Plectis system](https://www.youtube.com/watch?v=MBmVMMogXTA). The videos also show private interfaces. Do not
infer results from private or unreleased work.

## Other records

[Palomar](https://palomar-registry.org/) checks Lean proofs and publishes
registered results with their review comments. The [submission record](https://github.com/wcook04/plectis-erdos-lean#palomar-publication-surface)
separates verification, editorial review and registration. The
[Palomar guide](docs/verification/PALOMAR_QUALIFICATION.md) explains the local
preparation checks; passing those checks alone does not establish acceptance.

[plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean)
holds the Comparator and Palomar packages, and the
[Prove2Me records](docs/research-commons/README.md#native-prove2me-theorems) cover
#243 and #257. The [paper catalogue](docs/papers/README.md) links versioned aiXiv
editions, which may differ from the current papers.

<details>
<summary>How a reader moves from the website to the research record</summary>

[![Website → papers → research records and open questions](.github/system-map.png)](.github/system-map.svg)

</details>

## Credit

One mathematician's comments on the #243 note led to all sixteen problem papers
being rewritten for a first-time reader. The [credit ledger](docs/research-commons/CREDIT_LEDGER.md)
lists each piece of advice and what it changed. Names stay withheld until each
person confirms they want to be named.

<a id="citation-and-prior-work"></a>

## Citation and licence

Use [CITATION.cff](CITATION.cff) and record the commit used. For mathematics, cite the relevant
[problem paper](paper/README.md) and the original sources it uses:
[prior art](docs/PRIOR_ART.md) and [source attributions](docs/research-commons/SOURCE_ATTRIBUTIONS.md)
separate earlier results, formalisation and local use.

Code, scripts and documentation are Apache-2.0; manuscript sources and PDFs are
CC-BY-4.0. [REUSE.toml](REUSE.toml) records exceptions. See also
[scope](docs/SCOPE.md), [privacy](docs/PRIVACY.md) and the
[code of conduct](.github/CODE_OF_CONDUCT.md).
