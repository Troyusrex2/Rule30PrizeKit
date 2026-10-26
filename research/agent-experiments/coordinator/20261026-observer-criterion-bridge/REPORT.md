# The auxiliary observer route now has an explicit checked target

**The observer criterion and Prize Problem 1 remain open.** This update
states the criterion in Lean, proves its implication to the existing global
observer target, and connects the canonical rigidity results to its exact
definitions. It addresses the maintainer's request on
[PR26](https://github.com/WolframInstitute/Rule30PrizeKit/pull/26#issuecomment-6402447712)
and the dependent request on
[PR28](https://github.com/WolframInstitute/Rule30PrizeKit/pull/28#issuecomment-6422347240).
Both existing PRs were updated; neither is claimed accepted or merged.

## Precisely what remains to prove

For finite actual starting backgrounds a,b and a finite auxiliary start x,
`ObserverCriterion` retains all of these hypotheses:

- x has a black left edge lo and is white below lo;
- both a and b are white below lo;
- initially, every black x cell lies in a XOR b;
- the zero-gauge divided-difference mode satisfies `CommonField` for EVERY
  natural time and every adjacent physical pair.

The proposed conclusion, `ModeObservable a b x`, is that this mode is black
at some time at every fixed physical observation column. It concerns fixed
columns, not the outward-moving edge or arbitrary right-edge depth. The
definition is an open hypothesis; no axiom asserts it. It does not assume
the auxiliary mode is a physical Rule30 evolution, or replace all-time
CommonField by a finite temporal window.

`edgeObservable_of_observerCriterion` proves that this criterion implies
`Rule30TraceEdge.EdgeObservable`. If two finite backgrounds have unequal
left edges, their actual XOR is finite, has the smaller left edge, is
initially supported in their difference, and satisfies the exact mode and
common-field equations. Applying the criterion at column zero contradicts
equal infinite center traces. Reversing the pair handles the other order
of the edges. `problem1_of_observerCriterion` then applies the kit's existing
conditional implication to the exact official Problem1 statement.

The old periodic-background barrier is now linked to the defined target:
`barrier_mode_not_observable` proves that its finite mode has the initial
subset and all-time common-field properties yet fails ModeObservable. Those
backgrounds have no left bound. Thus the counterexample does not satisfy
the background hypotheses of ObserverCriterion. `Front.mode_left_edge`
supplies the complementary preserved-front result under those bounds.

## Exact connection for the canonical results

`Rule30CommonGauge.ObserverConnection` identifies the mode in the criterion
with the D equation used in the canonical exterior and escape theorems.
It also proves an equivalence of the two Common predicates and applies the
exterior coherence theorem directly to this mode. The canonical backgrounds
are the actual single-seed rows of ages U and V; the adapter proves their
restarted evolution equals the original history at age plus time.

This provides a literal connection, rather than treating similarly named
mode equations as interchangeable. Exterior coherence and unbounded depth
escape still leave fixed-column observation to prove.

## Validation and publication

At pinned kit5473ffd075f63c9d626e63b8455805d4831b39ca, the unchanged checker
fully replayed the exact staged bytes:

| Module | Full module constants | Previously present | Final guarded run |
|---|---:|---:|---|
| Rule30DividedDifference |198|185|2.73s,752MiB|
| Rule30CommonGauge |174|164|3.04s,754MiB|
| Official Rule30TraceEdge |14|14|1.63s,748MiB|

The23 added declarations include definitions and generated declarations;
the full module counts are not counts of new theorems. All seven selected
divided-difference headlines and five common-gauge headlines passed, with
no new axioms or native decisions. The official TraceEdge source is exactly
the pinned source and was freshly built and replayed. A private import
overlay copied60 compiled files after checking16 pinned official source
hashes; the reference project was read-only. No full catalog-root build
was run, and no backend or human verification status is claimed.

Cedar independently read the final PR26 source and found no scope defect;
that review did not rerun the kernel. The PR28 replay is the root agent's
validation. All runs retained the300-second/8GiB-owned/2GiB-free guards.
Recorded failures include a missing private import, an ambiguous namespace
opening, an extra rewrite, and a definitional arithmetic elaboration issue.
The final source and reports match exactly.

PR26 head: `5c6c9bc690b87b1995d856d4c71b8a261867a5cc`.
PR28 head: `47984734a7e5811e674af7d16b56ac7a2819d431`, including PR26 as a
dependency. Each contribution adds only its module, root import and catalog
row relative to its prerequisite. Six raw GitHub file readbacks and both PR
metadata readbacks matched. A connector permission error affected only the
description edit; the existing authenticated GitHub CLI completed it.

No new PR or prize essay/API submission accompanies this checkpoint. The
next mathematical task is the stated observer criterion, or a weaker route
to the same fixed-center conclusion, with all remaining hypotheses intact.
