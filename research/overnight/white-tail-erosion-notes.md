# Ether erosion with a white right tail

Troy Lowry with OpenAI Codex, 2026-10-24.

The new result extends the applicability of Luis Perez Morales and Claude's
[period-three ether erosion proof](https://github.com/WolframInstitute/Rule30PrizeKit/pull/10).
Their front certificate, potential, and good-state argument are used unchanged.
The dependency is pinned to `f6885abec122a9dcbb3160cb69312323bc075dc1`.
It is independently replayed alongside this extension; its authorship remains theirs.

Let `F(t,p)` be a Rule 30 evolution on columns `p >= 1`, with column zero
forced to the period-three ether at attachment `j0` and phase `s`, from time
`T` onward. Suppose `F(T,p)=0` for every `p>W`. For every `k>=1`, some
column in `1..k` differs from the matching ether at a time in

```
[T, T + 3 * max(W + 12 - k, 0) + 6].
```

There is no spatial-width, temporal-clock, transient, or initial-word bound.
An initially matching prefix is allowed but is not required: an existing
departure already supplies the witness. Moreover, column one differs from
the matching ether at arbitrarily late times (`white_tail_often_departs`).
This last statement follows by restarting at any later time, with the
support bound enlarged by the elapsed time.

This is **not an exclusion of a period-three center column**. Departing from
one matching ether profile does not exclude every periodic profile, and the
open constrained-left-half reductions are not resolved. The theorem also
does not prove erosion for every arbitrary infinite right side.

## What changes in the argument

The earlier `erosion3_fin` assumes a finite perturbation of the ether and
uses its rightmost defect. A white tail differs from the ether arbitrarily
far to the right, so it has no rightmost defect. That hypothesis cannot be
applied directly.

The generalized `erosion_bounded` instead assumes that at every time
`t>=T` there is **some** defect at a position at most `R+(t-T)`. The first
defect is bounded by that witness. In the earlier proof's sole bad state,
each consecutive bad-state step moves the front right by at least eight,
so it cannot remain bad against an upper bound moving right by one. Once
good, the existing potential forces the front left. The same arithmetic
gives a deadline `T + 3 * max(R-k,0) + 6`.

For a white tail, Rule 30 locality keeps all cells beyond `W+(t-T)` white.
Every spatial period of twelve ether cells contains a black cell, providing
a defect within twelve cells beyond that bound. Thus `R=W+12` supplies the
general theorem's premise. The constant twelve is convenient, not claimed
optimal. No new finite family of eventual center words is being excluded.

## Verification and reproduction

The [Lean source](Rule30WhiteTailErosionResearch.lean) passes the unchanged
official checker against both `2f63afda261888e04ec57237290e723190914a1d`
(current reference) and `cc1e0e0e7c1ae8c971aec5c14aaabb47c7b8c554`
(historical pinned reference). In each environment:

- all 48 extension declarations and eight selected headlines pass full kernel replay;
- all 131 dependency declarations and seven selected headlines pass separately;
- the extension source is unchanged; the dependency adaptation removes only
  module/export wrappers, preserving its proof bodies;
- the checker and official problem statements are unchanged; no new axioms
  or native decision procedure are used.

The complete reports are in
[`white-tail-erosion-evidence`](white-tail-erosion-evidence).
With the pinned dependency commit available in the repository:

```powershell
python research/overnight/verify_white_tail_erosion.py --lake PATH_TO_LAKE --project REFERENCE_CHECKOUT
python research/overnight/white_tail_erosion_controls.py
```

The independent finite controls pass 1,440 packed right-half cases across
all twelve attachments and all three phases. Twelve selected cases also
pass 25,061 cellwise comparisons using an independent scalar implementation.
These computations check the harness and examples, not the unbounded theorem.
See [the Python report](white-tail-erosion-controls.json).

In Wolfram, load `white-tail-erosion-check.wl` and evaluate
`whiteTailErosionReport[ABSOLUTE_PATH_TO_CONTROL_CASES_JSON]`.
Twelve built-in Rule 30 causal cones match 5,810 scalar cells and all first
departure times; see [the report](wolfram-white-tail-erosion-check.json).
A finite periodic array with sufficient left and right margins isolates each
cone. Comparison stops at the first prefix departure, through which the
physical boundary is still the matching ether. It does not claim that a
free physical boundary follows the imposed driver after that time.

No new prize API submission has been made. This proof is a research module
depending on the unmerged PR 10, not a module already incorporated into the kit.
