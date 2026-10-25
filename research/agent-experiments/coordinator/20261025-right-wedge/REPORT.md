# Common-gauge rigidity in the canonical right exterior

Problem 1, Q01, CQ01 and the canonical left-edge observer remain open.
The new proved result is proposed for the kit in
[PR28](https://github.com/WolframInstitute/Rule30PrizeKit/pull/28), head
24fe825edf60abbad7d7373bfbfca0af68cf0f31. The PR is open, not merged;
there has been no prize API submission for this result.

## The new uniform theorem

Let U>V>=0, A(t,p)=cell(U+t,p), B(t,p)=cell(V+t,p), delta=A XOR B.
Let h be an auxiliary field satisfying the divided-difference update D and
common-gauge constraint W from the previous briefs for all time. If h(0)
is initially supported inside delta(0), then for EVERY time t and integer
p>V+t,

    h(t,p) = h(0,U) AND cell(U+t,p).

Thus the entire exterior beyond the younger right front has one phase.
The field h is never assumed to be a physical Rule30 history. The result
does not cover the overlapping region containing the center and left edge.

The stronger finite-horizon version only needs an initial upper support
bound at U and W through N, where

    t + floor(max(U+t-p,0)/2) <= N.

There is no age-independent fixed horizon in this statement. This is
consistent with the previous all-horizons obstruction to finite lifting.

The supporting zero-background theorem classifies every initially subset
common mode on the sheared half-line as zero or the actual background,
with no finiteness or periodicity premise. An asymmetric gap induction
works because its right endpoint is black in the actual background. The
argument adapts the existing catalog's `Rule30XorRigidity` gap method;
it changes the auxiliary recurrence rather than assuming h is physical.
Applying it in the exact moving region where B is white proves the canonical
corollary. No claim of literature novelty for the underlying gap method is made.

## Verification

Both research sources pass complete unchanged official kernel replay at
0090056412733accaa27643d3cbbf982104f2251: 46 and 49 declarations respectively,
including generated proof declarations, with no new axioms. The 307-line
core-only catalog port combines the SAME mathematics into one module:
all 95 declarations and four headlines pass. These copies are not additional
mathematical discoveries. Catalog build plus check took 6.72 seconds with
833 MB peak owned-tree RSS. The source, catalog import and README row are
the only three files in PR28.

Independent controls exhaust 87,380 initial pairs, verify 128,584 finite
distance implications and 1,012 subset classifications, and compare 2,708
scalar timesteps. Dropping the black-right-endpoint premise or shortening
the required time horizon gives concrete failing controls. All pass as
expected. No finite computation is used as a Lean proof premise.

## What did not extend

An exhaustive local test finds only three one-cell physical factor maps
from unrestricted (A,B,h) under the one-step W constraints: zero, A and B.
None reads h. A five-site, two-layer test also refutes the corresponding
LOCAL subset-propagation implication. These are finite checks, not an
all-width or all-time classification.

Adding the new necessary exterior coherence to the exact finite lifting
test still leaves failures. Across 276 pairs U<=24 all sampled spaces lift
by horizon U, but the first required horizon reaches 11. For U=3,V=2 the
left-edge field initially black only at -3 still fails the restricted lift
through N=2; it clears at N=3. No all-time lifting theorem is refuted by this.

A stronger finite family was tested at H=0..6: e=2H+6, U=2^e,
V=U-(2H+3), and h=delta XOR the separated right pulse. It retains the
canonical left edge and exterior phase zero through H, satisfies D and W
through H, yet has no previous subset lift. The right-boundary inverse is
forced black at V-1, where previous delta is white. This family has NOT
been proved uniformly in Lean. Crucially, its center observations are
recorded and generally nonzero. It is not a zero-center all-time observer
counterexample; do not silently add that missing condition.

## A new conjecture to attack, not a theorem

In the frame of the older right edge, represent A and B by binary rows a,b.
Canonical a is odd and its bits 1 and 2 are equal. Canonical b is even
because its right front lies strictly to the left. Search suggests:

    If a is odd with bit1(a)=bit2(a), b is even, and h satisfies D and W
    for all time, no nonzero h can remain confined to any fixed finite
    band of right-edge depths.

This is deliberately stronger than the exact canonical-ancestry version.
It remains UNPROVED. Both backgrounds evolve by Phi; a and b may otherwise
have arbitrary finite prefixes. The most permissive experiment does not
even require initial subset support. All 43,688 parameterized background
cases at widths 2..8 reject every band mode. The subset-restricted search
uses the same cases; the 22,098 cases restricting b's low class are included,
not an additional disjoint dataset. No cutoff is extrapolated to all widths.

For exact canonical prefixes, the separate band search covers widths 1..13,
all reachable right-diagonal phases and all age gaps. Gaps larger than the
band are represented by the identical white younger prefix, with all older
phases retained. The 4,610 parameterized cases have no surviving nonzero
mode; the latest finite rejection is at step 17. Independent physical set
evolution rejects 832 small modes at 114 cases. A known NONCANONICAL pair
does have a permanent two-cell escaping difference: starts {-1,0} and {-1}.
The scalar control detects it for 65 timesteps, and the earlier finite XOR
rectangle proof already verifies the underlying all-time mechanism. The
search is therefore able to retain an escaping mode when one exists.

Even a proof of this bounded-band conjecture would not alone solve P1:
a canonical field can spread to unbounded right-edge depth, and the center
is a moving depth rather than a fixed band. The next argument must connect
growth or all-time compatibility to that moving observation.

## Publication and reproduction

PR28 was created through the authenticated GitHub CLI after the connector
returned a 403 integration-permission error. Connector readback confirms
the exact head, body and three-file scope. No new essay was submitted. The
prior 207-declaration product-parity notebook is still awaiting its large
fresh-process validation; a small canary does not stand in for that.

Run `python -B verify_artifacts.py` to audit archived bytes and proof scope.
Copy work to scratch before executing. Adapt the recorded Windows paths
while retaining the pin and unchanged checker. Run the two research modules
in dependency order with `guard.py replay.py <module>`. `prepare_catalog.py`
and `check_catalog.py` document the core-only port. The experiments are
separate from all proof premises. The usual 300-second, 8-GiB owned-RSS and
2-GiB system-free guards were unchanged.
