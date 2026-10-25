# An explicit defect clock and a charge target with scale slack

This is an unbounded necessary condition for a possible finite constrained
Golden row, plus a sufficient counting target. The counting target is still
unproved. Neither the coupled period-two question nor Prize Problem 1 is
settled.

All three modules passed the unchanged official checker at reference commit
`3eca23c0a9fa6b153313655e6d51835406c2d06e`, Lean 4.35.0. Every owned
declaration was replayed through the kernel: **77 declarations in total**.
Sources and reports are identified by
[`quantitative-drift-artifacts.json`](quantitative-drift-artifacts.json).
These are local full checks, not a new Wolfram review or submission.

## The quantitative statement

Let `L` be a finite zero-boundary left row, with last black cell at depth
`m >= 1`. Assume it keeps column `-1` black at every even time. Its free
stream is `s(k) = zrow L (2*k+1) 1`; assume `s` is Golden, so it contains
neither `00` nor `11111`.

The preceding critical-drift result defines `D(s,n)` by adding
`4 - trailing(s,n)` at each zero, and proves

```
5*zeros(s,n) + trailing(s,n) = n + D(s,n),
trailing(s,n) <= 4.
```

The new result makes its growth explicit:

```
D(s, 2*N + m + 16) >= D(s,N) + 1.
```

Define `cutoff(m,0)=0` and
`cutoff(m,k+1)=2*cutoff(m,k)+m+16`. Then

```
cutoff(m,k) + (m+16) = (m+16)*2^k,
D(s, cutoff(m,k)) >= k,
5*zeros(s, cutoff(m,k+5)) > cutoff(m,k+5) + k.
```

Thus the required excess grows by at least one unit per doubling scale,
up to the explicit base factor. This strengthens the earlier assertion
that the excess is merely unbounded; it does not give a positive
asymptotic gap above zero density `1/5`.

The proof uses the kit's `Rule30ZeroBoundary.free_bits_clock`, not a larger
finite enumeration. A constant-defect interval forces period five on its
interior. Taking its length to be `N+m+10` violates Jen's clock. Iterating
that observation gives the displayed exponential cutoffs.

The formal statements are in
[`Rule30GoldenQuantitativeDriftResearch.lean`](Rule30GoldenQuantitativeDriftResearch.lean):
`period_five_of_defect_plateau`, `defect_increase_by_clock`,
`cutoff_exponential`, `defects_at_cutoff` and
`excess_at_exponential_cutoff`. Full replay accepted 51 owned declarations;
see [`golden-quantitative-drift-evidence/report.json`](golden-quantitative-drift-evidence/report.json).

## A relaxed counting target

For the actual coupled free stream of a right half `R`, consider the
following target. **For each base `m`, choose its own finite constants
`C_m, B_m`**, so that for every `k`, with `n=cutoff(m,k)`,

```
5*zeros(free(R),n)
  <= n + B_m + C_m*blackCount(Psi(R),2*n+1) + floor(k/2).
```

The slack grows by half a unit per doubling scale. If `Psi(R)` were finite,
choose `m` to be its last black depth. Its black count is then bounded,
while the defect clock forces at least a whole unit per scale. Taking
`k=2*(B_m+C_m*(m+1)+5)` gives a contradiction.

[`Rule30GoldenScaleChargeResearch.lean`](Rule30GoldenScaleChargeResearch.lean)
proves that these scale charges, for every finite right half, imply `CQ01`.
It also proves that the previous pointwise critical charge implies this
target. The quantifiers are `forall m, exists C B, forall k`; using shared
constants for every `m` would recover a pointwise bound by setting `k=1`
and would lose the intended relaxation.

This module passed all 9 owned declarations and its three headlines;
see [`golden-scale-charge-evidence/report.json`](golden-scale-charge-evidence/report.json).
**Existence of the scale charges is not proved.** It remains the substantive
missing inequality. Proving it would settle the coupled period-two
reduction, which is itself only part of Problem 1.

## An exact simplification for signed reader searches

[`Rule30SignedReaderGaugeResearch.lean`](Rule30SignedReaderGaugeResearch.lean)
proves an algebraic identity used to reduce degeneracy in the discovery LPs.
For a deterministic reader transition `T`, signed transition cost `C`, and
terminal cost `D` with `D(0)=0`, replace

```
C'(p,a) = C(p,a) + D(T(p,a)) - D(p),
D'(p) = 0.
```

Every word has exactly the same energy from initial state zero. The module
checks the integer identity for all words; the same telescoping algebra
underlies the rational synthesis variables. Full replay accepted 17 owned
declarations; see [`signed-reader-gauge-evidence/report.json`](signed-reader-gauge-evidence/report.json).

This preserves the family only when transition costs may be signed.
It does not apply to the nonnegative-cost neural family whose missing
terminal readout was obstructed in the
[preceding report](ORDERED-READER-FOLLOWUP.md). No Rule 30 rank or charge is
claimed by this algebraic simplification.

The ongoing wider-strip and joint-reader searches have not supplied a
useful certificate. Their numerical failures and timeouts do not constitute
impossibility theorems. The new analytic bound gives those searches a target
that permits scale slack, rather than requiring uniformly bounded excess.
