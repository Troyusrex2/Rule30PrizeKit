# Finite feedback and uniform spatial period lifting

**Problem 1, Q01 and CQ01 remain open.** The new theorem is a uniform
period-lifting rule for official sideways reconstruction. Its core build and
full kernel replay pass. The numerical searches remain separate finite evidence.

## Proved: arbitrary spatial periods can lift by a factor of two

For any input sequence a, depths D, temporal row t and period p, suppose
`recon a (D+n+p+1) (t+1) = recon a (D+n+1) (t+1)` for every n, and a cell
in that period is white. Then, for all n >= 3p,

```
recon a (D+n+2p) t = recon a (D+n) t.
```

Encode two consecutive cells as one of four states. The driven transition
is `(a,b) -> (b, u XOR (b OR a))`. Its transformation monoid has 41 maps.
The 37 maps arising from words containing zero form a closed set and obey
`F^5 = F^3`. Kernel checks of these finite tables and induction on arbitrary
word lengths prove the result for every p and D. The white-cell premise
excludes the all-black driver's three-cycle. This is a period bound under
explicit hypotheses, with no density estimate or absorption claim.

The [catalog source](work/Rule30SpatialPeriodLifting.lean) is public in
[upstream PR 24](https://github.com/WolframInstitute/Rule30PrizeKit/pull/24),
head `3e7da6c362c8cad498bdb595854022b19b826462`, with exactly one module,
one public import and one catalog row. It is open and has no review decision
or GitHub checks in the saved readback. No Wolfram submission was made for it.

## Finite searches: actual right halves

All 16,777,216 right halves supported within positions 1..24 were evolved
through physical time 128. The detector checked the official width-six
ether prefix followed by the thirteen-cell wall. It found 418,403 entries,
yielding 954 distinct normalized complete eventual drivers. Every new
driver class was checked against additional physical evolution and its
full temporal-state reconstruction followed to an exact closed spatial
cycle. Minimum computed density was 2/7; none was below 1/4, the threshold
needed to refute the coefficient-three critical-charge candidate by this route.

This proves neither C3 nor absence of counterexamples. Starts wider than
24, later entries, other trap widths and nontrapped/aperiodic responses
remain uncontrolled. The trap and cycle bridges for these new records are
computational certificates, not new Lean theorems. The separately archived
W1 all-time proof is unchanged.

An initial random backward walk produced no valid histories. A bounded
branching search also lost every branch; its beam truncation makes that
inconclusive. Keeping independently verified known histories produced
2,048 actual starts but only three driver classes, exposing the search's
poor diversity. These negative results are retained, not counted as proofs.

## A shortcut that failed

The sampled spatial periods 7,14,28 do not justify a universal bound of 28.
An arbitrary eventually alternating driver produced a complete state cycle
of period 56. A shortened counterexample has a 76-bit prefix and an
independent scalar reconstruction check covering 166,140 cells. See
[the certificate](work/period28-counterexample.json). It is not asserted to
be realizable by a finite right half. This failure motivated the factor-two
lifting theorem, which allows further doublings instead of forbidding them.

## Validation and public audit

The two research modules replay 61+34=95 owned declarations, including
generated declarations. Their combined catalog version replays the same
95 declarations, not another 95 new results. Cold core-only catalog build
took 30.0 seconds including dependencies; build plus full replay took 34.1
seconds with peak owned RSS 1.74 GiB. The unchanged official checker at
kit `3eca23c0a9fa6b153313655e6d51835406c2d06e` passes all headlines with no
new axioms. Final research build logs are empty; the checker emits only
its existing replay-deprecation warning. Three initial compilation attempts
failed on tactic/arithmetic details and were repaired before publication;
their logs are retained. All eleven final guarded jobs exit normally.

The new external submission `R30-20261025-01554c` became Lean Verified,
with 735 declarations replayed by the official verifier. A focused source
audit confirms its fifth-diagonal and linear black-run statements and the
extra premises on its white-row bound. It is not imported or locally
replayed here, and supplies no full source-tail control for this work.

Upstream also incorporated our earlier stripe-tail completion in
[`0090056`](https://github.com/WolframInstitute/Rule30PrizeKit/commit/0090056412733accaa27643d3cbbf982104f2251),
credited to Troyusrex2 and committed by a Wolfram maintainer. It closes PR16;
GitHub reports that PR closed rather than merged. The verifier image remains
at 3eca, so this newer upstream module is not silently used in our proof.

All 352 selected hashes from eight prior archives remain unchanged. No
actual computer settings, external agents' files, verifier sources or checker
were changed. GitHub publication is authorized; no new prize essay/API
submission or message to other people was sent.

## Next unresolved step

The finite trap census has reached diminishing returns. A proof must
constrain arbitrary right feedback or the full unbounded source remainder.
The lifting theorem gives a correct framework for analyzing density under
successive spatial period doublings, but neither density nor realizability
follows from it. Fixed C3 and variable-coefficient charge routes remain open.
