# The complete Rule90 source bridge and the deep remainder

Troy Lowry and Codex, 25 October 2026. **Prize Problem 1 remains open.**
This closes the formal gap in the preceding
[dyadic-source result](../20261025-dyadic-sources/REPORT.md), rather than
assuming its binary mask is already a Green-function formula.

## A complete, unconditional identity for the actual center

Let R(d,s)=cell(s,s-d), and b(d,s)=R(d,s) AND NOT R(d-1,s) for d>0,
with b(0,s)=1. The preceding core proof links b to the actual black-to-white
run boundary, including the d=0 boundary convention.

Work over GF(2). For any e>=0 put H=2^e, n=2H-1 and m=n-1. Define

```
W(e,s,d) = b(d,s) * [if 2 divides m-d then choose(m-s,(m-d)/2) mod 2 else 0].
```

All subtraction indices below lie in their stated finite ranges. The new
Lean theorem **`center_eq_one_add_deep_sources`** proves, for every e,

```
c(2H-1) = 1 + sum(s=0..2H-2) sum(d=e+1..2H-2) W(e,s,d)  in GF(2).
```

There are no unproved hypotheses. The full center sum, its binomial
weights, the actual source semantics, and the shallow-strip value are now
linked by kernel-checked proofs. The depth cutoff e grows without bound.
This is **not** a theorem that the deep sum vanishes, has an uncancelled
term, or fails to be eventually periodic. At time 7 its value is 1 and
cancels the shallow 1. No prize solution follows.

## Proof chain

1. [SourceSeries](work/Rule30SourceSeriesResearch.lean) defines the actual
   right-edge seed series P_s(X)=sum_d R(d,s) X^d and B_s(X)=sum_d b(d,s)X^d.
   It proves `P_(s+1)=(1+X^2)P_s+X B_s` coefficient by coefficient from the
   official Rule30 diagonal recurrence. The row at time zero is 1.
2. Its `duhamel` theorem unrolls that recurrence for every time, and
   `kernel_coeff` proves the exact binomial coefficient of `(1+X^2)^h`.
   `center_source_sum` evaluates at the actual center coefficient. The
   homogeneous Rule90 contribution is zero at every odd time 2H-1.
3. [LucasMask](work/Rule30LucasMaskResearch.lean) derives the standard
   implication `choose(h,k) odd => k AND h=k` from Mathlib's Lucas theorem.
   This is a standard bridge lemma, not a claimed new number-theory result.
4. [DyadicSourceSum](work/Rule30DyadicSourceSumResearch.lean) applies the
   preceding actual-source mask theorem. `shallow_term_eq` proves that
   for d<=e only (d=0,s=H-1) has weight 1; all other shallow terms are zero.
   `shallow_sum` evaluates the entire shallow sum to 1. Splitting the exact
   full source sum proves the displayed deep-remainder identity.

The new modules contain **59 additional kernel-replayed constants**:
LucasMask 12, SourceSeries 25, DyadicSourceSum 22, including generated
declarations. The unchanged 56-constant source module was freshly rebuilt
and replayed as a dependency. [Proof summary](summary.json) and raw reports
are retained. All selected headlines passed; no new axioms were introduced.
The final source builds are warning-free. The unchanged official checker
prints its existing replay-deprecation warning.

All checks use Lean 4.35.0, verifier commit
3eca23c0a9fa6b153313655e6d51835406c2d06e, and checker SHA256
b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905.
Generic Duhamel, binomial expansion, Lucas' theorem and the known diagonal
periodicity are not claimed as new. The new work is their checked connection
to the uniform seed-source localization and the exact deep remainder.

## A new test of the deeper sources

The first new experiment used complete source-channel sums rather than a
larger shallow strip. For H=1,2,...,4096 restricted to powers of two, define
rho as the least changed right-edge bit of Phi^H(1) versus 1. At depth 2r,
the channel at time 2H-1 is computed by the explicit Lucas samples

```
XOR over u submask of r: b(2r, H-1+r-u),   0<=r<H.
```

Across 797,161 sampled terms, all 13 complete channel sums match the actual
center. The following candidate survived this finite test: positive source
channels below rho vanish pointwise, and when rho is even, channel rho has
parity 1. The five tested even-rho cases were (H,rho)=(4,4),(8,6),(128,16),
(256,24),(4096,34). **This candidate has no uniform Lean proof here.**
Even its truth would not control the total deeper parity: for H=8 the first
interior channel is odd but the final center is 1, whereas for H=4 it is 0.

A tempting odd-rho extension fails exactly. At H=16, rho=7, the next even
depth 8 contributes nothing; the first active positive depth is 14 and the
first odd interior channel is at depth 18. Thus rounding rho up to an even
depth does not give a universal leading odd channel. These are finite
diagnostics, not new impossibility or nonperiodicity theorems.

Independent polynomial controls passed 8,192 local-row identities,
257 complete finite polynomial convolutions, and 11 full shallow/deep
splits at times through 2,047. They use the actual right-edge packing,
not a Rule150 formula relabeled as Rule90.

## Catalog port and public audit

The core source theorem was ported to a separate catalog worktree as
`Ruliology.CellularAutomata.Rule30RunBoundarySources`. Its exact
[source](work/catalog/Rule30RunBoundarySources.lean), core-only Lake build,
and full 56-constant replay are archived. The port changes its namespace
and documentation, preserving the proof body. It uses no Mathlib.
The Mathlib bridge remains in the research modules above. A separate
catalog-PR record will link the upstream pull request after publication;
this archive itself is not a prize essay or API submission.

The 16:10 UTC refresh has **41 public entries**, down from 45. Four IDs
disappeared: R30-20261025-bcf514, R30-20261025-e88630,
R30-20261025-dacb3e and R30-20261025-483a37. No surviving entry changed
and no new entry appeared. We do not infer why they disappeared. None is
a premise of these proofs. The verifier and upstream main remain at 3eca.
The existing conservation PR21 is still open with the same head and no
review decision or GitHub status checks at the latest read.

All seven final jobs terminated normally within the 300-second/8-GiB
owned-RSS/2-GiB-system-free guards. The largest final source job used about
2.16 GiB owned RSS. The source-sum replay took 42.437 seconds. The core
catalog port built and replayed in 9.313 seconds. No other session's files,
processes, actual computer configuration, or sensitive values were touched.
The GPU and G913 were not used. No new prize essay was submitted.

Next: investigate the return-depth mechanism and its unrestricted tail,
trying to prove an unbounded constraint that excludes periodic full-center
behavior. The exact identity above supplies a sound interface for that work;
the identity alone is not the missing growth argument. The goal stays active.
