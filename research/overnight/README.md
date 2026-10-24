# Overnight investigation, 2026-10-24

Problem 1 remains open. This branch continues the spatial-column contribution
without changing its reviewed branch or any existing submission. No new prize
essay has been submitted from this investigation.

## New public contributions audited

The public upstream pull requests were checked at these exact heads:

| Contribution | Source head | Independent check |
|---|---|---|
| [AIOvernight, PR 4](https://github.com/WolframInstitute/Rule30PrizeKit/pull/4): `0^q10111`, every `q â‰¥ 9`, and 87 words | `f8ebd2facca7ea202be29556fa82bbd462280578` | The unchanged reference checker replayed the certificate's 1,131 constants and the public module's 219 constants. Both passed. |
| [AIOvernight, PR 5](https://github.com/WolframInstitute/Rule30PrizeKit/pull/5): 56 even black observations force 17 initial black cells | `8f6a97973c59b5a45ed676794cbcd3adb467e96a` | Independent full replay passed: 1,236 data declarations and 346 public declarations. No official private status inferred. |

The first result is an unbounded word-family exclusion. The second is a finite
quantitative bound, with an unrestricted initial tail. Its reviewer requests a
bound growing without limit, which would address the missing finite-support
argument. Its closed PR is not evidence that the mathematics is false.

[The audit report](contribution-audit/report.json) records exact source hashes,
every declaration replay, and the unchanged kit commit
`cc1e0e0e7c1ae8c971aec5c14aaabb47c7b8c554`. Only module/export wrappers were
removed to match that reference kit. These are independent local kernel checks;
we did not access another submitter's private prize status or infer official
verification from a PR description.

The sparse proof was also compiled and replayed under diagnostic module names
without native C generation: [full diagnostic record](contribution-audit/sparse-noC-verification.json).
That run preserved every mathematical proof body, changed only the module/export
wrappers and the public module's data import, and replayed all 1,582 declarations.
The ordinary library build was deliberately interrupted as redundant after this
pass; we do not claim that its C-artifact build completed. The audit runner's
`--no-native-c` option reproduces direct olean compilation under the original
module names, then invokes the same unchanged kernel checker. C artifacts are
unnecessary for this proof replay.
The [original-module-name run](contribution-audit/report-no-native-c.json) also
passed both complete replays, with exact upstream and adapted source hashes.

## An unbounded identity with an exact iteration obstruction

A separate public lead was
[morpholib's Theorem 14](https://github.com/fractastical/morpholib/blob/777865115483d310f72f0b9511b45409e330a8f5/docs/RULE30_PRIZE_SUBMISSION.md),
which describes an eight-column reconstruction identity. Its linked
`MathOfBiology.lean` contains local Boolean identities; it does not state the
advertised universal elimination of period two. We did not use that elimination
as a premise.

We formalized the one-step identity directly against the kit's `recon` and
checked what is required to repeat it. Write

```text
b_G(2r)   = !G(r)
b_G(2r+1) = 1
D G(r)   = G(r+2) xor G(r+4).
```

Say `G` is spaced if no two black cells have distance one or two. The new
core-only module proves:

1. For every depth `m â‰¥ 1` and every time `t`,
   `recon b_G (m+8) t = recon b_(D G) m t`, provided `G` is spaced.
2. If `lam b_G` is white beyond width `W`, then `lam b_(D G)` is white
   beyond `W-8`.
3. Under the same spacing hypothesis,
   **`D G` is spaced if and only if `G(r+4)=0` for every `r`.**
4. The period-five gate `G(r)=[r mod 5=0]` is spaced, its transform is not,
   and the formula obtained by applying the translation twice is false:
   the actual reconstructed cell at depth 17, time 0 is white, while the
   twice-transformed depth-one cell is black.

The third item identifies the obstruction to using this particular lemma as
an indefinitely repeatable support descent: an infinite gate loses its required
spacing after the first transform. The fourth also rules out simply dropping
the premise for a second application. Neither statement rules out other
renormalizations, and neither proves or disproves period two for the single seed.

Credit for the one-step identity belongs to the cited morpholib work. The Lean
formalization, support transfer, exact preservation criterion and checked
counterexample here were developed by Troy Lowry with OpenAI Codex. No claim
of literature priority is made.

The unchanged checker replayed all **45 generated constants**, with seven
headlines and standard axioms only, in both environments:
[working catalog](spacing-evidence/catalog/report.json),
[pinned reference](spacing-evidence/pinned/report.json).
The [independent Wolfram check](wolfram-spacing-probe.json) compares 12,800
reconstructed cells and reproduces the counterexample. A successful partial
headline check does not establish any official prize target.

## A checked obstruction to extrapolating the small white-gap table

The stronger spacing-three/five restriction also does not imply a universal
white-gap bound of sixteen. Let `G` be the period-31 gate black at residues
`0,3,6,9,12,15,18,21,26`. Its successive gaps are seven threes followed by
two fives. The kit's scalar reconstructed initial row is white at **every
depth from 528 through 544**.

`Rule30SpacingGapCounterexampleResearch.gate31_gaps` proves the restriction at
every gate index, and `seventeen_white` proves all seventeen cells. The
companion `Rule30PackedReconstructionResearch.packed_sound` proves that the
finite packed computation agrees with the actual `Rule30ZeroBoundary.recon`
inside its cone. It does not assume the numerical computation is sound.
The unchanged checker replayed all 13 packed-engine constants and 15
counterexample-module constants in both the
[working](gap-evidence/catalog/report.json) and
[pinned](gap-evidence/pinned/report.json) environments, with standard axioms
only. Wolfram's separate scalar reconstruction
[confirms the same cells](wolfram-spacing-gap-probe.json).

This explains why a small-depth table cannot supply the missing bound for all
depths. It does not refute a larger uniform bound, does not show this periodic
gate comes from a finite driven right half, and does not refute the prize
conjecture. The cited morpholib work reports its small-depth table; the
counterexample here addresses extrapolating that table to all depths.
`no_uniform_gap_bound_sixteen` states the failed universal bound directly.

## Falsification experiments

These are finite computations, not imported Lean premises:

- `forced_row_identities.py` enumerates all `2^18` choices of free bits and
  reconstructs the first 37 initial cells. Through that depth the only constant
  cell and simple equality/complement identities are the already known small
  ones. Independent ordinary forward evolution checks the reconstruction.
- `coupled_gap_search.py` tests white-gap proposals under the necessary
  no-`00` and no-`11111` free-bit restrictions. Exact forward checks confirm
  eight-cell white gaps, including one starting at depth 24. These restrictions
  alone do not certify realizability by a finite driven right half. Solver
  timeouts are recorded as unknown. The optional spacing-3-or-5 restriction is
  stronger and is not assumed to hold for every right half.
- `driven_spacing_probe.py` checks 128 finite right starts through 16,384
  boundary cycles. Some sampled runs eventually display only spacings three
  and five; others retain spacings two. Thus the samples do not justify a
  universal eventual-spacing claim. Thirty-two scalar cone controls check the
  independent packed evolution.
- `spacing35_row_probe.py` and `reduce_spacing35_witness.py` generate periodic
  spacing-three/five gates, check their reconstructed initial rows by ordinary
  forward evolution, and find the small gate used in the Lean counterexample.

The next proof must use an invariant with a justified unbounded step. Neither
a larger finite sparse budget, a finite gap table, nor an unpreserved spacing
condition supplies that step.

## A variation/weight route under investigation

Let `variation f n` count changes between consecutive free bits through index
`n`, and let `weight L N` count black initial cells at depths `1..N`.
The research-only module `Rule30VariationWeightResearch` defines the **open**
estimate

```text
there exist fixed natural constants C,K such that, for every f and n,
variation f n <= C * weight (Theta f) (2*n+3) + K.
```

It proves that this estimate would imply `Q01`, and hence exclude eventual
period two. Finite support would bound all prefix weights and therefore all
free-bit variation; bounded variation forces eventual constancy, contradicting
the kit's free-bit nonperiodicity theorem. This does not address every period,
and **the estimate itself is not proved**.

The strict candidate `C=2,K=0` survived an exact enumeration of all `2^24`
free prefixes through depth 49, but failed at depth 61: a prefix has 21 changes
and only 10 black initial cells. The same module now proves
`strict_factor_two_false` directly against `Theta`, using the packed-cone
soundness theorem. All **54 generated constants** passed unchanged-checker
replay in the [working](variation-evidence/catalog/report.json) and
[pinned](variation-evidence/pinned/report.json) environments. The conditional
headlines do not establish `Q01` or the missing estimate.

The beam search found larger finite violations for factor two; they do not
prove that every additive offset fails. A factor-three beam search through
depth 2049 found no counterexample, which is not a universal proof. Longer SAT
queries returned unknown at their time limits. These results are candidate
falsification evidence only.

We also tested local weighted potentials for the anti-diagonal recurrence.
The basic closed ribbon constraint is that the previous diagonal's black bits
force transitions in the next one; a stronger upper constraint was included
as well. Nonnegative local potential searches were infeasible in the tested
class. A signed finite-width LP produced a spurious zero-cost candidate, whose
potential becomes negative on an actually reachable depth-12 ribbon. That
candidate is explicitly rejected in its report. None of these numerical
optimization results is used as a Lean premise.

`reachable_variation_potential.py` tests richer windows on exactly reachable
diagonals, rather than only the earlier abstract ribbon constraints. The tested
nonnegative local potential classes with windows of three and four cells were
numerically infeasible through depths 27 and 29, respectively. Allowing a factor
of two potential increase at black outputs did not produce a candidate either.
These LP results are not kernel-verified impossibility theorems and rule out
neither a nonlocal potential nor the open variation estimate.
Distance-weighted versions, charging black output cells in proportion to their
depth rather than merely their count, were also infeasible in those two tested
classes. These results are recorded separately with the `-positional` suffix.

`psi_marker_probe.py` checked simple candidate black markers of the form
`a*2^n+b` for the empty-right `Psi` row. None survived the depth-65,536 training
window (odd `a` from 1 to 31 and `b` from -32 to 32, at least ten observations).
The independent forward controls and depth-1,048,576 row hash are recorded in
`psi-marker-probe.json`. This rejects only that tested marker family.

The conditional reduction and the exact factor-two refutation are research
checkpoints, separate from the three unconditional modules in
[catalog PR 7](https://github.com/WolframInstitute/Rule30PrizeKit/pull/7).
That PR also includes an evaluated review essay, with all 73 standalone
declarations replayed by LeanLink and zero saved message cells. It has not
been submitted to the prize API.

## Eventual spatial relations

The research-only `Rule30EventualColumnRelationsResearch` uses the update rule
and the existing no-eventually-constant-column theorem. If columns `i` and
`i+2` agree from a time onward, the middle column obeys

```text
b(t+1) = b(t) AND NOT a(t).
```

It becomes constant. Thus in every orbit with a leftmost black cell, those two
columns disagree at arbitrarily late times. Similarly, eventual complementary
values at adjacent columns make the left column monotone and are impossible.
This strengthens complete-trace separation in these specific relations only.
It excludes no new temporal period of one column and makes no assertion about
eventual equality at arbitrary spatial distances. Verification records are in
`eventual-relations-evidence`; the general prize problem remains open.
All nine generated declarations passed the unchanged checker in both the
[working](eventual-relations-evidence/catalog/report.json) and
[pinned](eventual-relations-evidence/pinned/report.json) environments. These
short consequences of the existing monotonicity theorem are research helpers;
no claim of literature priority is made.

## Reproduction

Use Lean 4.35.0 and the kit's unchanged `Check.lean`. Give the audit runner
the pinned worktree; it refuses to overwrite different source files and bounds
only its own child processes.

```text
python research/overnight/audit_contributions.py --project /path/to/pinned-kit --lake /path/to/lake
python research/overnight/audit_contributions.py --project /path/to/pinned-kit --lake /path/to/lake --no-native-c --module-filter Sparse16
python research/overnight/verify_spacing.py --project /path/to/pinned-kit --lake /path/to/lake
python research/overnight/verify_spacing.py --lake /path/to/lake
python research/overnight/verify_gap.py --project /path/to/pinned-kit --lake /path/to/lake
python research/overnight/verify_gap.py --lake /path/to/lake
python research/overnight/verify_variation.py --project /path/to/pinned-kit --lake /path/to/lake
python research/overnight/verify_variation.py --lake /path/to/lake
python research/overnight/verify_eventual_relations.py --project /path/to/pinned-kit --lake /path/to/lake
python research/overnight/verify_eventual_relations.py --lake /path/to/lake
python research/overnight/build_core_sequential.py --lake /path/to/lake
python research/overnight/forced_row_identities.py --free-bits 18
python research/overnight/driven_spacing_probe.py --samples 96 --cycles 16384
```

The audit needs the exact `origin/pr4-whitepad` and `origin/pr5-sparse16` refs
above. The Python verification runners use `psutil`; symbolic experiments use
`z3-solver==5.3.1.0`. In Wolfram, load `spacing-probe.wl` and evaluate
`spacingReport[]`. Raw account responses, local authentication files and
compiled artifacts are not part of this branch.

The first full-catalog cold build hit its per-job memory guard under parallel
compilation. The dependency-ordered runner then passed the complete standalone
core catalog; [the build record](core-build.json) includes the final root and
its source hash. The first sparse
certificate audit also stopped at its resource guard without a pass. A later
exact-source replay without C emission passed as described above. Neither
interrupted ordinary build is recorded as successful verification.
