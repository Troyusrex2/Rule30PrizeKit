# Overnight investigation, 2026-10-24

Problem 1 remains open. This branch continues the spatial-column contribution
without changing its reviewed branch or any existing submission. No new prize
essay has been submitted from this investigation.

## New public contributions audited

The public upstream pull requests were checked at these exact heads:

| Contribution | Source head | Independent check |
|---|---|---|
| [AIOvernight, PR 4](https://github.com/WolframInstitute/Rule30PrizeKit/pull/4), original revision: `0^q10111`, every `q ≥ 9`, and 87 words | `f8ebd2facca7ea202be29556fa82bbd462280578` | The unchanged reference checker replayed the certificate's 1,131 constants and the public module's 219 constants. Both passed. |
| PR 4, reviewed revision: general `0^q10111` theorem only | `993cb1b61164a1833788881128437ee9fb943627` | All 132 declarations and the directly stated headline passed full pinned-checker replay. |
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

The fork was checked again at 03:29 UTC. The reviewed PR 4 revision, pushed
at 03:17 UTC, responds to the maintainer's packaging requests and removes the
87 individual words. It supplies the same general family theorem, not a new
unbounded finite-support result. The [new exact-revision audit](reviewed-whitepad-evidence/report.json)
records its source hashes and all 132 declaration checks. The remote pull
reference was fetched directly before checking it; the earlier API listing
still displayed its previous head.

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

## Certified empty-right gate spacings

For `u empty s` in the kit's driven right half, define
`G(r)=u empty (146+r)`. The three new modules `Rule30DrivenPrefixResearch`,
`Rule30Certificates.DrivenEmptyWall` and `Rule30EmptyGateSpacingResearch`
prove at every future cycle that black gate observations have exact successive
spacings three or five. No six-cycle gate window is entirely white.

The packed update is proved equal to `Rule30Ether.drv`, with exact prefix
dependence. A 16-cell wall of 13,937 states contains the actual empty-right
orbit at white cycle 146 (physical time 293, prefix 49415). All 262,144
eighteen-bit cases check wall closure and the required gate windows, including
every value of the two unseen right cells. An induction covers all later
times. The generator is untrusted; its emitted certificate uses ordinary
`decide`, and every proof declaration is replayed by the unchanged checker.

All **351 generated declarations** passed full replay in both the
[working](driven-wall-evidence/catalog/report.json) and
[pinned](driven-wall-evidence/pinned/report.json) environments. The independent
[Wolfram check](wolfram-driven-wall-check.json) confirms all 55,748 wall
transitions, observations, 256 independent vector controls, and the entry time.
The broader `right_prefix_safety.py` search initially found a larger 18,012-state
region forbidding distance two; the emitted wall also forbids distance four,
which yields the sharper 13,937-state certificate.

The eight-column translation applies once to this actual driven gate, but its
transform is provably not spaced. **This does not prove `CQ01Empty`.** An
infinite gate and an infinite reconstructed initial left row are different
assertions; the latter remains open. No prize problem is claimed.

The periodic-free-bit cycle probe is a separate diagnostic. It tested all
words of periods one through twelve with a 20,000-state cap per word; some
period-ten and period-twelve cases reached that cap and remain unknown.
The completed cycles did not refute the proposed variation estimate. Those
ordinary integer calculations are not used as Lean premises.

The follow-up `spaced_density_potential.py` asks whether a nonnegative local
potential could force positive initial black density under the newly certified
gate restrictions. Its finite fits are not proofs. For minimum spacing three,
the radius-four depth-49 fit failed at depth 73. For exact spacings three or
five, the depth-49 fits failed at depths 59 and 52. At training depth 97, the
radius-three LP was infeasible and the radius-four solver returned unknown,
not infeasible. The reports retain those distinctions; no candidate is accepted
and no density or finite-left-support conclusion follows.

## Exact remaining target and anti-diagonal model

`Rule30EmptyGateReductionResearch` proves the unconditional equality

```text
lam (boundary gate) k = zrow (Psi empty) 293 k.
```

Finite support of `Psi empty` therefore implies finite support of this shifted
row. No converse assertion about finite preimages is used. The module defines
the **open** weighted-count estimate `CostEstimate`: fixed natural `C,K` with
`n <= C * sum_{1<=j<=n, shifted(j)=black} j + K` for every `n`.
It proves that this estimate would imply `CQ01Empty`, but **does not prove the
estimate**. All 32 generated declarations passed unchanged-checker replay in
the [working](empty-reduction-evidence/catalog/report.json) and
[pinned](empty-reduction-evidence/pinned/report.json) environments.

`Rule30DiagonalSuffixResearch` separately proves the scalar prefix-xor/OR
anti-diagonal recurrence and both local ribbon constraints used by the search.
For a reconstructed row white beyond width `W`, it proves that every suffix of
fixed width `s` is white once diagonal length `n > W+2*s`. All 32 declarations
passed replay in the [working](diagonal-suffix-evidence/catalog/report.json)
and [pinned](diagonal-suffix-evidence/pinned/report.json) environments. This is
a necessary consequence of finite support, not a decreasing-potential proof.

The [density search index](density-potential-index.json) distinguishes numerical
infeasibility, solver errors, time limits and rejected candidates. Adding global
renewal-clock weights produced finite fits, but six successive fits were
rejected by independently evolved prefixes, through depth 248. Restricting the
descent inequalities to states with white suffixes also produced rejected fits,
through depth 641. No potential is accepted.

`check_abstract_density_potential.py` uses dynamic programming over a fixed set
of ribbon-buffer states. It checks a **bounded** range of widths and can impose
an exact finite legal history at the head. Its synthetic counterexamples need
not be reachable from a gate: they reject only a proof based on that ribbon
overapproximation. They do not refute the desired estimate. An unbounded
transducer certificate would additionally need graph-potential inequalities
covering every transition and endpoint; that proof has not been supplied.

## Refined empty-gate language and all-length synthesis

`Rule30Certificates.DrivenEmptyCore` and `Rule30EmptyGateLanguageResearch`
refine the preceding gate result. From white cycle 155 (physical time 311),
the actual empty-right prefix remains in a closed 740-state wall. Every
eight-bit gate window, with its earliest bit in the least significant position,
belongs to `[8,9,16,18,33,36,66,72,132,144]`. In particular, a gap of three
cannot immediately follow another gap of three. These statements hold at
**all subsequent times**. They do not establish `CQ01Empty` or Problem 1.

All **294 generated declarations** passed full replay with the unchanged
checker in the [working](empty-language-evidence/catalog/report.json) and
[pinned](empty-language-evidence/pinned/report.json) environments. The
[independent Wolfram controls](wolfram-empty-core-check.json) confirm all
2,960 tail transitions, all observations, 256 cellwise update controls, and
the exact first entry at cycle 155 with prefix 38682. The generator report
describes an untrusted computation; verification belongs to the separate
kernel replay reports.

The transducer synthesis scripts replace finite-width training with a finite
set of graph inequalities sufficient for **every word length**. Sources impose
a legal boundary history; edges implement the prefix-xor/OR recurrence;
terminal edges impose the white suffix that finite support would eventually
require. Auxiliary signed vertex potentials telescope along arbitrary paths.
The sought nonnegative ribbon potential would decrease at every cycle, or
only at short or long gate gaps. Neither potential has been found.

`synthesize_transducer_potential.py` tests single steps;
`synthesize_cycle_transducer_potential.py` groups two steps;
`synthesize_controlled_cycle_potential.py` uses longer gate histories from the
740-state automaton. Only the eight-bit language above has been formally
exported from that automaton; larger extracted controllers remain unverified.
`synthesize_position_transducer_potential.py` additionally permits polynomial
weights in the spatial position and polynomial auxiliary graph potentials.
Its coefficient inequalities suffice for all positions, but can be stronger
than necessary. Independent feature-accounting controls compare each scan
with the directly computed whole-word feature difference.

The numerical reports are **not Lean results**. Infeasibility rejects only the
specified abstraction and coefficient class. Two cycle-model reports contain
Farkas combinations checked with exact Python integer arithmetic: auxiliary
terms cancel and nonnegative potential terms have a negative right-hand sum.
These refute the corresponding finite LP systems, not the Rule 30 conjecture.
`synthesize_inversion_potential.py` tests a separate ordered-pair feature class
on finite samples and is not an all-length certificate method.

The subsequent `synthesize_front_transducer_potential.py` uses the exact
outer black edge of a hypothetical finite row. It cuts each diagonal at that
moving front; the cut grows by one per two reconstruction steps, instead of
counting an increasing white suffix. Its endpoint motifs were compared with
2,412 independently evolved cellwise finite-row cases. The distance model
also permits weights in the distances from both ends of the moving word.
Neither model yielded a certificate. Some larger models ended in numerical
errors, recorded separately from infeasibility.

`synthesize_history_transducer_potential.py` retains four or six consecutive
diagonals, enforcing their exact reconstruction equations. Only the oldest
two input bits are free. Its controls check thousands of transitions against
direct complete diagonals and compare whole-word feature differences. The
signed-weight variant seeks an additional graph certificate that bounds its
potential below. These are still **unverified proof models**. The six-row
run timed out; two exact-rational solver runs were stopped by an external
480-second guard after the requested 90-second solver limit did not return
a result promptly. No infeasibility is inferred from these stopped runs.
Run exact-solver experiments behind an external wall-clock guard.

The [search index](transducer-search-index.json) records all these outcomes
and exact report hashes. A separate [finite symbolic probe](gate-language-renormalization-bits48.json)
checks 755 words in the eight-bit gate language: among reconstruction depths
1 through 79, only 1 and 9 have universally black odd entries. The depth-nine
recoding gives twelve eight-bit words and fails to preserve the input
language. This rejects that tested fixed-depth return, not every possible
renormalization or the prize conjecture. The probe has not been Lean verified.

## Paired rows: an all-period target and a verified sparse-family obstruction

`Rule30PairedTraceResearch` investigates a weaker target than arbitrary edge
recovery. `NestedNoncoincidence` says that two finite rows cannot have equal
complete center traces when the outer row's support strictly contains the
inner row's support and the inner support straddles zero. This is **OPEN**.
The module proves that it would exclude every eventual period for every
nonzero finite start, and hence imply the exact official Problem 1. A later
row has both support edges strictly outside those of the earlier row; a
restart puts the center inside both supports.

It also defines the **OPEN** `FlipRanking` hypothesis. A natural-valued
potential need only be nonincreasing while the two center observations agree,
with a drop at a color change. The kit's existing period-one theorem implies
that color changes occur infinitely often. Thus such a potential would imply
the noncoincidence statement and the full prize statement. No such potential
is constructed.

Two unbounded limitations are proved, rather than inferred from samples.
The inner row is black at `-1,0,1`; the outer row adds black cells at
`-(H+3),H+3`. Both are finite and strictly nested, have at most three and five
black cells respectively, and their center observations agree at every time
`t <= H`, for **every H**. Therefore no separation horizon depending only on
the initial black counts can work. More strongly, every `FlipRanking` must
have unbounded initial values on this sparse family: a uniform initial bound
would bound all color changes of the inner row, contradicting the period-one
theorem. This does not prohibit potentials that depend on distance, width,
or other unbounded positional information. No novelty claim is made for the
causality construction.

All **99 generated declarations**, including seven headlines and the sparse
rank obstruction, passed full replay in the
[working](paired-trace-evidence/catalog/report.json) and
[pinned](paired-trace-evidence/pinned/report.json) environments. The earlier
14-declaration edge-reduction dependency was also replayed in each. An initial
pinned build found that dependency absent from this isolated audit worktree;
the runner now copies its exact source with module/export wrappers removed,
refuses to overwrite different source, and checks it explicitly. The
[independent Wolfram samples](wolfram-paired-trace-check.json) use the built-in
Rule 30 automaton at eight horizons through 1,024 and confirm five/three
initial black counts and matching prefixes. The all-horizons results belong
to the Lean proof.

`pair_containment_potential.py` tests a global route to this target. It scans
arbitrary-length words over the four pair states, checks the strict nesting
language and the current/next center agreement, and applies the exact product
Rule 30 update. The row potential counts local patterns separately on each
side of zero and weights them by distance. Affine or quadratic auxiliary
vertex polynomials give sufficient inequalities for all spatial positions.
Variants charge every step, every color change, or only white-to-black
changes. Signed-weight variants seek a second graph certificate that bounds
the potential below along surviving pairs. That pathwise lower bound suffices
for an infinite-trace contradiction; it is not automatically a natural-valued
`FlipRanking` on every finite-prefix transition.

All twelve tested systems were numerically infeasible, at local window sizes
one through three. Each passed independent scalar updates and exact whole-row
feature accounting on 128 nested pairs. Infeasibility rejects these particular
sufficient graph-certificate systems; it does not refute the open target,
every distance-sensitive potential, or a certificate with a different form.
The solver outcomes have **not** been Lean verified. The use of finite
de Bruijn graphs for additive-energy inequalities is standard; see
[Taati, Section 3.2](https://siamak.isoperimetric.info/articles/handbook09.pdf).
No general conservation-law theorem from that survey is assumed in the Lean
proof or used to infer a result about Rule 30 here.

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
python research/overnight/verify_driven_wall.py --project /path/to/pinned-kit --lake /path/to/lake
python research/overnight/verify_driven_wall.py --lake /path/to/lake
python research/overnight/verify_driven_wall.py --project /path/to/pinned-kit --lake /path/to/lake --language-core
python research/overnight/verify_driven_wall.py --lake /path/to/lake --language-core
python research/overnight/verify_empty_reduction.py --project /path/to/pinned-kit --lake /path/to/lake
python research/overnight/verify_diagonal_suffix.py --project /path/to/pinned-kit --lake /path/to/lake
python research/overnight/verify_paired_trace.py --project /path/to/pinned-kit --lake /path/to/lake
python research/overnight/verify_paired_trace.py --lake /path/to/lake
python research/overnight/pair_containment_potential.py --radius 3 --reward flip --graph-degree 2
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
