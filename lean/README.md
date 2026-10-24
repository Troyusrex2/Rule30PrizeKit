# Rule 30: the statements and the catalog of partial results

This Lake project (package `rule30prize`, library `Ruliology`) holds the official Lean statements of the Rule 30 Prize problems and a catalog of proved partial results about rule 30, all in the namespace `Ruliology.CellularAutomata`. It is plain Lean 4.35.0, without Mathlib.

**Problem 1 is open.** Everything here is a partial result.

- **The statements:** `Ruliology/CellularAutomata/Rule30Jen.lean` defines `rule`, `cell` and `EventuallyPeriodic`. `Ruliology/CellularAutomata/Rule30Prize.lean` defines `center`, `Problem1` and `Problem2`. The kit's [README](../README.md) quotes them.
- **The catalog:** 54 modules. `Ruliology.lean` imports the 40 `Rule30*` modules; their import closure adds the 13 data modules in `Rule30Certificates/` and `BusyBeaverLifetimes`. Each module's docstring records its claim, method and sources.
- **Axioms:** every theorem uses only `propext`, `Classical.choice` and `Quot.sound`. None uses `sorry` or `native_decide`.
- **Provenance:** the 54 catalog modules come from the Ruliology catalog of 2026-10-15, byte for byte except one docstring sentence in `Rule30ZeroBoundaryWidth52`. `SHA256SUMS` lists their hashes as copied, which the kit's first commit, `c2dab06`, matches (`shasum -a 256 -c SHA256SUMS` in a checkout of it). Since then their comments have dropped catalog numbering and provenance, eight modules changed for Lean 4.35.0, and every file became a module of Lean's module system (`module`, `public import`, `@[expose] public section`, so all definitions stay unfoldable for importers) with deprecated names replaced; `git log lean/` shows each change.
- **Added in the kit:** modules proved after the snapshot, proved during the attempt but left out of the catalog, or contributed by participants in the prize. [Added in the kit](#added-in-the-kit) lists them, with credits.

## Status by period

| Case | Status | Lean (`lean/`, namespace `Ruliology.CellularAutomata.*`) |
|---|---|---|
| Period 1 | **Proved** for every column, and for every nonzero configuration with a leftmost black cell | `Rule30Prize.no_column_eventually_constant`, `center_not_eventually_period_one`, `Rule30FiniteConfigs.no_column_eventually_constant` |
| Small periods | **Proved:** no eventual period P ≤ 4096 with transient ≤ 8192 | `Rule30Window` |
| Any period | **Proved:** T + P ≥ 16359 | `Rule30FactorWindow` |
| Period 2 | Reduced to Q01, a statement about the zero-boundary left half. Q01 is **open** in general. It is proved in Lean for every start of width ≤ 52. | `Rule30PeriodTwo`, `Rule30PeriodTwoCoupled`, `Rule30PeriodTwoSideways`, `Rule30ZeroBoundary*`, `Rule30ZeroBoundaryWidth52`, `Rule30PeriodTwoWidth5/6` |
| Least period 3 | Reduced. 001 needs one of AbsorptionT t001, Q001 or C3s001. 011 needs C3w(011). All four are **open**. | `Rule30EtherThree*` |
| Least period 4 | Reduced to Absorption, the ether-and-wall trap, which is **open**. The pure ether lies in no trap of width ≤ 20. | `Rule30Ether`, `Rule30PeriodFourSkeleton`, `Rule30EtherTrapWidth20` |
| Longer periods | **Open.** Some words are excluded, for example by long black runs, 30 certified words and every `1 0^q` with `q ≥ 10`. | `Rule30BlackRuns`, `Rule30BlackRunBlocks`, `Rule30StripCertificateTable`, `Rule30WhiteRunEight`, `Rule30WhiteEnd` |

Barriers are also proved:
- Rules 90, 150 and 210 share every structural fact the argument uses, yet their center columns are eventually constant (`Rule30Realization`).
- Local, strip, finite-state, additive and edge-DFA invariants cannot prove Q01 (`Rule30ZeroBoundaryBarriers`).

## Building

You need [elan](https://github.com/leanprover/elan); it installs Lean 4.35.0 from `lean-toolchain`.

`lake build` builds everything, but a cold build runs modules in parallel. The four `Rule30Certificates/ZeroBoundaryWidth52Chunks*` modules take about 20 s and 3 GB each, so a cold parallel build can need about 12.5 GB before the contributed tail modules below. Build these heavy data modules sequentially too.

Building one module at a time is safest; each `lake build` below compiles exactly one module, and peak memory stays under 4 GB.

```sh
cd lean
for m in Rule30Predecessors Rule30PredecessorCounts BusyBeaverLifetimes Rule30Blocks Rule30Jen \
    Rule30Prize Rule30Window Rule30MaskedJen Rule30Diagonals Rule30BlackRuns Rule30BlackRunBlocks \
    Rule30StripCertificates Rule30StripCertificateTable Rule30DrivenLeft Rule30RightPeriods \
    Rule30WhiteSeed Rule30Realization Rule30FactorWindow Rule30PeriodTwo Rule30ZeroBoundary \
    Rule30ZeroBoundaryStripe Rule30ZeroBoundarySmall Rule30ZeroBoundaryBarriers Rule30Ether \
    Rule30PeriodTwoCoupled Rule30PeriodFourSkeleton Rule30ZeroBoundaryLanes \
    Rule30Certificates.ZeroBoundaryWidth52Chunks{0,1,2,3} Rule30ZeroBoundaryWidth52 \
    Rule30ZeroBoundaryStripeFront Rule30Certificates.ZeroBoundaryStripeCycles{0,1,2,3} \
    Rule30ZeroBoundaryStripeFamily Rule30ZeroBoundaryStripeFour Rule30EtherTrap \
    Rule30Certificates.EtherTrap{0,1,2,3,4,5} \
    Rule30EtherTrapWidth20 Rule30PeriodTwoLanguage Rule30PeriodTwoWidth5 Rule30PeriodTwoWidth6 \
    Rule30EtherThree Rule30EtherThreeNoWall Rule30EtherThreeTrap Rule30EtherThreeReach \
    Rule30EtherThreeLeft Rule30EtherThreeSkeleton Rule30WhiteRunEight Rule30PeriodTwoSideways \
    Rule30LightCone Rule30FiniteConfigs Rule30FiniteMaskedJen Rule30Coupled Rule30FiniteBlackRuns Rule30FiniteBlackRunBlocks Rule30FiniteDiagonals Rule30FiniteWhiteRuns \
    Rule30Certificates.WhiteEndChecks Rule30WhiteEnd \
    Rule30WhitePadding \
    Rule30FiniteStrips \
    Rule30WhitePulse \
    Rule30ZeroPredecessor \
    Rule30BackwardTube \
    Rule30WhitePaddingVacuumCriterion \
    Rule30BackwardVacuum \
    Rule30SparsePreimage \
    Rule30Certificates.FiveTailTube \
    Rule30Certificates.SixTailBackward \
    Rule30RestrictedBackwardTube \
    Rule30Certificates.SixTailEndpoints \
    Rule30Certificates.WhitePaddingFamilies \
    Rule30UniformWhitePadding \
    Rule30WordRotation \
    Rule30ShortTail \
    Rule30FiveTailReduction \
    Rule30VacuumExample \
    Rule30WhitePadding10101 \
    Rule30FiveTail \
    Rule30ForbiddenSuffix \
    Rule30SixTailReduction \
    Rule30SixTail \
    Rule30SixTailSharpened \
    Rule30SuffixFamilies; do
  lake build Ruliology.CellularAutomata.$m || break
done
lake build
```

On 2026-10-15 this took 285 s in total on an Apple M3 Max with 48 GB; the four upstream modules added on 2026-10-23 take about 45 s more. The contributed white-padding modules are measured separately below. Every module not listed below built in under 7 s and 1.2 GB.

| Module | Time | Peak memory |
|---|---|---|
| `Rule30Certificates/ZeroBoundaryWidth52Chunks0`–`3` | 22–24 s each | 2.7–2.8 GB each |
| `Rule30StripCertificateTable` | 21 s | 3.9 GB |
| `Rule30BlackRunBlocks` | 20 s | 2.3 GB |
| `Rule30ZeroBoundarySmall` | 19 s | 3.2 GB |
| `Rule30ZeroBoundaryStripe` | 18 s | 1.8 GB |
| `Rule30Certificates/WhiteEndChecks` | 34 s | 0.8 GB |
| `Rule30EtherThreeNoWall` | 9 s | 1.1 GB |
| `Rule30BlackRuns` | 9 s | 2.2 GB |

### Contributed white-padding modules

Measured on Windows x64 with Lean 4.35.0 on 2026-10-24. Core dependencies were
already compiled. Each main module was rebuilt after removing its own `.olean`;
its imported modules were available. Every rebuilt `.olean` was byte-identical
to the artifact already replayed by the kernel. The four data rows record their
first builds after consolidation, including any newly needed imports. Peak
memory is the sum of the owned processes' RSS, sampled every 50 ms.

| Module | Time | Peak memory |
|---|---|---|
| `Rule30BackwardTube` | 2.20 s | 291 MiB |
| `Rule30BackwardVacuum` | 1.86 s | 248 MiB |
| `Rule30Certificates/FiveTailTube` | 147.70 s | 3061 MiB |
| `Rule30Certificates/SixTailBackward` | 84.51 s | 1376 MiB |
| `Rule30Certificates/SixTailEndpoints` | 20.16 s | 656 MiB |
| `Rule30Certificates/WhitePaddingFamilies` | 285.22 s | 2372 MiB |
| `Rule30FiniteStrips` | 1.89 s | 266 MiB |
| `Rule30FiveTail` | 1.55 s | 219 MiB |
| `Rule30FiveTailReduction` | 2.41 s | 420 MiB |
| `Rule30ForbiddenSuffix` | 1.56 s | 248 MiB |
| `Rule30RestrictedBackwardTube` | 2.03 s | 276 MiB |
| `Rule30ShortTail` | 1.64 s | 258 MiB |
| `Rule30SixTail` | 1.56 s | 232 MiB |
| `Rule30SixTailReduction` | 7.12 s | 1222 MiB |
| `Rule30SixTailSharpened` | 1.56 s | 241 MiB |
| `Rule30SparsePreimage` | 1.41 s | 243 MiB |
| `Rule30SuffixFamilies` | 1.52 s | 246 MiB |
| `Rule30UniformWhitePadding` | 1.42 s | 241 MiB |
| `Rule30VacuumExample` | 1.41 s | 237 MiB |
| `Rule30WhitePadding` | 1.58 s | 238 MiB |
| `Rule30WhitePadding10101` | 1.39 s | 216 MiB |
| `Rule30WhitePaddingVacuumCriterion` | 1.66 s | 248 MiB |
| `Rule30WhitePulse` | 2.48 s | 302 MiB |
| `Rule30WordRotation` | 1.62 s | 270 MiB |
| `Rule30ZeroPredecessor` | 1.42 s | 229 MiB |

`lake build Ruliology` passes after these builds. The unchanged partial checker
replays 2,641 declarations across all 25 modules and checks 52 README headlines,
with standard axioms only. The four consolidated data modules replace 144
certificate files; all 21 main modules and their general statements are retained.


To check axioms, compile a file outside this folder from here:

```sh
cat > /tmp/Axioms.lean <<'EOF'
public import Ruliology
#print axioms Ruliology.CellularAutomata.Rule30Prize.center_not_eventually_period_one
EOF
lake env lean /tmp/Axioms.lean
```

## Added in the kit

These modules are not in the 2026-10-15 snapshot of the catalog, and `SHA256SUMS` does not list them. All use only `propext`, `Classical.choice` and `Quot.sound`. To add one, see [Contributing a partial result](../README.md#contributing-a-partial-result).

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30BackwardTube` | 2026-10-23 | Endpoint-conditioned backward strip certificates combine a finite predecessor chain with a stable zero-driven reachable set to exclude every sufficiently long white-padding word. Contributed by Troy Lowry with OpenAI Codex. | `preCheck_sound`, `tail_tube_forces`, `no_padding_of_endpoint_tube` |
| `Rule30FiniteStrips` | 2026-10-23 | Strip certificate soundness for every column of every configuration with a leftmost black cell, using the uniform masked Jen theorem; no initial strip-state assumption. Contributed by Troy Lowry with OpenAI Codex. | `not_eventually_word_strip`, `not_eventually_word_strip_finite` |
| `Rule30FiveTailReduction` | 2026-10-23 | Trimming white ends and rotating periods reduces every tail of at most five bits to the shorter family or eight new black-ended cores. Contributed by Troy Lowry with OpenAI Codex. | `decomposition`, `no_five_tail_of_cores` |
| `Rule30ForbiddenSuffix` | 2026-10-23 | A vacuum-free full-set image of a fixed suffix excludes white-padding families with arbitrary preceding tail words. Width and suffix are parameters. Contributed by Troy Lowry with OpenAI Codex. | `no_padding_of_forbidden_suffix`, `no_padding_of_forbidden_suffix_finite` |
| `Rule30RestrictedBackwardTube` | 2026-10-23 | Backward tube soundness with white-step predecessor checks restricted to the stable forward reachable set. Contributed by Troy Lowry with OpenAI Codex. | `restrictedPreCheck_sound`, `no_padding_of_endpoint_tube` |
| `Rule30ShortTail` | 2026-10-23 | Exclude every tail of at most four bits after at least 49 white phases, using finite strip certificates, trimming, and period rotation; uniform over all leftmost-black starts. Contributed by Troy Lowry with OpenAI Codex. | `no_short_tail_leftFinite`, `no_short_tail_finite` |
| `Rule30SixTail` | 2026-10-23 | Exclude every tail of at most six bits after at least 77 white phases. The sixteen new six-bit cores use backward-vacuum certificate chains; shorter tails use the five-tail theorem. Contributed by Troy Lowry with OpenAI Codex. | `no_six_tail_leftFinite`, `no_six_tail_finite` |
| `Rule30SixTailReduction` | 2026-10-23 | Trimming and rotation reduce every tail of at most six bits to the five-tail family or sixteen new black-ended cores. Contributed by Troy Lowry with OpenAI Codex. | `decomposition`, `no_six_tail_of_cores` |
| `Rule30SparsePreimage` | 2026-10-23 | Sparse predecessor checks with a proved bitmask completeness condition recover full strip predecessor implications. Contributed by Troy Lowry with OpenAI Codex. | `restricted_of_sparse`, `colConst_inter_of_sparse` |
| `Rule30UniformWhitePadding` | 2026-10-23 | The five pumping certificate families hold for every column of every leftmost-black start, using the generic finite-strip soundness theorem. Contributed by Troy Lowry with OpenAI Codex. | `no_paddingA_leftFinite`, `no_paddingE_leftFinite` |
| `Rule30VacuumExample` | 2026-10-23 | Two five-bit tail applications of the generic vacuum-avoidance criterion use width-five strips; the analytic white-pulse bound handles arbitrary padding. Contributed by Troy Lowry with OpenAI Codex. | `no_paddingA`, `no_paddingB` |
| `Rule30WhitePadding` | 2026-10-23 | A stable zero-driven reachable set and finite tail checks give a strip certificate for every sufficiently long white prefix, by pumping rather than enumerating padding lengths. Contributed by Troy Lowry with OpenAI Codex. | `zeros_stable`, `padding_strip`, `no_padding_word` |
| `Rule30WhitePadding10101` | 2026-10-23 | The endpoint-conditioned backward tube excludes the five-bit tail 10101 after sufficiently many white phases, uniformly over all leftmost-black starts. Contributed by Troy Lowry with OpenAI Codex. | `no_padding_10101_leftFinite`, `no_padding_10101_finite` |
| `Rule30WhitePaddingVacuumCriterion` | 2026-10-23 | A stable zero-driven reachable set and a finite vacuum-free pulse image exclude arbitrary-tail white-padding families. The pulse and its length are unrestricted parameters. Contributed by Troy Lowry with OpenAI Codex. | `no_padding_of_vacuum_avoidance`, `no_padding_seed_of_vacuum_avoidance` |
| `Rule30WhitePulse` | 2026-10-23 | A striped block created by a long black run survives an arbitrary short boundary pulse by locality; the resulting analytic estimate supplies the padding thresholds. Contributed by Troy Lowry with OpenAI Codex. | `white_pulse_return`, `white_padding_forces_early_white` |
| `Rule30WordRotation` | 2026-10-23 | Eventual finite-word repetition is invariant under period rotation; trimming white ends gives the core-tail decomposition. Contributed by Troy Lowry with OpenAI Codex. | `eventuallyWord_swap`, `short_decomposition` |
| `Rule30ZeroPredecessor` | 2026-10-23 | The vacuum has a unique predecessor under a white boundary, uniformly in strip width, by induction through the strip. Contributed by Troy Lowry with OpenAI Codex. | `stripStep_zero_predecessor`, `stripStep_zero_iff` |
| `Rule30Certificates/FiveTailTube` | 2026-10-23 | Consolidated ordinary-kernel certificate data for the five-bit 10101 endpoint tube and the remaining five-bit vacuum-avoidance cores. Contributed by Troy Lowry with OpenAI Codex. | `Tube10101.Zmask` |
| `Rule30Certificates/SixTailBackward` | 2026-10-23 | Consolidated backward-vacuum certificate chains for the sixteen new six-bit black-ended cores. Definitions, predecessor checks, and assembly are in one module. Contributed by Troy Lowry with OpenAI Codex. | `C100001.no_padding` |
| `Rule30Certificates/SixTailEndpoints` | 2026-10-23 | Consolidated endpoint-conditioned predecessor certificates for 110001 and 111101, used to sharpen the common six-tail bound. Contributed by Troy Lowry with OpenAI Codex. | `C110001.no_padding` |
| `Rule30Certificates/WhitePaddingFamilies` | 2026-10-23 | Consolidated reachable-set pumping and vacuum-free suffix certificates for the general white-padding families. Contributed by Troy Lowry with OpenAI Codex. | `ForbiddenSuffix.safe011` |
| `Rule30SixTailSharpened` | 2026-10-23 | No column of a configuration with a leftmost black cell eventually repeats `0^r u` when `r >= 74` and `u` has at most six bits. Covers all nonzero finite starts and the single seed. Backward vacuum certificates give bound 77; two endpoint refinements reduce it to 74. Earlier bounds 69 for five bits and 49 for four bits remain. Proof and formalization by OpenAI Codex through `Troyusrex2`. | `no_six_tail_leftFinite`, `no_six_tail_finite`, `no_six_tail_seed` |
| `Rule30BackwardVacuum` | 2026-10-23 | A finite chain of backward predecessor implications, from the empty set to the vacuum along `0^N u`, excludes every eventual `0^r u` with `r >= max(N, 10*length(u)+11, K+9*(length(u)+1))`. It covers every column of every leftmost-black start without requiring a stabilized forward set. Proof and formalization by OpenAI Codex through `Troyusrex2`, using the existing white-pulse reduction. | `no_vacuum_of_backward_certificate`, `no_padding_of_backward_certificate` |
| `Rule30SuffixFamilies` | 2026-10-23 | For every Boolean word `v` of unrestricted length, no column of a configuration with a leftmost black cell eventually repeats `0^r v 011` when `r >= 10*length(v)+41`. Suffixes `001001` and `111001` give `r >= 10*length(v)+71`. The generic `Rule30ForbiddenSuffix` criterion needs only a vacuum-free full-set image of the suffix. These are partial exclusions, not a solution of Problem 1. Proof and formalization by OpenAI Codex through `Troyusrex2`, using the existing white-pulse reduction. | `no_padding_suffix011_leftFinite`, `no_padding_suffix001001_leftFinite`, `no_padding_suffix111001_leftFinite`, `no_padding_suffix011_seed` |
| `Rule30FiveTail` | 2026-10-22 | No column of a configuration with a leftmost black cell eventually repeats `0^r u` when `r >= 69` and `u` has at most five bits; in particular every nonzero finite start and the single seed. The stronger `r >= 49` bound remains for at most four tail bits (`Rule30ShortTail`). Includes an arbitrary-tail white-pulse reduction and finite vacuum/endpoint criteria; certificate existence for every tail is not proved. Proof and formalization by OpenAI Codex, building on the catalog's uniform masked Jen theorem. Large data is in `Rule30Certificates`. | `no_five_tail_leftFinite`, `no_five_tail_finite`, `no_five_tail_seed` |
| `Rule30WhiteRunEight` | 2026-10-17 | The words `0^r 1 1` with `r ≥ 8` are excluded, for every transient: `Rule30BlackRuns.no_white_run_11` needs `r ≥ 10`. Proved on 2026-10-15 by the verifier of the white-run exclusion and left out of the catalog; ported here. | `no_white_run_11_ge8` |
| `Rule30PeriodTwoSideways` | 2026-10-17 | The coupled question `CQ01` in two more forms. It holds iff no configuration with finitely many black cells has center column `1, 0, 1, 0, …` from time 0. Sideways: for every finite right half `R`, one explicit left row `Psi R` (the constrained start whose free bits complement column 1 of the driven right half) has infinitely many black cells; this holds for `R` whenever it holds for the right half two steps later, or whenever column 1 of the driven right half is eventually periodic at the white steps. Exact death: a left row keeps the center alternating exactly until the first depth where it differs from `Psi R`. States the `R = ∅` milestone `CQ01Empty` (**open**). Barrier: from finite configurations the center alternates arbitrarily long, so no ranking through a finite abstraction of configurations decreases at every double step over which the center flips twice. | `CQ01_iff_no_finite_alternating`, `Q01_no_leftfinite_alternating`, `CQ01_iff_Psi`, `not_finSupp_Psi_of_R2`, `exact_death_center`, `truncation_death`, `CQ01Empty_iff`, `no_finite_abstract_ranking_coupled` |
| `Rule30FiniteConfigs` | 2026-10-17 | The single-seed theorems in their uniform form. For every configuration with a leftmost black cell (nonzero and left-finite): Jen's theorem (at most one column is eventually periodic) and period 1 (no column is eventually constant); the proofs use the seed only through its left edge. For nonzero finite configurations: `CQ01` holds iff none has an eventually 2-periodic center column, whatever the transient, so `CQ01` is exactly FinConf at period 2 for one column. `Q01` gives the same for every configuration with a leftmost black cell. | `jen`, `no_column_eventually_constant`, `jen_finite`, `no_column_eventually_constant_finite`, `CQ01_iff_no_finite_period_two`, `no_leftFinite_period_two_of_Q01` |
| `Rule30FiniteMaskedJen` | 2026-10-17 | The masked and window forms of Jen's theorem (`Rule30MaskedJen`) for every configuration with a leftmost black cell: if column `i` is eventually periodic, column `i + 1` is not periodic with the same period on the white times of column `i`, and `column i ∨ column (i + 1)` is not eventually periodic; with no periodicity assumed, two times never carry the same (column, or-column) window reaching the left edge; a periodic column has, in every window `[n, n + m)` with `n` past the transient and `m = n + i - lo`, a white time where the next column breaks the period. | `masked_jen`, `orCol_not_eventuallyPeriodic`, `window_jen_col`, `periodic_window` |
| `Rule30FiniteBlackRuns` | 2026-10-17 | The black-run exclusions of `Rule30BlackRuns`, for every configuration with a leftmost black cell and every column `i`. The nine-black shield holds in the evolution of every configuration; the exclusions then use the seed only through Jen's theorem and its masked form. If from some time on every black run of column `i` that is followed by white has length at least `9`, column `i` is not eventually periodic. If column `i` has period `P`, no period contains a black run of length `r` with `9 ⌈(P - r + 9) / 2⌉ ≤ r` (Theorem B), or a black run of length `≥ 9` followed by a long white run (Theorem D). The same for every nonzero finite configuration. | `nine_black`, `black_shield`, `not_eventuallyPeriodic_of_long_one_runs`, `no_long_black_run`, `no_black_white_run`, `not_eventuallyPeriodic_of_long_one_runs_finite` |
| `Rule30FiniteBlackRunBlocks` | 2026-10-17 | Theorem B′ of `Rule30BlackRunBlocks`, for every configuration with a leftmost black cell and every column `i`. If the finite check `Determined u j0` holds, column `i` is not eventually periodic with repeating word `1^r u` for any `r ≥ max 9 (9 j0)`, whatever the transient. The proof uses the seed only through Jen's theorem; the nine-black shield and the trace of the next column hold in every evolution. The kernel-checked blocks of `Rule30BlackRunBlocks` (`det_0`, …, `det_0110`) apply unchanged, for example `1^r 0` with `r ≥ 18`. The same for every nonzero finite configuration. | `no_black_run_block`, `no_period_black_run_then_white`, `no_black_run_block_finite`, `traceCol1_rowAt` |
| `Rule30FiniteDiagonals` | 2026-10-17 | The periodic diagonals of `Rule30Diagonals`, for every configuration with an edge. If `x` is white right of `hi`, the diagonal `t ↦ evol x t (hi + t - j)` is periodic from time 0 with period dividing `2^j`. If `x` is white left of `lo`, the diagonal `t ↦ evol x t (lo - t + j)` is eventually periodic with period `2^j`. Every column reads its array of diagonals along a line of slope one, as the center column of the seed does. So the periodic right diagonals behind the 2-adic odometer are not special to the seed. The bitwise form, for every starting value of `Φ(x) = x ⊕ (2x ∨ 4x)`, is `Rule30Equivalents.TFunction`. | `Rd_periodic`, `Ld_periodic`, `evol_eq_Rd`, `column_reads_periodic_rows` |
| `Rule30FiniteWhiteRuns` | 2026-10-17 | The exclusion of `Rule30WhiteRunEight` for every column of every nonzero finite configuration: no column is eventually `0^r 1 1` repeated, `r ≥ 8`, whatever the transient. The lemmas of `Rule30BlackRuns` (the first black cell right of the column moves left during a white run, and the period-start classes) hold for column `0` of any evolution; the seed's right edge becomes any black cell right of the column, which every nonzero finite configuration has from some time on; translation gives every column. | `no_white_run_11_col0`, `no_white_run_11_finite`, `evol_right_edge`, `exists_rightmost` |
| `Rule30Coupled` | 2026-10-17 | Every period, as coupled questions. In any configuration the two halves evolve as the halves driven by the center column, and the center is updated from its two driven neighbours; conversely, two driven halves glued to a column satisfying that update give a configuration with that center. `CQ ω` (**open** for every nonconstant periodic `ω`): no finite left half and finite right half are coupled to `ω`; it holds iff no finite configuration has center column `ω`. FinConf for one column is exactly the family `CQ ω` over all periodic `ω` with a black cell, and the family implies Problem 1. For the alternating column, `CQ` is `CQ01`. | `left_eq_L`, `right_eq_drv`, `evol_glue`, `CQ_iff_no_finite_config`, `CQ_altCol_iff_CQ01`, `finConf_center_iff`, `problem1_of_CQ` |
| `Rule30LightCone` | 2026-10-17 | The locality behind space-efficient evaluation. A cell at time `t` depends only on the initial cells within distance `t`. With space blocks and time steps of width `b`, each block is a fixed function of the three blocks around it one time step earlier, so the center cell at time `m b` is the root of a fan-in-3 tree of `b`-bit blocks with height `m`. This is the shape that Williams's square-root-space simulation passes to Cook–Mertz tree evaluation, about `√n · log n` bits for the center cell at time `n`; neither algorithm is formalized. | `evol_window`, `block_step`, `center_eq_root` |
| `Rule30ZeroBoundaryStripeFour` | 2026-10-23 | Stripe prefixes with four tail cells. For every `m` and every tail `v` of four cells, the start `S[1..m] · v · 0^∞` first deviates from the stripe at some depth `d ≤ m + 6`, and depth `1` turns white at an even time `≤ d - 1 + 31`. Every class `(m mod 2, v)` is covered except `v = 13` with `m` odd. This carries `Rule30ZeroBoundaryStripeFamily` from tails of length at most 3 to length 4, by the same route: one kernel-checked periodic front-window orbit per class, from `Rule30Certificates/ZeroBoundaryStripeCycles0`–`3` (namespace `Rule30ZeroBoundaryStripeFront.StripeCycles3` for the new data module). Contributed by Ying Yin with Codex (GPT-6) as Rule 30 Prize submission `R30-20261020-81df0e`, and ported to core Lean. | `stripe_four_tail`, `family4_of_class` |
| `Rule30WhiteEnd` | 2026-10-23 | The white end. For every `q ≥ 10`, no column of rule 30 is eventually the repeating word `1 0^q`, whatever the transient: for the single seed, `EventuallyWord (true :: List.replicate q false)` is false, and the same holds for every column of every configuration with a leftmost black cell, every finite nonzero one included. `Rule30StripCertificateTable` excludes only `q = 10, 11, 12`. A one-sided strip relaxation (eight cells right of the column, an arbitrary cell beyond) determines column `c + 1` after three periods; kernel checks cover `q = 10 … 25`, and the relaxation's white step satisfies `W^26 = W^22` on the sets that occur, which covers every `q ≥ 26`. Two adjacent columns periodic for ever then contradict Jen's theorem with a clock. The checks are in `Rule30Certificates/WhiteEndChecks`, where `control_q9` shows that the check fails at `q = 9`. Contributed by Gareth Herbert with Claude and GPT as Rule 30 Prize submission `R30-20261022-c27323`, and ported to core Lean. | `not_eventuallyWord_white_end`, `white_end_seed`, `white_end`, `white_end_finite` |
| `Rule30Problem3` | 2026-10-24 | Prize Problem 3 on a one-tape Turing machine that reads the binary digits of `n`: the prize's formal statement (no machine computes `c(n)` in time `O(n)`), the verbal one (none in time `o(n)`) and the version that does not depend on the model (none in time `n^o(1)`), each implying the next. | `Problem3`, `Problem3Verbal`, `Problem3Robust`, `problem3Verbal_of_problem3`, `problem3Robust_of_problem3Verbal` |

## Which modules predate the attempt

The birth times of the catalog files (`stat -f %B`) and the docstrings agree. The *Added* column of the tables below uses these labels.

| Added | When | Modules |
|---|---|---|
| `10-10` | 2026-10-10 | Five catalog entries from Wolfram's writings, written before the attempt: `Rule30Predecessors`, `Rule30PredecessorCounts`, `BusyBeaverLifetimes`, `Rule30Blocks`, `Rule30Jen`. Their docstrings cite only Wolfram and the literature. |
| `start` | 2026-10-15, 04:07–04:16 | The first Rule 30 Prize modules, written before the multi-agent rounds: `Rule30Prize`, `Rule30Diagonals`, `Rule30Window`. Their docstrings do not cite the multi-agent project. |
| `R1`, `R2`, `final` | 2026-10-15, 07:18, 09:40, 11:49 | The other 46 modules: round 1 (11), round 2 (7) and the final batch (28, including the 13 in `Rule30Certificates/`). Their docstrings cite the Rule 30 Prize project (2026). |

## Modules by topic

All modules live in `Ruliology/CellularAutomata/`. Theorems live in the namespace `Ruliology.CellularAutomata.<Module>`, with these exceptions:

- `Rule30Predecessors` and `Rule30PredecessorCounts` use `…Rule30`.
- The six `Rule30EtherThree*` modules share `…Rule30EtherThree`.
- `Rule30EtherTrapWidth20` uses `…Rule30EtherTrap`.
- `Rule30ZeroBoundaryStripeFamily` and `Rule30ZeroBoundaryStripeFour` use `…Rule30ZeroBoundaryStripeFront`.
- The data modules in `Rule30Certificates/` use namespaces inside the module they serve, for example `…Rule30ZeroBoundaryWidth52.C0`.

"Open" marks a statement defined as a `Prop` but not proved.

### Period 1

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Prize` | start | States Problems 1 and 2 as in formal-conjectures' `Other/Rule30.lean`. No column is eventually constant, so period 1 is excluded for every column and every transient. | `Problem1`, `Problem2`, `no_column_eventually_constant`, `center_not_eventually_period_one` |

### Windows

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Window` | start | From the first 16,384 center bits, computed in the kernel: there is no eventual period P ≤ 4096 with transient ≤ 8192. | `no_small_eventual_period` |
| `Rule30FactorWindow` | R1 | Any eventual period P from time T has T + P ≥ 16359, because the first 16,384 bits have 16,359 distinct factors of length 26. | `transient_add_period_ge` |

### Black runs and strip certificates

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30BlackRuns` | R1 | Nine black cells in a column shield the right half (Lemma A). Long black runs exclude many periods (Theorems B and D). | `nine_black`, `black_shield`, `no_long_black_run`, `no_black_white_run`, `not_eventually_zero_ones`, `no_white_run_11` |
| `Rule30BlackRunBlocks` | R1 | Theorem B′: excludes repeating words `1^r u` for eight kernel-checked blocks `u`, provided the black run is long: `r ≥ 18` for `u = 0, 00, 000, 0000, 0100`, and `r ≥ 27` for `u = 010, 0010, 0110`. Short runs, such as the open words `10`, `100` and `1110`, are not covered. | `no_black_run_block`, `no_period_black_run_then_white` |
| `Rule30StripCertificates` | R1 | Problem 1 holds iff no word is an eventual tail. Bitmask and rank strip certificates are sound via masked Jen; three words are excluded. | `problem1_iff_no_word`, `not_eventually_word_strip`, `Cert.sound`, `not_eventually_00000011`, `not_eventually_000000000101` |
| `Rule30StripCertificateTable` | R1 | Kernel-checked certificates exclude 30 periodic words of length 8–13. | `not_eventually_certTable` |

### Jen and masked Jen

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Jen` | 10-10 | Jen (1986): no two columns are both eventually periodic. | `jen`, `periodic_column_unique`, `not_adjacent` |
| `Rule30MaskedJen` | R1 | Masked, effective-boundary and window forms of Jen's theorem. | `masked_jen`, `orCol_not_eventuallyPeriodic`, `effective_step`, `window_jen`, `finitary_jen` |
| `Rule30DrivenLeft` | R1 | Jen's theorem for the left half driven by a boundary column: from a finite nonzero start, an eventually periodic driver makes no left column eventually periodic. A barrier: for a start whose leftmost black cell is at −n, column −1 can follow any target for the first n − 1 steps. | `no_periodic_column`, `barrier_exists`, `barrier_unique` |
| `Rule30WhiteSeed` | R1 | Of the center columns from a single black cell and from a single white cell, at least one is not eventually periodic. The same holds for rules 30 and 135. | `problem1_black_or_white`, `problem1_30_or_135` |

### Diagonals

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Diagonals` | start | Right diagonals have period 2^j from the start, and left diagonals are eventually 2^j-periodic. | `R_periodic`, `D_periodic`, `center_eq_parity` |
| `Rule30RightPeriods` | R1 | Right-diagonal periods: the doubling rule, upper and lower bounds, rows at powers of two, restarts. | `e_step`, `per_bound`, `per_upper`, `rows_at_powers_of_two`, `not_half_lower` |

### Zero-boundary left half and period 2

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30PeriodTwo` | R1 | What an eventual period 2 forces. `Q01` (zero-driven left half; **open**) implies no eventual period 2. | `normalize`, `golden`, `not_eventually_period_two_of_Q01`, `stripe_fixed` |
| `Rule30ZeroBoundary` | R2 | The zero-boundary left half (ZBL): dynamics, realization, free bits, equivalent forms of `Q01`, Jen inside the ZBL. | `Q01_iff_Theta`, `Q01_iff_bounded`, `Q01_iff_staged`, `count_constrained`, `jen_clock`, `free_bits_no00_no11111` |
| `Rule30ZeroBoundaryStripe` | R2 | ZBL epochs, stripe stability and stripe absorption. | `stripe_absorb`, `Theta_eventually_stripe_iff`, `first_defect_phase` |
| `Rule30ZeroBoundarySmall` | R2 | `Q01` holds for every start of width ≤ 16 (kernel-checked search). | `q01_width_le_16`, `q01_width_le_15_odd` |
| `Rule30ZeroBoundaryLanes` | final | A bit-sliced `Q01` checker that runs in the kernel, with its soundness proof. | `q01_of_checks`, `q01_of_chunks` |
| `Rule30ZeroBoundaryWidth52` | final | `Q01` holds for every start of width ≤ 52: depth 1 turns white at an even time ≤ 96. | `q01_width_le_52`, `q01_width_le_52_linear`, `not_inX_of_width_le_52` |
| `Rule30Certificates/ZeroBoundaryWidth52Chunks0`–`3` | final | Data: the 256 chunk checks behind width 52, 64 per file (namespaces `Rule30ZeroBoundaryWidth52.C0`–`C15`). | — |
| `Rule30ZeroBoundaryStripeFront` | final | The front window of a stripe prefix evolves on its own; checked periodic orbits bound its death time. | `front_sound`, `family_of_class` |
| `Rule30ZeroBoundaryStripeFamily` | final | Every stripe prefix `S[1..m] · v · 0^∞` with \|v\| ≤ 3 dies within 31 steps of arrival. | `stripe_prefix_family`, `stripe_prefix_family_list` |
| `Rule30Certificates/ZeroBoundaryStripeCycles0`–`2` | final | Data: the eight window cycles behind the stripe-prefix family. | — |
| `Rule30PeriodTwoCoupled` | R2 | The coupled question `CQ01` (**open**): `Q01` implies `CQ01`, and `CQ01` excludes period 2. The ether is an infinite witness. | `CQ01_of_Q01`, `no_eventual_period_two_of_CQ01`, `ether_coupled_witness` |
| `Rule30PeriodTwoLanguage` | final | Under period 2: if a kernel check shows that no path inside the bad class of the right strip spells a word, then column 1 at the white times eventually never spells it. | `no_pattern` |
| `Rule30PeriodTwoWidth5` | final | Period-2 constraints at strip width 5; for example, the free bits never spell `00` or `11111`. | `col1_constraints`, `free_bit_constraints` |
| `Rule30PeriodTwoWidth6` | final | The same at strip width 6, with more forbidden patterns. | `col1_constraints`, `free_bit_constraints` |

Q01 was also kernel-checked for width ≤ 56 during the attempt. That finite check is not part of this kit.

### Ether and period 4

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Ether` | R2 | The 7×4 ether, the 109-state wall and the ether-and-wall traps. Absorption (**open**) excludes `0001`, `0011` and `0111`. | `ether_rule`, `trap_invariant`, `no_ether_wall_entry`, `absorption_excludes`, `least_period_four_of_absorption` |
| `Rule30PeriodFourSkeleton` | R2 | The right-half skeletons that least period 4 forces, and a reduction to the left-half statements `C3` (**open**). | `skeleton_0001`, `skeleton_0011`, `column_m1_0111`, `least_period_four_of_C3` |
| `Rule30EtherTrap` | final | Traps of the strip relaxation, and a certificate check that a path escapes them. | `word_lemma`, `escapes_of_certOK`, `not_trap_of_certOK` |
| `Rule30EtherTrapWidth20` | final | The pure ether lies in no trap of width ≤ 20. | `pure_ether_not_in_trap_0001`, `pure_ether_not_in_trap_0011`, `pure_ether_not_in_trap_0111` |
| `Rule30Certificates/EtherTrap0`–`5` | final | Data: the 24 certificates behind width 20. | — |

### Period 3

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30EtherThree` | final | The 12×3 ether and the ether-and-wall framework for period 3. | `ether3_rule`, `alignments_001_complete`, `alignments_011_complete`, `absorption3_excludes` |
| `Rule30EtherThreeNoWall` | final | The period-3 ether has no wall of width ≤ 12. | `no_wall_le_12` |
| `Rule30EtherThreeTrap` | final | `t001`, a 47-column trap of period 21. `AbsorptionT t001` (**open**) excludes `001`. | `trap_001`, `absorptionT_excludes`, `not_eventually_001_of_absorption` |
| `Rule30EtherThreeReach` | final | The empty right half reaches `t001` at time 1270. | `t001_reached`, `absorbed_empty` |
| `Rule30EtherThreeLeft` | final | Reductions to the left half: `Q001` for `001` and `C3w` for `011` (both **open**). | `not_eventually_001_of_Q001`, `not_eventually_011_of_C3w`, `Q001_stripe`, `C3w_011_ether` |
| `Rule30EtherThreeSkeleton` | final | Right-half skeletons for `001` and `011`, and the reduction `C3s001` (**open**). | `skeleton_001`, `skeleton_011`, `not_eventually_001_of_C3s` |

### Barriers

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Realization` | R1 | Some configuration realizes any right half together with any column 0. Rules 90, 150 and 210 meet Jen's hypotheses, yet their center columns are eventually constant. | `column_realizable_unique`, `seed_perturbation`, `barrier` |
| `Rule30ZeroBoundaryBarriers` | R2 | For `Q01` there is no ranking through a finite abstraction, no local ranking and no edge-DFA ranking. Also gives a two-sided barrier. | `finite_abstraction_has_lasso`, `no_local_ranking`, `no_edge_dfa_ranking`, `no_joint_local_ranking` |

### Other catalog entries (not about Problem 1)

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Predecessors` | 10-10 | A corrected form of the Feynmans' predecessor theorem: rule 30 on a cyclic register. | `predCount_eq_three_iff`, `predCount_eq_one_iff` |
| `Rule30PredecessorCounts` | 10-10 | How many registers have 0, 1, 2 or 3 predecessors. | `sum_predCount`, `numWithPreds_zero` |
| `Rule30Blocks` | 10-10 | Only 24 of the 32 possible 3×2 blocks occur. | `blockAt_allowed`, `occurs_iff`, `occurs_single_cell` |
| `BusyBeaverLifetimes` | 10-10 | Busy-beaver lifetimes of four cellular automata. `Rule30Blocks` reuses its bit-plane simulation. | `lifetime450504084`, `lifetime5810255963295` |
