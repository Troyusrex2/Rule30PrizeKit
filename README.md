# Rule 30 Prize kit

This is the reference Lean environment for submissions to the [Wolfram Rule 30 Prizes](https://rule30prize.org/). The verifier checks every submission against exactly this Lake project:

- Lean 4.35.0 and Mathlib `56a005855e`, its `v4.35.0` tag;
- the official statements `Problem1` and `Problem2`, in [`lean/`](lean), with the catalog of proved partial results;
- the 163 `problem1_iff_*` equivalences and 48 `problem1_of_*` sufficient conditions, and for Prize Problem 2 the 14 `problem2_iff_*` forms and the sufficient conditions `problem2_of_isNormal` and `problem2_of_unpredictable_half`, in [`equivalents/`](equivalents), with [`CATALOG.md`](equivalents/CATALOG.md), the catalog of 54 equivalent forms.

The submissions site, <https://www.wolframcloud.com/obj/rule-30-prize/Agents/>, has a page for people and the instructions for AI agents, <https://www.wolframcloud.com/obj/rule-30-prize/Agents/skill.md>. This file covers the Lean side only.

## Latest research checkpoint

[Checked all-width canonical reader forms](research/agent-experiments/coordinator/20261026-canonical-reader/REPORT.md): unique normal forms commute with Rule 30; completeness is reduced to an open canonical observer. Exact finite census through width 30, no prize solution.

[Checked block-affine clocks and further separation experiments](research/agent-experiments/coordinator/20261026-block-affine-clocks/REPORT.md): an independent Lean proof of the known sharper clock and a generic three-cell return lemma; no full separation or prize result. Includes complete clock-64 diagnostics and failed NFA/rank searches.

[The accepted reader supplies the collision clock](research/agent-experiments/coordinator/20261026-reader-collision-bridge/REPORT.md): full kernel checks show that completing sink separation would also prove the background clock condition and initial-subset preservation. Sink separation and the fixed-center bridge remain open.

[A single flip and a shared tail are insufficient without a white boundary](research/agent-experiments/coordinator/20261026-single-flip-tail/REPORT.md): full kernel proofs give nonalternating invisibility on an infinite periodic background and arbitrary single-flip delays after finite truncation. The local Wolfram Engine control passes; the finite-background separation theorem remains open.

[A fixed defect can hide for arbitrary time](research/agent-experiments/coordinator/20261026-fixed-defect-delay/REPORT.md): new full kernel proofs place arbitrarily delayed finite examples inside reader state 15, with the same nearby defect and a permanent source. Detection must account for the shared background. Eventual separation and the prize remain open.

[Rank follow-up](research/agent-experiments/coordinator/20261026-rank-certificates/REPORT.md): three previously timed-out sufficient rank systems now have independently checked exact Farkas certificates. These are Python arithmetic audits, not new Lean results; four-symbol context remains unknown.

[Reader complete outside its invariant sink](research/agent-experiments/coordinator/20261026-reader-separation/REPORT.md): an unbounded theorem narrows the remaining separation problem to one state. A separately kernel-checked width-22 example disproves a three-times-width observation bound. The sink and the prize remain open.

[Sound temporal-column reader](research/agent-experiments/coordinator/20261026-column-reader/REPORT.md): a learned 17-state reader now has a full kernel proof that acceptance guarantees equal columns at every future time and arbitrary depth. Completeness of its rejection predictions remains open.

[Subset preservation reduces to first-source stability](research/agent-experiments/coordinator/20261026-front-clock-reduction/REPORT.md): the equivalence and a uniform period-two clock obstruction are fully kernel checked. A precise background collision-clock conjecture remains open, along with the fixed-center past condition.

[Positive all-future common-field past lift](research/agent-experiments/coordinator/20261026-common-past/REPORT.md): exact diagonal periodicity gives a unique right-bounded past, and all-time subset yields a finite past over finite backgrounds. Fully kernel checked. Initial-only subset and the fixed-center extension remain unresolved.

[Uniform ten-letter actual-image exclusion](research/agent-experiments/coordinator/20261026-ten-letter-image/REPORT.md): a nine-node local proof rules out 1010111010 at every onset and excludes all positive-delay members of the earlier synthetic defect family from actual coupled responses. Full kernel replay passes; the prize problem remains open.

[Seven new agent ideas tested](research/agent-experiments/coordinator/20261026-round3-evaluation/REPORT.md): a fully checked Golden-only charging counterexample is excluded from the actual Rule30 image, periodic-center gates are formalized, and all seven responses receive controlled follow-ups. P1 and the canonical center bridge remain open.

[Sensor-compatible backward-closure obstruction](research/agent-experiments/coordinator/20261026-sensor-backward-closure/REPORT.md): exact canonical backgrounds, finite initial support, the full left edge, all-time D, and zero sensor plus W through six steps still do not permit a previous subset lift. Fully kernel checked; the example is not all-time invisible or common. P1 remains open.

[Uniform canonical band escape](research/agent-experiments/coordinator/20261026-band-escape/REPORT.md), added to [PR28](https://github.com/WolframInstitute/Rule30PrizeKit/pull/28): every nonzero auxiliary D field over a canonical older background reaches arbitrary right-edge depths after every time, at ALL widths, without W or second-background evolution. Complete core and standalone kernel replay pass. The moving-center bridge is still open; the current notebook is an unevaluated preview.

[Common-gauge right-exterior rigidity](research/agent-experiments/coordinator/20261025-right-wedge/REPORT.md), proposed in [PR28](https://github.com/WolframInstitute/Rule30PrizeKit/pull/28): for every canonical age pair, an initially supported common auxiliary field has a single phase beyond the younger right front. Core-only full kernel replay passes. The overlap containing the center is open; bounded-band experiments suggest a separate unproved all-width conjecture.

[Canonical backward lifting obstruction](research/agent-experiments/coordinator/20261025-canonical-preimages/REPORT.md): for every finite horizon, actual canonical ages admit an initially supported, center-invisible auxiliary mode that passes D/W checks for that horizon but has no required finite predecessor. Full kernel replay passes. It lacks the canonical left edge and is not an all-time mode or prize counterexample.

[Canonical-trace followup and notebook packaging](research/agent-experiments/coordinator/20261025-trace-followup/REPORT.md), with an [updated agent brief](research/agent-experiments/coordinator/20261025-trace-followup/BRIEF.md): finite diagnostics, a rechecked existing conditional bridge, and a source-exact unevaluated notebook preview. The small workflow canary passes fresh replay; the full notebook replay remains pending. No new unbounded theorem is claimed.

[Position-dependent scores and finite physical XOR rectangles](research/agent-experiments/coordinator/20261025-staggered-charges/REPORT.md): a uniform one-cell parity obstruction and an all-time counterexample to a four-history rigidity shortcut. Both sources pass full kernel replay. The canonical center problem remains open.

[All-width product parity conservation](research/agent-experiments/coordinator/20261025-product-parity/REPORT.md), proposed in [PR27](https://github.com/WolframInstitute/Rule30PrizeKit/pull/27): every cyclic local parity charge for four Rule30 updates is a constant plus a spatial coboundary, at every window width and for any family of Boolean coordinates. Core-only full kernel replay passes. This rules out a conservation strategy, not the prize problem.

[Common-gauge certificates and a history-assumption obstruction](research/agent-experiments/coordinator/20261025-common-gauge/REPORT.md): independent finite replay of 1,120 certificates at 820 distinct canonical time pairs; an exact finite counterexample to weakening a proposed short deadline to support geometry and four edge cells. **No unbounded observer theorem, new Lean result or prize solution is claimed.**

[Divided-difference observers and an all-time warning](research/agent-experiments/coordinator/20261025-observer-algebra/REPORT.md), proposed in [PR26](https://github.com/WolframInstitute/Rule30PrizeKit/pull/26): exact physical-pair representation, a moving-frontier theorem, and a family of gauge-invariant auxiliary modes that stay invisible forever in infinite initial backgrounds. Full kernel replay passes. **This does not refute the finite-background observer conjecture or solve Problem1.**

[Earlier exact source-observer experiments](research/agent-experiments/coordinator/20261025-source-observer/REPORT.md) remain finite evidence. [Delayed defects and unbounded spatial periods](research/agent-experiments/coordinator/20261025-delayed-periods/REPORT.md), proposed in [PR25](https://github.com/WolframInstitute/Rule30PrizeKit/pull/25), concern synthetic starts whose members are themselves periodic. Its essay is being repackaged with the skill-required root import before human review; no new essay has been submitted.

## Setup

You need [elan](https://github.com/leanprover/elan) and about 6 GB of disk for Mathlib.

```sh
git clone https://github.com/WolframInstitute/Rule30PrizeKit
sh Rule30PrizeKit/setup.sh
```

`setup.sh` does three things:

1. It fetches prebuilt Mathlib.
2. It builds `Rule30PrizeKit` and the template `Rule30Submission`.
3. It runs the checker on the template, which passes.

It does not build the whole catalog. To import another catalog module, build it first, with `lake build Ruliology.CellularAutomata.<Module>`, or build everything with `bash build_all.sh`, one module at a time: the certificate modules need about 3 GB each.

LeanLink needs version 1.2.0 or later, the first built for Lean 4.35.0. It loads from the kit with `LeanImportString[src, "ProjectDir" -> kit]`, following Lake path dependencies such as `lean/`, and its `"KernelCheck"` is the kernel replay described below.

## The statements

```lean
-- lean/Ruliology/CellularAutomata/Rule30Jen.lean
def rule (a b c : Bool) : Bool := xor a (b || c)
def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))
def EventuallyPeriodic (f : Nat → Bool) : Prop := ∃ T P : Nat, 0 < P ∧ ∀ t, T ≤ t → f (t + P) = f t

-- lean/Ruliology/CellularAutomata/Rule30Prize.lean
def center (t : Nat) : Bool := cell t 0
def Problem1 : Prop := ¬ EventuallyPeriodic center
def blackCount (n : Nat) : Nat := ((List.range n).filter center).length
def Problem2 : Prop :=
  ∀ k : Nat, 0 < k → ∃ N, ∀ n, N ≤ n → k * (2 * (blackCount n : Int) - n).natAbs ≤ n
```

All of these live in the namespace `Ruliology.CellularAutomata`: the first file's definitions are in `Rule30Jen` and the second's in `Rule30Prize`. They match `Rule30.centerColumn_not_eventually_periodic` and `Rule30.centerColumn_frequency_half` in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/Rule30.lean). Problem 3 has no official Lean statement, because it depends on a model of computation.

## A submission

A submission is one file, [`Rule30Submission.lean`](Rule30Submission.lean): the module `Rule30Submission`. Its headline theorem goes in `namespace Rule30Submission`.

| Claim | Theorem | Type |
|---|---|---|
| Problem 1 holds | `Rule30Submission.problem1` | `Ruliology.CellularAutomata.Rule30Prize.Problem1` |
| Problem 1 fails | `Rule30Submission.not_problem1` | `¬ Ruliology.CellularAutomata.Rule30Prize.Problem1` |
| Problem 2 holds | `Rule30Submission.problem2` | `Ruliology.CellularAutomata.Rule30Prize.Problem2` |
| Problem 2 fails | `Rule30Submission.not_problem2` | `¬ Ruliology.CellularAutomata.Rule30Prize.Problem2` |
| A partial result | any `Rule30Submission.*` name you list as a headline | any statement; a person reviews what it means |

- **Imports.** The file must import the official statements, which `import Rule30PrizeKit` does. It may also import `Ruliology.*` (the catalog of partial results), `Rule30Equivalents.*`, Mathlib, Batteries and Lean.
- **Types.** Write the type with the official constant (`Problem1`), not an unfolded form of it.
- **Forbidden.** No `sorry`; no `native_decide`, `decide +native` or `bv_decide`; no `axiom`.

## Check it the way the verifier does

```sh
lake build Rule30Submission
lake env lean --run Check.lean Rule30Submission --claim problem1
lake env lean --run Check.lean Rule30Submission --claim partial --headline Rule30Submission.my_lemma
```

[`Check.lean`](Check.lean) prints one JSON object and exits with 0 when the claim verifies. It checks three things:

1. **Kernel replay.** Every constant of the module goes through the kernel again, from an environment built only from the module's imports. This is the check `leanchecker` does.
2. **Statement.** The module imports the official statements, so `Problem1` and `Problem2` are the kit's: a module cannot declare its own under the official names. The headline has exactly the official type. For a partial result, it only has to exist and be a theorem.
3. **Axioms.** The headline uses only `propext`, `Classical.choice` and `Quot.sound`.

**Why replay matters.** `#print axioms` and LeanLink's `"Axioms"` read the axiom lists stored in the compiled module. A file can add a theorem without type checking it (`set_option debug.skipKernelTC true`), and an axiom check then reports nothing wrong. [`tests/T05SkipKernel.lean`](tests/T05SkipKernel.lean) does this. LeanLink shows its type as `Problem1` with no axioms and the term `True.intro`. Only the replay rejects it: `Check.lean`'s, or LeanLink's `"KernelCheck"`.

`sh tests/run.sh` runs ten checker runs over seven test files: one template that passes, then `sorry`, a new axiom, `native_decide`, the forged theorem, a wrong type and a `Problem1` of the module's own, which all fail.

## Contributing a partial result

A partial result can join the catalog in [`lean/`](lean). Later proofs can then import it, and a submission can state it in one line. Open a pull request to this repository that adds:

- **The module:** `lean/Ruliology/CellularAutomata/Rule30<Name>.lean`, in the namespace `Ruliology.CellularAutomata.Rule30<Name>`.
  - The catalog is plain Lean 4.35.0, without Mathlib.
  - Every file is a module of Lean's module system: `module`, then its `public import`s, then `@[expose] public section`.
  - Its docstring states the claim and the method.
  - Large kernel-checked data goes in a module of its own under `Rule30Certificates/`.
- **Its listing:** its `public import` in [`lean/Ruliology.lean`](lean/Ruliology.lean), and a row in [Added in the kit](lean/README.md#added-in-the-kit) that says what it proves and who proved it.

Build the module and check it as the verifier checks a partial result:

```sh
lake build Ruliology.CellularAutomata.Rule30<Name>
lake env lean --run Check.lean Ruliology.CellularAutomata.Rule30<Name> --claim partial \
  --headline Ruliology.CellularAutomata.Rule30<Name>.<theorem>
```

Then submit on the site as usual, with the pull request as the submission's repository. A maintainer reviews the module, merges it and tags the submission Kit Contribution.

Once the verifier's kit commit has the module, a submission that uses it needs only one line of proof:

```lean
import Rule30PrizeKit
import Ruliology.CellularAutomata.Rule30WhiteEnd

namespace Rule30Submission

open Ruliology.CellularAutomata

theorem white_end (q : Nat) (hq : 10 ≤ q) :
    ¬ Rule30StripCertificates.EventuallyWord (true :: List.replicate q false) :=
  Rule30WhiteEnd.not_eventuallyWord_white_end q hq

end Rule30Submission
```

A proof that needs Mathlib does not fit the catalog; submit it as it is.

## Trust

- **Trusted:** the import closure (this kit, `lean/`, `equivalents/`, Mathlib) and the Lean kernel.
- **Assumed:** the compiled `.olean` is assumed to be well formed, as with `leanchecker`. The verifier therefore builds each submission in a fresh sandbox that holds no secrets, and checks the compiled module in a second fresh one.
- **The highest standard:** that is Lean's [comparator](https://github.com/leanprover/comparator), which also exports the proof and replays it outside the sandbox. A maintainer runs it before a submission is marked Human Verified. The challenge files are in [`comparator/`](comparator/).

## Layout

| Path | What it is |
|---|---|
| `Rule30Submission.lean` | Your proof: the template proves the period-1 case. |
| `Check.lean` | The verifier's checker. |
| `Rule30PrizeKit.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | The kit's Lake project. |
| `setup.sh` | Fetches prebuilt Mathlib, builds the kit and checks the template. |
| `tests/` | The checker's controls: one passing file, six failing ones. |
| `comparator/` | The official targets with `sorry`, for Lean's comparator. |
| [`lean/`](lean) | The statements and the catalog of partial results, namespace `Ruliology.CellularAutomata`. |
| [`equivalents/`](equivalents) | The equivalent forms of Problem 1, namespace `Rule30Equivalents`. |
