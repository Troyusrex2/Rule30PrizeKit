# Catalog review follow-through and independent proof audit

2026-10-24, Troy Lowry with OpenAI Codex. **Problem 1 remains open.**

The maintainer's outstanding reviews on PRs 1, 6, 7 and 9 have been addressed,
with replies posted on each conversation. Earlier commit-head audits missed
older review comments; this pass reads the conversations as well. No further
PR was opened during the cleanup.

## Revised catalog heads

All four branches include official main `cc6867c8fe269c04a60db9fce1720ce2dbb563fb`.
Each passes `lake build Ruliology` in `lean/` and the unchanged partial checker.
The counts below are declarations replayed in the contributed modules, excluding
their imported dependencies.

| PR | Revised head | Modules | Declarations | Headlines | Evidence |
|---|---|---:|---:|---:|---|
| [1](https://github.com/WolframInstitute/Rule30PrizeKit/pull/1) | `5dc53f37e910e5775ca6feff3268ab0147be0561` | 25 | 2641 | 52 | [Current-reference replay](pr1-current-reference-report.json) |
| [6](https://github.com/WolframInstitute/Rule30PrizeKit/pull/6) | `b94808b0110f3e0859ed26590b8c9d7a2337e2ae` | 4 | 197 | 12 | [Report](pr6-report.json) |
| [7](https://github.com/WolframInstitute/Rule30PrizeKit/pull/7) | `f58b7f7e8350285cfd9e205c34489530569399c1` | 5 | 158 | 16 | [Report](pr7-report.json) |
| [9](https://github.com/WolframInstitute/Rule30PrizeKit/pull/9) | `51d7d4d6c400f21df315a3d781a8031ff1b986ef` | 7 | 399 | 32 | [Report](pr9-report.json) |

The latest PR 1 replay is fresh at the exact published merge head `5dc53f3`,
including current reference kit `2f63afd`, without reusing earlier replay
results. Its [complete core build](pr1-current-reference-build-report.json)
passes for all 112 source modules. The 25 contributed proof sources are
unchanged, their compiled artifacts remain byte-identical to the freshly
replayed artifacts, and the import conflict with upstream has been resolved.
The README credits AIOvernight's stronger single-seed `10111` threshold of nine.

The [previous final replay](pr1-report.json) at `3b8cae7` and
[earlier build/replay history](pr1-build-and-replay-history.json)
record first-build resource measurements and explicitly identify reused,
byte-identical proof artifacts during intermediate wrapper fixes. The
[separate measurements](pr1-build-measurements.json) force all 21 main modules
to rebuild; each regenerated `.olean` is byte-identical to its verified input.
The final catalog build also passed after the documentation commit. The four
data builds peaked at approximately 3061, 1376, 656 and 2372 MiB.

The complete top-level `build_all.sh` also builds unrelated Mathlib equivalences
and was not executed in this pass; its shell syntax was checked. The catalog
build emits five non-failing unnecessary-`simpa` linter warnings. No checker,
official target, axiom policy, or test control was changed.

## Review changes

PR 1 retains the general five/six-tail and arbitrary-prefix suffix families.
Its 144 certificate files are consolidated into four data modules. All 21
main modules remain, with module names, namespaces, claim/method docstrings,
README headlines, measured build costs and a sequential build list. Full
builds caught and corrected relative data namespace references and a misplaced
root import after the public section.

The [source transport manifest](pr1-consolidation-manifest.json) and
[`audit_consolidation.py`](audit_consolidation.py) compare all 165 original
source components with the revised 25 modules. The allowed changes are exact
module/namespace transport, its corresponding namespace opening, comments,
whitespace, and four deprecated if/ite aliases. This comparison is a separate
source audit, not a substitute for kernel replay.

PR 6 retains the general column-separation, edge-recovery reduction, merge and
finite-ambiguity results, removing the fixed-edge/horizon separation modules
and all 14 associated certificate files. PR 7 removes both exhaustive
empty-gate certificates and their dependent gate-language/spacing results;
its exact-return module retains the general argument and boundary example.
PR 9 keeps all seven general controlled-response modules. Each PR is now
catalog-only, and all module names drop `Research`.

Earlier research, notebooks and certificate experiments remain on the fork's
`archive/pr{1,6,7,9}-before-catalog-review-20261024` branches. The maintainer
replies are [PR 1](https://github.com/WolframInstitute/Rule30PrizeKit/pull/1#issuecomment-6383210607),
[PR 6](https://github.com/WolframInstitute/Rule30PrizeKit/pull/6#issuecomment-6382841220),
[PR 7](https://github.com/WolframInstitute/Rule30PrizeKit/pull/7#issuecomment-6382841609),
and [PR 9](https://github.com/WolframInstitute/Rule30PrizeKit/pull/9#issuecomment-6382842023).
PR 1 remains open. The maintainer has now incorporated PRs 6, 7 and 9 into
official main, with the direct commits
[`570fc7f`](https://github.com/WolframInstitute/Rule30PrizeKit/commit/570fc7f195a4b4558993fa66aaa654ca69a9fd6e),
[`c24caf5`](https://github.com/WolframInstitute/Rule30PrizeKit/commit/c24caf5c34b07bea433da9344605458bf085ed81),
and [`9f4b63f`](https://github.com/WolframInstitute/Rule30PrizeKit/commit/9f4b63f038c24101d6ace7b5f5fa4f8a45414494).
All sixteen incorporated sources are byte-identical to their reviewed heads.
GitHub marks these PRs closed rather than merged; the files and commits on
main establish their incorporation. See the
[source correspondence record](upstream-incorporation-report.json).

## Current reference environment

The verifier's environment API now names official kit commit
`2f63afda261888e04ec57237290e723190914a1d`, with Lean 4.35.0,
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, and LeanLink 1.2.1.
The checker bytes have not changed. The official Problem 1 and `cell` source
files differ from the previous pinned revision only in module/export wrappers;
`Rule30Realization` additionally renames two deprecated proof aliases. The
definitions are unchanged. The historical pinned reports above retain their
original commits. The source correspondence record checks these transformations.

Fresh full kernel replay at the new reference commit passes for all seventeen
modules added since `cc6867c`: **886 declarations and 61 headlines**. This
includes our sixteen incorporated modules and AIOvernight's
`Rule30WhitePad10111` (132 declarations, one headline). The latter proves the
stronger threshold nine for that tail; it is credited to AIOvernight, OpenAI
Codex and Claude Code in the official README. No additional temporal period
is excluded by our audit. See [the new replay report](current-reference-replay-report.json).

The initial parallel whole-catalog build stopped at its memory resource
guard after all seventeen kernel replays had passed. The subsequent
[sequential build](current-reference-sequential-build-report.json) passes
for all **87 core source modules**, including the catalog root. The builder
below uses dependency order and retains the same resource guards and proof
settings. The complete root build with the unrelated Mathlib equivalences
was not run in this compatibility check.

## Human verification and outside contributions

The signed Wolfram status API now tags
[R30-20261024-ad6cac](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261024-ad6cac),
**Distinct spatial column traces with an explicit uniform bound**, as
**Lean Verified**, **Human Verified**, and **Kit Contribution**. The signed
status identifies the incorporated `Rule30ColumnSeparation` module at
`570fc7f195a4b4558993fa66aaa654ca69a9fd6e`. See the
[minimal status record](human-verification-status.json). That reviewed result
separates distinct spatial column traces from time zero; temporal
nonperiodicity remains open.

A [wider repository scan](quick-lean-scan.json) found Keith Adler's independent
core-Lean formalization of a known constant-column horizon theorem, credited
upstream to D. L. Condrey. Its original proof, plus an explicit bridge to the
official evolution, passed full replay in the pinned reference checkout:
124 declarations and two headlines. See [the report](adler-constant-column-report.json)
and [reproducer](audit_adler.py). It states that a nonzero row supported in
`[-A,A]` cannot keep the center constant through time `A+2`; it is a period-one
result, with no new-result or prize claim by this audit.

The new official core `Rule30Problem3` module also passed independent replay:
117 declarations and two selected headlines. This checks its computation
model and conditional implications between variants, not a lower bound.
The new Mathlib adapter was not replayed in this audit and is not used as a
premise. See [the core report](official-problem3-core-report.json).
Numerical/conditional seed-gap claims and unreviewed harness sources from
other repositories are not adopted as proved facts.

## XOR rigidity audit

The new [PR 12 XOR-rigidity contribution](https://github.com/WolframInstitute/Rule30PrizeKit/pull/12)
was independently replayed at immutable head
`e7d1e3a03dff9c57a0c78e94b7bf9e4df1c0bd36`, against the unchanged reference
kit at `2f63afda261888e04ec57237290e723190914a1d`: all **87 declarations and
10 selected headlines** passed full kernel replay, with standard axioms only.
The proof bodies and namespace are unchanged; only module/import/export
wrappers are removed for the standalone review. Credit: OpenAI Codex for
@AIOvernight; the pull request was assembled with Claude Code.

Its premise is that the pointwise XOR of two entire Rule 30 histories is
itself a Rule 30 history. Our kernel-checked
`same_trace_does_not_imply_xor_step` gives a concrete limitation on applying
it to the remaining trace-completeness question: finite rows **2 and 3 at
center index 1 have equal entire center traces**, but `Phi(2 XOR 3)=7` while
`Phi(2) XOR Phi(3)=3`. Their difference already fails the update on the
first step. The counterexample uses the independently replayed stripe
trace-preservation proof; it is an all-time statement, rather than a long
finite trace comparison. Its own five declarations and three headlines pass
full replay. See [the combined audit report](xor-rigidity-e7d-report.json)
and [the counterexample source](Rule30XorTraceBarrierResearch.lean).

To reproduce the external audit, fetch PR 12's immutable head into the source
repository and run:

```text
python research/catalog-review/audit_xor_rigidity.py --project <pinned-reference-checkout> --source-repository <repository-with-e7d1e3a> --lake <lake> --output <audit-directory>
```

For the counterexample too, first run
`research/normalization-first-meeting/replay.py` against the same reference
checkout, then add `--trace-barrier` to the audit command. This checks the
exact prerequisite source hashes before building and fully replaying the
counterexample.

## Reproduce

In a checkout of the corresponding revised PR head:

```text
python research/catalog-review/verify_catalog.py --project <checkout> --lake <lake> --output <evidence-directory>
```

Run the script from this research branch, pointing `--project` at the catalog
checkout. Its immutable comparison base is `cc6867c`; it checks the original
checker bytes, source hashes, full kernel replay, selected headlines, and
standard axioms, with time and memory guards. `--skip-build` replays already
built modules without running build commands.

For the complete core catalog on a machine that needs to limit compiler
concurrency:

```text
python research/catalog-review/build_catalog_sequential.py --project <checkout> --lake <lake> --output <build-evidence-directory>
```

This is a build, not kernel replay. It hashes every source before and after,
builds modules in dependency order, and changes no project or machine settings.

```text
python research/catalog-review/audit_consolidation.py --project <PR-1-checkout>
python research/catalog-review/audit_adler.py --project <pinned-reference-checkout> --lake <lake> --output <evidence-directory>
```

The Adler audit pins the upstream source hash and reference commit, preserves
the upstream Apache-2.0 copyright header, refuses to overwrite different source,
and proves agreement with the official evolution. It credits the upstream
author and makes no novelty claim.
