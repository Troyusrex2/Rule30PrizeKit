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
| [1](https://github.com/WolframInstitute/Rule30PrizeKit/pull/1) | `3b8cae7ed1573dbe30b9b38e53ff2113864706e4` | 25 | 2641 | 52 | [Final replay](pr1-report.json) |
| [6](https://github.com/WolframInstitute/Rule30PrizeKit/pull/6) | `b94808b0110f3e0859ed26590b8c9d7a2337e2ae` | 4 | 197 | 12 | [Report](pr6-report.json) |
| [7](https://github.com/WolframInstitute/Rule30PrizeKit/pull/7) | `f58b7f7e8350285cfd9e205c34489530569399c1` | 5 | 158 | 16 | [Report](pr7-report.json) |
| [9](https://github.com/WolframInstitute/Rule30PrizeKit/pull/9) | `51d7d4d6c400f21df315a3d781a8031ff1b986ef` | 7 | 399 | 32 | [Report](pr9-report.json) |

The final PR 1 replay is fresh at the exact published head, without reusing
earlier replay results. Its [earlier build/replay history](pr1-build-and-replay-history.json)
records first-build resource measurements and explicitly identifies reused,
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
These are addressed reviews, not claims that the PRs have been merged.

## Human verification and outside contributions

The signed Wolfram status API now tags
[R30-20261024-ad6cac](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261024-ad6cac),
**Distinct spatial column traces with an explicit uniform bound**, as
**Lean Verified** and **Human Verified**. See the
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

```text
python research/catalog-review/audit_consolidation.py --project <PR-1-checkout>
python research/catalog-review/audit_adler.py --project <pinned-reference-checkout> --lake <lake> --output <evidence-directory>
```

The Adler audit pins the upstream source hash and reference commit, preserves
the upstream Apache-2.0 copyright header, refuses to overwrite different source,
and proves agreement with the official evolution. It credits the upstream
author and makes no novelty claim.
