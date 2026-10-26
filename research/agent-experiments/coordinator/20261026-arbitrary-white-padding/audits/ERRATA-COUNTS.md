# Replay-count correction — 2026-10-26

This additive note supersedes the interpretation of replay counts in the frozen v1 report/result. The Lean source, theorem statements, proofs, official PASS, and no-new-axioms result are unchanged. All v1 files and their original manifest remain byte-for-byte preserved.

## Correct counts

| Artifact | Explicit source declarations | Non-internal constants listed in `declared` | Internal generated constants | Total module constants replayed |
| --- | ---: | ---: | ---: | ---: |
| `FrontBlackInterval` | 12 | 13 | 44 | 57 |
| `Rule30AgedLeftDiagonals` catalog module | 16 | 18 | 45 | 63 |

The replay totals count the module's **own** compiled constants, including internal generated proof constants. They do not count transitive imported modules. They are not counts of handwritten theorems.

The frozen `RESULT.json` key `kernel_replayed_constants_including_transitive_imports` is therefore incorrectly named. `RESULT-v2.json` replaces it with explicit module, non-internal, and internal counts. The frozen report's phrase “13 owned inspected constants” should be read more precisely as “13 non-internal module constants listed by the inspector.” Its total replay count of 57 was correct.

For the base leaf, the extra non-internal declaration is `FrontBlackInterval.PeriodFrom.eq_1`. For the catalog candidate, the two non-internal generated equation declarations are `Ruliology.CellularAutomata.Rule30AgedLeftDiagonals.PeriodFrom.eq_1` and `Ruliology.CellularAutomata.Rule30FiniteDiagonals.Ld.eq_1`. A generated declaration's namespace does not imply that the checker replayed its imported source module.

## Direct checker evidence

The correction was checked against `D:/MWB/Rule30/overnight-20261024/Check.lean`, SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`:

- Lines 118–125 construct the imported environment separately, collect the inspected module object's own constants, and replay that collection.
- Lines 202–206 construct `declared` by filtering that collection with `!name.isInternal`.
- Line 230 reports `replay.constants` as the full collection's size.

The root-run receipts still show PASS and no new axioms:

- Base: `../front-interval-root-review-20261026T2128/formal/FrontBlackInterval/report.json`.
- Catalog: `../aged-catalog-root-review-20261026T2136/formal/CatalogModule/report.json`.

The catalog now also has a root-run cold core build with 16 fresh official source dependencies and PR #34 at commit `f04ee865b052380886431ae5380486941b365a9a`. The separate additive catalog status note records that evidence. No source edit, build, or publication was performed for this correction. P1 remains open.

The preserved v1 manifest SHA256 is `46452baf548cbf625331f1cdce9863ae709185b12e6afbcc3040fc2c1a9e7525`. `MANIFEST-v2.sha256` covers the original artifacts and manifest plus these additive correction files.
