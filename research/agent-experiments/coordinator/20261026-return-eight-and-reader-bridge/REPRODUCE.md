# Reproduction

Use official kit5473ffd075f63c9d626e63b8455805d4831b39ca with Lean4.35.0 and its unchanged dependencies. Check.lean must have SHA256 b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905. Keep `--claim partial`, full replay, and the recorded headline names.

The exact original private runners, dependency source/compiled hashes, sources, reports and resource guards are preserved. Paths identify the original G913 run; adapt local executable/project/dependency paths in a fresh private copy, without changing proof sources or checker.

1. Rebuild the safety dependencies from `../20261026-short-extension-proof` in this order: CedarSafetySoundness, CedarSafetySemantics, CedarSafetyBridge. Their expected source hashes are in `work/root/sources.json`. Other prior artifacts listed by the original runner are integrity checks for that existing dependency directory, not additional mathematical assumptions.
2. Build the provided Rule30CommonPastResearch and Rule30ColumnReaderResearch. Then build/replay CedarMarkerReturnTwo, CedarReturnEightReduction and PrizeSafetyBridge. Build ResetExcursionControl after PrizeSafetyBridge. Use `work/root/replay.py` and `guard.py`, adapting the original directory checks and dependency locations to the isolated copy. Root's fresh common/reader dependency replay totals219; the three safety imports were previously root-replayed220 declarations, reused only after exact hash checks.
3. Rebuild RootEventHeight from `../20261026-height-and-cylinder/work/root-height`, then RootOrientedHeight from `work/oriented`. Its original runner checked its own prior43-declaration dependency by exact source and compiled hashes. The new module has13 replayed declarations.
4. Check each saved report's source hash, full replay status, counts, headlines, absence of new axioms and guard result. Recompilation on another platform need not produce identical binary hashes; use and validate that run's freshly compiled dependencies.
5. `python -B verify_artifacts.py` audits bytes and saved evidence, not the Lean kernel. `--staged` audits staged publication bytes.

The external PR31 audit is separately reproducible through `work/external-pr31/REPLAY.md`. It includes its exact public source provenance, namespace overlay, official dependency source checks, the resource-limited aggregate attempt and successful individually guarded recovery. Its218 declarations belong to the external contribution.

For finite diagnostics, run `python -B probe.py` inside `work/height-diagnostic`; the adjacent saved input is provided. `query.py` contains the exact one-clock Z3 query and a90-second solver timeout; adapt its optional local Z3 search path if needed. These controls do not replace unbounded Lean proofs. No fresh larger-width or larger-clock search is required to reproduce the claims here.
