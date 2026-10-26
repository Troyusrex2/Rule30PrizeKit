# Reproduce the checks

Use the official Rule30PrizeKit checkout at `5473ffd075f63c9d626e63b8455805d4831b39ca`, its Lean 4.35.0 toolchain and pinned Mathlib dependencies. Keep the official `Check.lean` unchanged; SHA256 is `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

Run `python verify_artifacts.py` in this archive to audit exact bytes and saved results. This checks receipts; it does not rerun Lean.

For a fresh replay, create a private output directory and prepend it to the pinned project's Lean search paths (obtain those with `lake env`). Compile the files in `sources/` in this dependency order, using `lean -o <private-output>/<Module>.olean <source>`:

1. CedarSafetySoundness, CedarSafetySemantics, CedarSafetyBridge, CedarWhiteTransport, RootShortExtensionCore, RootEventHeight, CedarNo11011, Rule30CommonPastResearch.
2. HeightOneLogic, HeightOneSemantics, HeightOneTransfer, HeightOnePeriodicity, HeightOneDescent.
3. RootReturningPrefixSafety, RootMinimalCounterexample, HeightTwoNearReturn, HeightTwoDescent.

All source imports are included in this archive or in the pinned official environment. Do not replace official modules or use compiled artifacts from another investigator. The eight modules in step 1 were previously root-replayed dependencies; the nine modules in steps 2–3 are the fresh replays in this checkpoint.

For each module, run the official checker from the pinned project:

```text
lean --run Check.lean <Module> --claim partial --headline <Module>.<theorem>
```

Use the exact headlines recorded in `formal/<Module>/report.json`; more than one `--headline` may be passed. Require verdict pass, full replay success, every headline type matching, and no new axioms. Guards used here were 300 seconds, 8 GiB total owned-process memory, and at least 2 GiB available system memory. The reports preserve actual timings and resource usage.

The separate catalog PR33 module imports official `Rule30ControlledResponse`. Build it with `lake build Ruliology.CellularAutomata.Rule30FiniteReturnEight` in the pinned core Lean subproject, then run the same official checker against its four catalog headlines. Its exact candidate, normal-build report, source review and PR readback are under `catalog-pr33/`.

Worker delivery folders retain failed elaboration attempts as well as successful ones. The root `formal/` directory contains only the successful exact-byte leaf replays; the 540-case prefix generator is explanatory evidence, not a trusted proof step.
