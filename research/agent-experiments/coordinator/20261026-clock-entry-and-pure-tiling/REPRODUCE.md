# Reproduce the checks

Use the official Rule30PrizeKit checkout at `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0 and its pinned dependencies. The unchanged `Check.lean` SHA256 is `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

Run `python verify_artifacts.py` to check exact archive bytes and saved receipts. This does not rerun Lean.

For a fresh replay, prepend a private output directory to the pinned project's Lean search paths and compile `sources/` in dependency order. Use `lean -o <output>/<Module>.olean <source>` and retain the official environment for imports not included here. An explicit order is:

1. CedarSafetySoundness, CedarSafetySemantics, CedarSafetyBridge, CedarWhiteTransport, RootShortExtensionCore, RootEventHeight, CedarNo11011, Rule30CommonPastResearch, RootAntiPeriodHeight.
2. HeightOneLogic, HeightOneSemantics, HeightOneTransfer, HeightOnePeriodicity, RootReturningPrefixSafety, HeightTwoNearReturn, HeightTwoDescent.
3. HeightTwoPureMode, SafeClockEntry, SafeEntryLocalControl, SafeClockDichotomy, HeightTwoMixedControl.

The sixteen modules in steps 1–2 are prior dependencies. The five modules in step 3 are this checkpoint's fresh root replays. Run the official checker on each new module:

```text
lean --run Check.lean <Module> --claim partial --headline <Module>.<theorem>
```

Use all headlines recorded in its `formal/<Module>/report.json`. Require full replay, matching headline types, no new axioms, and verdict pass. Root runs used 300-second / 8-GiB-owned / 2-GiB-system-free guards. Worker folders preserve their independent replays, generators, controls, and failed elaboration attempts. The temporal masks are only discovery inputs; the all-time claims are Lean theorems.
