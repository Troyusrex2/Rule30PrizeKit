# Reproduce the checks

Use the official Rule30PrizeKit at `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean4.35.0 and pinned dependencies. Require unchanged `Check.lean` SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

`python verify_artifacts.py` checks saved bytes and receipts; it does not invoke Lean.

For fresh replay, prepend a private output directory to the official Lean search paths. Compile each source with `lean -o <private-output>/<Module>.olean sources/<Module>.lean` in the following dependency order:

1. CedarSafetySoundness, CedarSafetySemantics, CedarSafetyBridge, CedarWhiteTransport, RootShortExtensionCore, RootEventHeight, CedarNo11011, HeightOneLogic, HeightOneSemantics, HeightTwoNearReturn, HeightTwoDescent, HeightTwoMixedControl, CedarMarkerReturnTwo.
2. AnchoredDefectAbstraction, MarkerCarryAmbiguity, MarkerCarryReconstruction, MarkerCarryProjectedCycle, MarkerTailStructure.

Step1 lists thirteen previously root-verified dependencies. Step2 lists the five fresh root replays in this checkpoint. Do not use peer compiled binaries. Run the unchanged official checker on each module in step2:

```
lean --run Check.lean <Module> --claim partial --headline <Module>.<theorem>
```

Use every headline in its `formal/<Module>/report.json`. Require full replay, matching types, no new axioms and pass verdict. Keep the official project read-only; all outputs belong in private directories. Root runs used guards of300seconds,8GiB owned RSS and2GiB minimum free system memory. Guard logs are included.

The sealed `work/` bundles preserve independent discovery scripts, finite controls, source generation and worker receipts. Their original local paths describe provenance and may require adjustment for another computer. The top-level sources and formal receipts are the independently root-checked copies. Neither Python discovery tables nor external public-source status replaces kernel replay of a proof being adopted.
