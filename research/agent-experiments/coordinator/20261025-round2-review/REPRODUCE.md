# Reproduction and evidence boundaries

`artifacts.json` hashes every archived file except itself. Run
`python verify_artifacts.py` here first. Run experiments in a **scratch copy**;
they write outputs and logs. Original received files are under
`work/snapshots`. Copy each response to `work/runs/<response_id>/` in the
scratch copy before using coordinator wrappers that refer to `runs`.

Received manifests with schema notes are preserved, not silently normalized.
The verifier checks their artifact hashes independently of schema validity.

## Mathematical environment

Reference kit: `3eca23c0a9fa6b153313655e6d51835406c2d06e`; Lean 4.35.0.
Unchanged checker SHA-256:
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
Coordinator Python 3.12.3, psutil 5.9.8, NumPy 1.26.4, scikit-learn 1.8.0.
Exact finite scripts use standard Python integers/Fractions or the stated
prime field. No solver status or learning score is a Lean proof.

For Lean, use your own project/build output at that pin with compiled official
imports. The earlier published C1 core/bridge and their research dependencies
must be installed unchanged. Copy `CedarAncestry.lean` from its received
response and the seven new `work/*.lean` modules into your scratch project.
Compile in this dependency order:

1. `CedarAncestry`, then `Rule30RoundTwoAncestryFrontResearch`.
2. `Rule30RoundTwoDrivenPrefixResearch`, `Rule30RoundTwoChargeTwoEntryResearch`,
   `Rule30RoundTwoChargeTwoThetaResearch`, `Rule30RoundTwoChargeTwoResearch`,
   `Rule30RoundTwoChargeTwoBridgeResearch`.
3. `Rule30RoundTwoDefectTransferResearch` (independent of steps1/2).

For each module use `lake env lean -o <your-build>/<Module>.olean <Module>.lean`
and then the unchanged `lake env lean --run Check.lean <Module> --claim partial
--headline <fully-qualified-headline>`. Full exact commands and every checked
headline are in the corresponding reports. Add your own build directory to
LEAN_PATH as needed. The conditional ancestry bridge must not be run as a
purported full Problem1 proof.

Coordinator scripts retain original paths for provenance. `replay_with_reference_imports.py`
uses the previously compiled reference imports read-only and a separate
`cedar-verifier/cedar-build` for owned outputs. Update its project/tool paths
when reproducing on another machine, or use the commands above. The unchanged
checker emits its existing deprecation warning; do not edit it to remove that.

## Finite experiments

The independently repeated outcomes are in `work/*reproduction.json`,
`work/sanity-reproduction-v1`, and `work/evidence/cedar/fronts.json`.
Coordinator wrappers and exact supplied sources are included. Examples in a
prepared scratch copy:

```
python -B work/guard.py swarm_prefix_cycle.py
python -B work/guard.py wiki_followup.py
python -B work/guard.py wiki_cycle_checks.py
python -B work/guard.py backend_reproduce.py
python -B work/guard.py photograde_reproduce.py
python -B work/guard.py moving_edge_reproduce.py
```

Wrappers use paths relative to their own file, so launch as shown or from
`work/`. The wiki trap search also names the original pinned official source
path; supply that checkout or adjust only the path in your scratch copy.
The sanity response has its own `src/run_guarded.py --output <new-directory>`.
The Cedar response has its own reviewed `guard.py` and `replay.py` with
`--project` and `--lean` options.

Guards used: 300-second wall limit, 8 GiB owned process-tree RSS, minimum
2 GiB system available memory, 0.1-second samples. Final relevant guards all
completed normally. Reported sampled peaks are not guaranteed true peaks.
The coordinator fixed an outer console encoding error and a shared guard
log-name collision before archiving final per-module logs. It reran the four
affected module jobs with distinct names; no mathematical source was changed
by that logging repair. Raw checker reports were separate throughout.

Finite-only conclusions are explicitly labeled in the reports. The cycle
certificates include full deterministic states and written semantic arguments;
they have not been translated into Lean here. The larger supplied backend
rank runs and moving-edge full seed sweep were not independently repeated.

The transcript and files contain mathematical seeds, not computer security
keys. No computer configuration, credentials, unrelated files, remote prize
essay submission or new PR is part of this archive.
