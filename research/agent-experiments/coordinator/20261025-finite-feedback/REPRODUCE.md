# Reproduction

Use Python 3.12 with NumPy 1.26 and psutil 5.9, Lean 4.35.0, and the official
kit at `3eca23c0a9fa6b153313655e6d51835406c2d06e`. Saved scripts contain the
original Windows paths; in a disposable copy, change `root`, `ref`, `repo`
and the Lake path to your equivalents. Never rerun inside this hash archive.

`python -B verify_artifacts.py` checks saved hashes and scope read-only.
`--staged` checks actual staged Git blobs.

Run the eight experiment scripts using `python -B guard.py SCRIPT.py` in
the order trap_cycles, backward_traps, backward_beam, guided_preimages,
exhaustive_traps, width24_traps, period_lifting, minimize_period. They create
outputs; use a fresh directory. `feedback_core.py` and `preimage_core.py`
are helper modules. Width24 uses the prior width20 archive for chunk zero.
The guard limits owned process trees to 300 seconds and 8 GiB, stopping
when available system memory falls below 2 GiB. A cap or failure is not a
negative mathematical result.

For proof replay, copy the unchanged official Check.lean into an owned
verifier directory, create its owned-build directory, and run replay.py on
Rule30SpatialLiftingResearch first, then Rule30SpatialPeriodResearch, with
the headline names from the saved reports. Its stale optional source-green
dependency path may be omitted: these modules use only the pinned kit.

Alternatively apply the three-file catalog PR to the pinned core project
and run the saved check_catalog.py after adjusting its paths. It executes
`lake build Ruliology.CellularAutomata.Rule30SpatialPeriodLifting` in lean/
then the unchanged official checker with word_power, stateAt_period and
recon_period_lift as partial-result headlines. Require full replay, no new
axioms, and successful headline checks. A build or axiom check alone is not
equivalent to full kernel replay. No Wolfram authentication is needed.
