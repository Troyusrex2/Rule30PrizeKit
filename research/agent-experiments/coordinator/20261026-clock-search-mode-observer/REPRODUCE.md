# Reproduce

Use the official kit at `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean
4.35.0 and its pinned Mathlib. Checker's SHA-256 is
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
Start with `python verify_artifacts.py`; `--staged` checks actual Git index
bytes.

Copy the `work/*.lean` research sources into a disposable project at that
pin. Build and check modules in the order in `work/refresh-modules.json`,
then `Rule30ClockSearchResearch`, then `Rule30ClockModeResearch`.
For each use normal `lake build <module>` and
`lake env lean --run Check.lean <module> --claim partial --headline <name>`.
Headlines, source hashes and exact commands are saved in `work/formal`,
`work/final-pin-audit.json` and `work/replay.py`. Adapt owned project paths
in the replay wrapper rather than overwriting another working project.

The source manifest records every official file. The isolated cache-copy
scripts document this session's migration and require its previous owned
cache; a fresh machine can use the kit's normal setup. Wait for copying to
finish before building reference roots. The original sequencing failure
and subsequent complete byte audit are both retained.

All 41 research modules passed full replay, each below one minute and
4 GiB. Research guards stay at 300 seconds, 8 GiB owned RSS and 2 GiB
system free. No proof-native shortcuts or checker changes are permitted.

From `work`, run `python guard.py clock_search_control.py` for independent
periodic-driver controls. `python guard.py wl_clock_search.py` additionally
uses the local Wolfram Engine path in that wrapper; it tests built-in
Rule 30 and performs no cloud sign-in or submission.

The experiments are separate from the Lean proofs. From `work/experiments`:

- `python guard.py audit_temporal_dfa.py` independently replays all 66,282
  DFA rejection witnesses without NumPy, Numba or Z3.
- `python guard.py mode_descent_probe.py` rebuilds the fixed-clock prefix
  graphs through 64 and literally audits selected full trajectories and
  the failed erosion formulas. It has no third-party dependencies.
- The original tiny-DFA search additionally uses NumPy and Numba.
- Tree/paired-stream learning and table inspection additionally use Z3
  5.3.1. Supply it in an isolated `solver-deps` directory, or adapt the
  import path to an existing installation. `solver-manifest.json` records
  this session's copied package; binary dependencies are not committed.

Solver timeouts mean `unknown`. The finite mode correspondence is not a
uniform observer theorem; missing membership in a fixed-clock graph is
not general nonrealizability. No full prize proof is asserted.
