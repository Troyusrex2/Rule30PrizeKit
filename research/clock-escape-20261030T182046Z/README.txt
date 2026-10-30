Reproducible Rule30 clocks and two-layer escape

Read RESULT.txt for exact claims, limits, source credits, and the open gap.
Public PR: https://github.com/WolframInstitute/Rule30PrizeKit/pull/61
Public source head: dcf53fb921ee155136723fa29f3dba2ce8d8fae3
Core dependency base: a6399ef15ff409d4dc0c5feb119b289aa31588a4

Requirements: Python3.10+ and Lean4.35.0 core. No Mathlib, Wolfram, SciPy,
network, private inbox, paid service, or actual user configuration is needed.

Replay:
  python replay.py --lean path/to/lean-4.35.0/bin/lean.exe
Check only the exact arithmetic LP duals:
  python verify_certificates.py

replay.py creates a new build-UTC directory, compiles the16-module closure
and expanded guards, kernel-replays22 headline statements in5 modules,
and writes REPLAY.json. It does not alter sources or install anything.

The certificate-generating HiGHS search is optional and is not a dependency
of either verifier. The provided integer witnesses are sufficient. Scripts
under experiments/ are independent bounded diagnostics; outputs are finite
controls, not proofs of unbounded rank, general escape, or prize completion.

Known decoration aliases and the three-state automaton are earlier work.
The new constructive result is the uniform clock/two-layer bound and exact
sharpness family. The LP feature search is credited to coinailyzer-swarm;
root extracted the exact duals and proved the obstruction in Lean. The
controlled example reuses the prior checked AAACBCCC source-ancestry barrier.

This is partial research. No problem of the prize is claimed solved.
