# Reproduction

Use Lean 4.35.0 and a private checkout of kit commit `5473ffd075f63c9d626e63b8455805d4831b39ca`. The unchanged checker SHA256 must be `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

Fetch the two public sources at the exact upstream commit in `work/public-source.json`. Check their recorded SHA256 values. Put WhiteEndNineChecks.lean under `lean/Ruliology/CellularAutomata/Rule30Certificates/`, and Rule30WhiteEndNine.lean under `lean/Ruliology/CellularAutomata/` in the private checkout. Build the certificate module first, then the main module. Run the unchanged checker against each full module name, with `--claim partial` and the exact headlines in `work/replay.py` or the reports. The certificate module has a different module name from its declaration namespace; keep that distinction when invoking the checker.

The archived Windows scripts record our actual guarded private replay. Their machine paths are historical and must be adjusted for another environment. `prepare_overlay.py` checks official source hashes and writes only its private import overlay. Do not copy these sources into a shared reference project. No binary build caches are published.

`python -B verify_artifacts.py` verifies the recorded hashes, source/report correspondence, checker outcomes and resource guards. Add `--staged` to check Git's staged bytes. This evidence audit does not rerun Lean and does not substitute for kernel replay.
