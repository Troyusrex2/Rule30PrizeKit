# Reproduce

All non-Lean experiments here remain computational evidence. Run them only
in copied work directories under the unchanged300s/8-GiB-owned/2-GiB-free
guard. Width32 uses a4-GiB visited array; G913 supplied sufficient headroom.
Do not raise a guard or install dependencies silently. The large producer
needs NumPy/Numba; the independent audits need standard Python and psutil
for the guard. The documented private Z3 path is an existing installation;
adapt it to a separately available compatible solver. No solver binaries
or credentials are distributed.

```text
python -B guard.py audit_safe_language.py
python -B guard.py audit_compact_cubic.py
python -B guard.py strip_ancestry_probe.py
```

These independent audits operate on the compact archived artifacts.
`safe_stress_orbits.py` reproduces the full width30/32 orbit decomposition.
`mode_cubic_probe.py` regenerates the cubic experiment; the 24-MB verbose
dual witness was replaced in this archive by a494-KB list of literal
width/initial-hex pairs. All43,745 moments can be reconstructed from it.
The SAT jobs have8-second case timeouts; unknown is not unsat.

For PR31, use a disposable kit checkout at
`5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean4.35.0.
Copy the two exact new modules to their paths in pr31-source.json, build
their official dependencies normally, then build and fully replay the data
module before the main module. Namespace for headlines in both modules is
`Ruliology.CellularAutomata.Rule30WhiteEndNine`. Commands and headlines are
recorded in replay_pr31.py; adapt its explicit owned project paths.
Check.lean must retain SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
The data import is separately replayed, not merely trusted by checking the
main theorem. The two sources are exact Git objects from PR31's recorded
head. Do not use the fork branch's older root base as the reference pin.

All final jobs and transfers were terminal when archived. No Wolfram
activation, login, live PowerToys configuration, or two-computer changes
are involved. Run `python -B verify_artifacts.py`, or add `--staged` before
publication, for exact selected-byte, scope, replay and prior-archive checks.
