# Reproduce

Use a disposable official kit checkout at
`5473ffd075f63c9d626e63b8455805d4831b39ca` with Lean4.35.0.
Keep `Check.lean` unchanged; SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
The fork branch's root base is older, so copy the five archived research
sources into the pinned checkout, not into its older root environment.

Build official dependencies normally. Build CommonPast, OrClockObserver,
ClockJet, ClockMode, then ModeClockRigidity. The four dependency sources
are byte-identical to the previous archive, which retains their complete
current-pin replay reports. Then:

```text
lake env lean -o .lake/build/lib/lean/Rule30ModeClockRigidityResearch.olean Rule30ModeClockRigidityResearch.lean
lake env lean --run Check.lean Rule30ModeClockRigidityResearch --claim partial --headline Rule30ModeClockRigidityResearch.mode_readout_no_half_clock --headline Rule30ModeClockRigidityResearch.actual_lower_readout_no_half_clock
```

The archived replay script records the actual G913 paths and commands.
Use the complete kernel replay, not only an axiom check.

In a copied work directory with Python and psutil:

```text
python -B guard.py mode_unrestricted_mask_probe.py
python -B guard.py mode_clock_controls.py
python -B guard.py mode_genuine_local_inverse.py
python -B guard.py audit_genuine_local_collision.py
```

The other scripts reproduce the additional finite searches. No dependency
installation or live computer changes are required. Keep per-owned-job
limits 300 seconds, 8 GiB RSS, 2 GiB system free. Every archived job is
terminal. The finite-strip witnesses have unconstrained oldest-two cells;
they do not establish actual finite white ancestry.

`python -B verify_artifacts.py` audits selected bytes, scopes, complete
checker JSON, dependency hashes and all older immutable archives.
Add `--staged` to check actual Git index bytes before publication.
