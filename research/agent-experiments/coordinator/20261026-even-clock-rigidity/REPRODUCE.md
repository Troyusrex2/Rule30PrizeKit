# Reproduce

Use a disposable checkout of official kit commit
`5473ffd075f63c9d626e63b8455805d4831b39ca` with its Lean 4.35.0 toolchain.
The fork branch's root base is older; copying this archive into a fresh
pinned checkout is required. Keep `Check.lean` unchanged, SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

Build the official dependencies normally. Copy the five research sources
from `work/` to the checkout root. In order, build and run the complete
unchanged partial checker on CommonPast, OrClockObserver, ClockJet,
ClockMode, and EvenModeRigidity. For example, after dependencies:

```text
lake env lean -o .lake/build/lib/lean/Rule30EvenModeRigidityResearch.olean Rule30EvenModeRigidityResearch.lean
lake env lean --run Check.lean Rule30EvenModeRigidityResearch --claim partial --headline Rule30EvenModeRigidityResearch.actual_even_plateau_or_clock_rigidity
```

The archived `replay.py` records the six headlines and actual direct-Lean
commands used on G913, with the explicit owned project path. Adapt paths
only for a disposable local checkout. Replay every declaration, not just
an axiom list. Existing dependency reports are retained with exact hashes.

For the external audit, copy the unmodified `Rule30CoupledGerms.lean` to
`lean/Ruliology/CellularAutomata/Rule30CoupledGerms.lean` in that disposable
checkout, build its official dependencies and the module, then run
`Check.lean Ruliology.CellularAutomata.Rule30CoupledGerms --claim partial`
with its seven headlines listed in `replay_external_germs.py`.

Python controls, in a copied `work/` directory with psutil available:

```text
python -B guard.py even_mode_controls.py
python -B guard.py audit_mode_witnesses.py
```

The producer `mode_coordinates.py` also needs NumPy. It repeats the finite
graph/linear algebra experiment; the independent audit needs no NumPy.
Keep 300 seconds, 8 GiB owned RSS, and 2 GiB system free per job. Do not
increase limits silently. G913 used Python 3.13/NumPy 2.4.6; the independent
witness audit and controls used local Python 3.12. All jobs were terminal
when archived. No Wolfram activation, cloud authentication, live computer
configuration, or two-computer setup is needed for this checkpoint.

Run `python -B verify_artifacts.py` to check the archive's exact selected
bytes, complete replay reports, scope and immutable prior archive hashes.
`--staged` checks the actual Git index bytes before publication.
