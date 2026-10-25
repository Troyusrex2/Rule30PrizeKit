# Reproduce the finite experiments

Python3.12 and psutil5.9.8. The main searches and the independent verifier
need no NumPy, GPU, Wolfram account, Lean installation or network. The optional
SMT search uses the existing z3-solver5.3.1 package; change its local sys.path
line to your installation. Its timeout results are not proofs.

From a COPY of work/, run one job at a time:

    python -X utf8 -B guard.py source_profiles.py
    python -X utf8 -B guard.py source_observer.py
    python -X utf8 -B guard.py observer_generic.py
    python -X utf8 -B guard.py observer_stress.py
    python -X utf8 -B guard.py observer_adversarial.py
    python -X utf8 -B guard.py observer_smt.py
    python -X utf8 -B guard.py verify_observers.py

Every command rewrites its own output files; use a copy to retain the frozen
manifest. The stress set is time-budget dependent; completed cases have exact
certificates, while an unstarted case says nothing. The original run completed
33 cases in298.8seconds. The SMT witnesses and timing can differ across runs.
refresh.py records the original public API snapshot and references the previous
private snapshot path; it is provenance, not needed for the math checks.

From this archive itself, `python -B verify_artifacts.py` is read-only and
checks exact hashes, metadata, Python syntax, all saved certificates backward
and all six solver witnesses. `--staged` reads the actual Git index blobs.
The 600 earlier selected artifact hashes are checked during preparation and
remain immutable; those proofs are not counted again as new results.
