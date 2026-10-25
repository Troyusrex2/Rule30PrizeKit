# Reproduce

This checkpoint contains finite Python experiments, not new Lean proofs.
Python 3.12 and psutil 5.9.8 suffice; no GPU, Wolfram sign-in or prize API is used.
The source of the saved public metadata is identified in REPORT.md and the JSON
files. The external Lean source is archived for provenance, not adopted here.

Copy `work/` to a scratch directory before running producers, which rewrite
their own result files. The ordinary guard is 300 seconds / 8 GiB owned RSS /
2 GiB minimum system available memory. Each command below must exit zero:

    python -B guard.py common_certificate.py
    python -B guard.py deadline_probe.py
    python -B guard.py deadline_certificates.py
    python -B guard.py history_control.py
    python -B guard.py centered_geometry_control.py
    python -B guard.py inverse_geometry_control.py
    python -B guard.py verify_common.py
    python -B guard.py verify_inverse.py

The source copy includes observer_core.py for the earlier single-gauge controls;
zero_forcing.py and joint_gauge.py can be run under the same guard. Their
historical sibling-directory search is optional: Python also finds the included
same-directory module. No predecessor archive is needed for the mathematics.

The independent common verifier imports no producer or packed evolution.
The independent inverse verifier enumerates complete initial words directly,
without using inverse reconstruction or parallel bit planes. The first checks
1,120 canonical certificates at 820 distinct pairs, 11 controls and 1,123 deliberately
corrupted positive certificates; the second exhausts 57 inverse cases.

From the archive directory, `python -B verify_artifacts.py` is read-only: it
checks every selected byte hash, Python syntax, JSON structure, exact saved
checks, guards and scope flags. With --staged it reads the actual Git index.
This integrity audit does not substitute for the independent mathematical
replays above. No claim of full or partial Lean verification follows from it.
