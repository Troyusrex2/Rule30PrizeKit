# Reproduction

Run the experiment scripts in a fresh writable copy of `work`, not inside
this immutable archive. Python 3.12.3 and psutil 5.9.8 were used; no NumPy,
GPU, solver, or Wolfram account is needed for this batch.

```
python -B guard.py number_wall.py
python -B guard.py independent_controls.py
python -B guard.py source90.py
python -B guard.py dyadic_strip.py
python -B guard.py control_selected_events.py
```

For the Lean check prepare the official reference kit at
3eca23c0a9fa6b153313655e6d51835406c2d06e, Lean 4.35.0, and its compiled
imports. Edit only the local path variables in your copy of `replay.py`.
Create `owned-verifier/owned-build`, copy the unchanged official Check.lean
to owned-verifier, then run:

```
python -B guard.py replay.py Rule30DyadicSourceResearch selected_event_iff_outer source_dyadic_kernel_zero source_physical rule90_source_identity
```

The replay runner enforces checker SHA256
b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905.
It uses read-only reference imports and writes only owned build outputs.
The archive's `verify_artifacts.py` checks saved evidence and hashes; it is
not a substitute for Lean kernel replay. No full Problem1 theorem is claimed.
