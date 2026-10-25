# Reproduce the complete bridge

Use a fresh writable copy of work. Do not rerun scripts in this immutable
archive. Prepare Lean 4.35.0 and the compiled reference kit at 3eca23c0a9fa6b153313655e6d51835406c2d06e.
Edit only local path variables in your copy of replay.py; create
owned-verifier/owned-build and copy the unchanged official Check.lean to
owned-verifier. Python 3.12.3 and psutil 5.9.8 were used.

```
python -B guard.py replay.py Rule30DyadicSourceResearch selected_event_iff_outer
python -B guard.py replay.py Rule30LucasMaskResearch choose_odd_submask
python -B guard.py replay.py Rule30SourceSeriesResearch center_source_sum kernel_coeff row_succ
python -B guard.py replay.py Rule30DyadicSourceSumResearch center_eq_one_add_deep_sources shallow_sum shallow_term_eq
python -B guard.py green_controls.py
python -B guard.py deep_channels.py
```

The source-series module depends on the first module; the sum module depends
on both the series and Lucas modules. Rebuild in that order. The final raw
reports record exact commands, source hashes, pin, checker hash and all
headline and replay verdicts. Saved-artifact verification checks hashes and
scope only; it does not replace Lean's full kernel replay.

The separate core port is reproduced using prepare_catalog.py on a fresh
worktree from the same pin, followed by check_catalog.py under guard. It
changes exactly the new catalog module, public import and README table row.
It is the same core mathematics as the preceding source module, not 56 more
independent mathematical results.
