# Reproduce finite experiments

First run `python -B verify_experiments.py`; `--staged` audits index blobs.
This is an integrity/outcome audit, not a Lean proof checker. No Lean source
or new kernel-verified theorem is part of this archive.

Work in a scratch copy. Scripts write outputs. The sources use Python3.12.3
with the package versions listed in REPORT. SMT sources point to the earlier
task's `solver-deps`; adapt that import path to your own Z3 install. The neural
source requires CUDA with at least2GiB free GPU memory. Other sources are CPU
only. All final data and coefficient tables are preserved for inspection.

From the scratch `work` directory, run each desired source with the supplied
guard, for example:

```
python -B guard.py global_block_search.py
python -B guard.py global_block_dominating_search.py
python -B guard.py global_block_incremental_search.py
python -B guard.py train_global_block_rank.py
python -B guard.py global_block_sum_search.py
python -B guard.py global_multiset_cone.py
python -B guard.py global_boundary_length_cone.py
python -B guard.py root_gap_potential.py
python -B guard.py root_small_control.py
python -B guard.py empty_trace_renewal_clock.py
```

Run `root_small_control.py` after its root-gap input exists. Every numerical
discovery must be revalidated with its exact integer routines. Changing
hardware or solver builds may change fitted weights/statuses; timeouts do not
become refutations, and the negative out-of-sample result for one table does
not exclude its whole function class.

The renewal binary contains262144 bytes, one0/1 byte per free bit, and its
SHA-256 is in the JSON report. It is generated directly from the empty right
half under the exact alternating boundary. The Z-array search covers all
lags at the specified selected onsets, not every possible onset/lag pair.
The clock measure is exactly2*(C-r-p), derived from the official
`free_bits_clock` endpoint convention.

Deduplication is by effective onset for unlabelled canonical pairs and by
onset/lag/root-cut for source-aware states. All training selection and final
integer-scale/model selection use the declared training range only. Held-out
failures are recorded without refitting against them.

The guards sample every0.1s and only manage the launched process tree. Limits
are300s,8GiB owned RSS and2GiB system available minimum. A sampled RSS is not
a guaranteed true peak. No other agent's work or earlier immutable archive
was modified.
