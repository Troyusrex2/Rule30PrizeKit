# Reproduction

Work in a fresh writable copy of work; do not rerun inside this immutable
archive. Use Lean 4.35.0 and the compiled reference kit pinned to
3eca23c0a9fa6b153313655e6d51835406c2d06e. Python 3.12.3 and psutil 5.9.8
were used. Edit only local path variables in replay.py and create the owned
verifier/build directories with an unchanged copy of the official Check.lean.

The replay runner reads the previously checked source-green build as a
dependency and writes only its own build outputs. For a completely fresh
rebuild, copy the four exact dependency-source files into your writable
root and first compile/check them in this order: DyadicSource, LucasMask,
SourceSeries, DyadicSourceSum. Set the runner's dependency path to that
owned build (or an empty directory once all four are in the main build).
The copied dependency reports show their previous full kernel replay;
they are not counted as new declarations in this batch.

```
python -B guard.py replay.py Rule30DyadicSourceResearch selected_event_iff_outer
python -B guard.py replay.py Rule30LucasMaskResearch choose_odd_submask
python -B guard.py replay.py Rule30SourceSeriesResearch center_source_sum kernel_coeff row_succ
python -B guard.py replay.py Rule30DyadicSourceSumResearch center_eq_one_add_deep_sources shallow_sum shallow_term_eq
python -B guard.py replay.py Rule30ReturnDepthResearch cut_bit_flip source_cut_window source_prefix_period
python -B guard.py replay.py Rule30ReturnSourcesResearch selected_event_iff_below_cut cut_layer_source cut_exceeds_exponent
python -B guard.py replay.py Rule30ReturnSumResearch center_eq_one_add_after_return returned_sum
python -B guard.py replay.py Rule30FirstReturnParityResearch center_after_even_return first_even_channel_odd all_ones_choose
python -B guard.py replay.py Rule30EchoProjectionResearch no_autonomous_profile initial_profiles_equal next_profiles_differ
python -B guard.py echo_operator.py
python -B guard.py echo_anf.py
python -B guard.py return_controls.py
```

The proof dependencies make the order of the first four new modules
significant. The echo projection module depends only on the carried core
source theorem and official CenterRuns. All final reports include the
source/checker hashes, reference pin, commands, headlines and full replay.
Artifact verification checks saved evidence and scope, not Lean proof terms.
