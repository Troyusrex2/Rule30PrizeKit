# Reproduce the proof and experiments

Audit bytes with `python -B verify_artifacts.py`; add `--staged` to check
actual index blobs. Run all writing scripts in a scratch copy, not here.

Use the reference kit at3eca23c0a9fa6b153313655e6d51835406c2d06e with Lean4.35.0
and compiled official imports. Copy the two `work/*.lean` modules into an
owned project/build directory. Compile `Rule30BlockRowsResearch` first, then
`Rule30CausalBlockRankResearch`, with the build directory on LEAN_PATH:

```
lake env lean -o <build>/<Module>.olean <Module>.lean
lake env lean --run Check.lean <Module> --claim partial --headline <headline>
```

Exact headlines, commands, source/checker hashes and raw output are in
`work/evidence/<Module>`. `replay.py` retains original Windows paths for
provenance; adapt paths in your scratch copy or use direct commands. The data
module imports official `Rule30Equivalents.IntegerRows`; the rank module also
imports Mathlib's preorder definitions. The final headline is
`Rule30CausalBlockRankResearch.no_causal_block_rank` and
`Rule30CausalBlockRankResearch.no_causal_block_rank_type_one`. The generic
universe-polymorphic theorem is replayed but cannot be a headline under the
unchanged checker; fixed-universe wrappers meet that existing requirement.
The replay wrapper clears any stale report before starting, so a failed run
cannot leave an earlier pass report at the same path.

The generator `generate_block_rows.py` consumes `block-cycle-witnesses.json`.
It supplies integers and ordinary proof code; the checker verifies every jump.
No generation algorithm, finite simulation, solver status or graph search is
trusted by the final theorem. The one mistaken sibling halo in the initial
draft was corrected from the actual row before the passing replay.

Python experiments use3.12.3, psutil5.9.8 and task-local Z3 5.3.2.0. The Z3
scripts retain the earlier private `solver-deps` import path; adjust that path
to your own install in a scratch copy. No solver binary is included. Run the
corrected search, extract the cycle and regenerate rows, in that order:

```
python -B guard.py block_rank_distinct_onsets.py
python -B guard.py extract_block_cycle.py
python -B generate_block_rows.py
```

The prototype `block_rank_search.py` has overlapping canonical states in its
training/test partition; its figures are diagnostic only. The earlier scans
also count repeated T,t representations, not unique onset states. Use the
distinct-onset script for the reported independent held-out test. The supplied
core is recorded, but Z3 may return a different valid core on another run;
the Lean source checks the fixed eight-event cycle independently.

Every final job used300-second,8GiB owned-tree RSS,2GiB minimum free RAM and
0.1-second sampled guards. Only owned processes may be stopped. The first row
replay used a plain `replay` guard label; its terminal guard/log were copied
into the module evidence before later jobs, then labels were made module-specific.
No running job or another agent's work was overwritten.
