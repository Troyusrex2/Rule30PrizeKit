# Reproduction

Run `python -B verify_artifacts.py` in this archive. The `--staged` option
audits actual Git index blobs. Hashes authenticate bytes, not mathematical
truth. Reproduce computations in a scratch copy: they write output files.

Prepare the reference kit at commit
`3eca23c0a9fa6b153313655e6d51835406c2d06e`, with Lean4.35.0 and its official
compiled imports. Use an owned project/build directory and unchanged
`Check.lean`. Compile the six conservation modules in this order: Corner,
Word, Descent, Triviality, Cycle, Classification (all have the prefix
`Rule30Conservation` and suffix `Research`). Each imports only its predecessor
or the official statements. They do not depend on ancestry or earlier research.

For the greedy ancestry module, first compile CedarAncestry from the previous
round-two archive's received Cedar response, then
`Rule30RoundTwoAncestryFrontResearch` from that archive, then the new
`Rule30GreedyAncestryFrontResearch`.

For each module:

```
lake env lean -o <owned-build>/<Module>.olean <Module>.lean
lake env lean --run Check.lean <Module> --claim partial --headline <qualified-headline>
```

Add the owned build directory to LEAN_PATH. Exact headlines/commands/source
hashes are in `work/evidence/<Module>/report.json`. The supplied local replay
wrapper retains original paths for provenance; adapt those paths in a scratch
copy or run the direct commands above. No official checker edit is required.

The exact finite scripts need Python3.12 and psutil5.9.8 for `guard.py`.
The inverse scripts additionally need Z3 5.3.2.0 in `work/solver-deps` or an
equivalent adjusted import path. Run, from the scratch `work` directory:

```
python -B guard.py conservation_corner_controls.py
python -B guard.py greedy_front.py
python -B guard.py ether_greedy_cycles.py
python -B guard.py language_filtered_cycles.py
python -B guard.py coupled_language_cegar.py
python -B guard.py inverse_language_cones.py
python -B guard.py inverse_refined_candidate.py
```

Some original inverse scripts refer to the preceding private round-two work
directory. Supply the prior archive's corresponding JSON files there or adapt
only the input paths in a scratch copy. The final refined test and language
tests read this archive's own outputs. All final raw outcomes are archived,
including solver timeouts. Do not rerun immutable archives in place.

Resource guards:300 seconds,8GiB owned-tree RSS,2GiB available minimum,0.1s
samples. A reported RSS is a sampled peak. The supplied Python scripts and
solver conclusions are experiments, never proof dependencies. No additional
finite excluded word is claimed as a prize submission.
