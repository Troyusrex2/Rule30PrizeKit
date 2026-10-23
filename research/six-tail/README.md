# Backward vacuum obstructions

The generic `Rule30BackwardVacuumResearch.no_padding_of_backward_certificate`
theorem is kernel-checked in the catalog checkout and the pinned reference kit.
It excludes an eventual word `0^r u` whenever a finite predecessor chain from the
vacuum along `0^N u` ends in the empty set, and

```
r >= max(N, 10*length(u)+11, K+9*(length(u)+1)).
```

It applies to every column of every configuration with a leftmost black cell.
Unlike the forward pumping method, this criterion does not require a stabilized
reachable set. It uses the existing analytic white-pulse reduction.

## Six-bit theorem: kernel verified

`Rule30SixTailSharpenedResearch.no_six_tail_leftFinite` excludes eventual `0^r u`
for every `length(u) <= 6` and `r >= 74`, at every column of every configuration
with a leftmost black cell, after every transient. This covers all nonzero finite
starts and the single seed. Earlier bounds 69 for five bits and 49 for four bits
remain available. No optimality is claimed.

All 162 research modules in its dependency chain compile in the catalog and the
pinned kit `cc1e0e0e7c1ae8c971aec5c14aaabb47c7b8c554`. Catalog declarations were
replayed through unchanged `Check.lean`. The pinned run compiles the 48 inherited
research modules and replays the 114 added modules where they contain declarations.
Only module-system wrappers change for that older kit; source bodies are identical.
Import-only modules have no declarations to replay. Data-only modules pass kernel
replay and introduce no axioms; their expected missing-headline exit is recorded
separately, not treated as a submission verdict. All three final theorem headlines
pass in both runs. Exact reports and source hashes are in `evidence/catalog` and
`evidence/pinned`.

The sixteen basic backward certificates give a uniform bound 77. Endpoint
restrictions for `110001` and `111101`, using the existing restricted backward-tube
criterion, reduce this to 74. Rotation and the prior five-tail theorem handle all
shorter and white-ended tails.

The computational facts below have already been checked independently:

- Every predecessor set in [certificates.json](certificates.json) was reconstructed
  by a cellwise Boolean implementation, covering 889,216 transition cases.
- Three negative controls retain vacuum predecessors: removing one needed white
  step, decreasing the width, and using the earlier exceptional tail `10101`.
- Wolfram's free remote evaluator, version 15.0.1, independently encoded the finite
  transition histories as Boolean satisfiability problems. All sixteen positive
  cases were unsatisfiable; the one-shorter white run was satisfiable. Exact code
  and returned results are in [evidence/wolfram](evidence/wolfram/).

These remote Wolfram computations are exploratory cross-checks. They are not a
Wolfram prize-verifier verdict, an evaluated LeanLink notebook, or an API submission.

![Backward predecessor sets for 110001 at width fourteen](backward-obstruction.png)

The graph starts at the vacuum and runs backward through the six pulse bits and
then fourteen white steps. The predecessor sets become empty at the last step.
The largest stored set has 68 states. The finite completeness checks nevertheless
consider all 16,384 strips and both possible right inputs.

## Reproduce the computations

From the repository root:

```sh
python tests/check_six_tail_backward_research.py
python tests/check_six_tail_endpoint_research.py
python research/six-tail/generate.py
python research/six-tail/generate-endpoints.py
python research/six-tail/verify.py --lake /path/to/lake --target Ruliology.CellularAutomata.Rule30SixTailSharpenedResearch
python research/six-tail/wolfram-crosscheck.py --width 14 --padding 14 --word 110001
python research/six-tail/wolfram-crosscheck.py --width 14 --padding 13 --word 110001
```

The generator writes Lean data modules whose predecessor implications are checked
with `decide +kernel`. It is a search/data-export tool, not a proof oracle. The
Wolfram script sends only this public mathematical model to the free remote
service; it uses no Wolfram ID and performs no prize submission.

The endpoint test checks both closed white sets, forward and backward transitions,
and forced bits, and rejects a wrong-bit negative control.

`prepare-pinned.py PATH --target Ruliology.CellularAutomata.Rule30SixTailSharpenedResearch`
copies the dependency chain to a separate pinned worktree. Use `verify.py --kit PATH
--output PATH` there; omitting `--build-only-base` replays inherited modules too.

The [standalone proof](Rule30SixCoreStandalone.lean) covers all sixteen new six-bit
black-ended cores at bound 74. It omits the older five-tail chain, so its headline
is **not** the complete length-at-most-six theorem. All 940 declarations were
separately replayed in the pinned kit. The [essay source](Rule30-Six-Core-Notebook.md)
embeds that exact proof. Its exact embedded source, including the required
`import Rule30PrizeKit`, separately passes a root-project build and unchanged
checker replay (939 local declarations); see `evidence/notebook-source`. The
difference is the helper `Rule30Realization.seed.eq_1`, already provided by the
root import. `bundle-core.py` rebuilds both artifacts without changing the checked
proof, and `tests/check_rule30_notebook_sources.py` checks both essays against
their recorded exact-source hashes.

To build it in a fresh activated Wolfram kernel, first evaluate the official
`HowToStart.md` starter essay as the agent workflow requires. Then set
`RULE30PRIZE_KIT` and `RULE30_NOTEBOOK_CONFIG` to the prepared kit and this directory's
`notebook-config.json`, then run `../forbidden-suffix/build-notebook.wl`. The builder
requires actual LeanLink kernel checks before writing a verification report and
never submits to the prize API. No notebook has yet been built or evaluated here.

Research and formalization: OpenAI Codex through `Troyusrex2`, building on the
earlier white-pulse, strip, and uniform Jen results. All results remain partial;
period two and the full prize questions are unresolved.
