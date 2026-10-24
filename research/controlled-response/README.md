# Controlled right-half responses and finite-support limits

This contribution contains two core Lean modules, developed by Troy Lowry with
OpenAI Codex. Problem 1 remains open. No literature-priority claim is made.

`Rule30ControlledResponseResearch` characterizes equal head responses to **all**
left-boundary inputs by head and first-two-cell OR observations of the triangular
map `Q(x)(k) = x(k) XOR (x(k+1) OR x(k+2))`. It proves that terminal `011 -> 01`
and `101 -> 11`, followed by zero tails, preserve responses behind every common
finite prefix. The result remains sound with actual whole-line feedback: every
common initial left half, including the center, stays equal at every later time.
For example, finite starts black only at positions `{2,3}` and `{2}` have the
same complete center trace, despite different right edges.

The module also separates finite-horizon agreement and agreement under a
single driver from universal response equivalence. It does not prove a complete
finite-tail normal form or recover a left edge from a center trace.

`Rule30PeriodicProfileCounterResearch` supplies three explicit infinite tails.
Two have period-eight diagonal orbits with the same nonconstant first-two-cell
OR trace and different head traces. The third has head least period two and
full-state least period eight. All are proved to have infinite support. Thus
neither a power-of-two temporal period nor a nonconstant OR observation replaces
the finite-support hypotheses in proposed reconstruction arguments. No finite
conjecture is refuted and no eventual center period is excluded.

The [review essay](controlled-response-essay.md) embeds the exact standalone
proof; the [evaluated notebook](controlled-response-essay.nb) carries that source
and its full LeanLink replay. The [diagram](profile-counter-figure.png) is
exported from its saved output. The notebook has not been sent to the prize API.

Validation records:

- [Catalog build and replay](catalog-verification.json): the standalone core
  catalog is built in dependency order, then every declaration in both new
  modules is replayed with the unchanged checker.
- [Pinned standalone replay](standalone-verification.json): all 203 declarations
  and 18 selected headlines pass at kit commit `cc1e0e0`, with standard axioms.
- [Fresh-kernel notebook inspection](controlled-response-essay.nb.verification.json):
  exact saved source, all declarations replayed, standard headline axioms,
  zero message cells, and independently checked computation outputs.
- [Wolfram controls](wolfram-independent-controls.json): 104 full Rule 30 rewrite
  experiments and 792 scalar cells in three profile cones.
- [Python response controls](controlled_response_controls.json): exact response-tree
  partitions compared with the nonbranching signatures at widths 1 through 7
  and horizons 1 through 20.
- [Profile discovery and controls](periodic_profile_counter_controls.json):
  independent integer evolution checks 12,288 cells. The finite search is not
  a premise of the unbounded Lean proof.

Reproduce with Lean 4.35.0, Python with `psutil`, and Wolfram with LeanLink:

```text
python research/controlled-response/verify.py --lake /path/to/lake
python research/controlled-response/generate_essay.py
python research/controlled-response/verify_standalone.py --project /path/to/pinned-kit --lake /path/to/lake
python research/controlled-response/controlled_response_controls.py
python research/controlled-response/periodic_profile_counter_controls.py
```

Set `RULE30PRIZE_KIT` to the prepared reference kit and evaluate
`build-notebook.wl` in a fresh Wolfram kernel. It builds without cached outputs,
replays all declarations, checks each computation output, and verifies that the
saved notebook retains the exact standalone source. It makes no submission call.
