# Controlled right-half responses and finite-support limits

This contribution contains six core Lean modules, developed by Troy Lowry with
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

`Rule30FeedbackErasureResearch` strengthens the single-driver distinction to
actual feedback from finite configurations. Initial black sets `{1}` and
`{1,2}` have identical complete center and right-head traces, although their
initial right halves are not universally response equivalent. Their common
traces are proved not eventually constant, using the kit's existing finite
configuration theorem. The distinction is erased after one white-boundary
step. Both left edges are position 1, so left-edge recovery remains open.

`Rule30PeriodicProfileCounterResearch` supplies three explicit infinite tails.
Two have period-eight diagonal orbits with the same nonconstant first-two-cell
OR trace and different head traces. The third has head least period two and
full-state least period eight. All are proved to have infinite support. Thus
neither a power-of-two temporal period nor a nonconstant OR observation replaces
the finite-support hypotheses in proposed reconstruction arguments. No finite
conjecture is refuted and no eventual center period is excluded.

`Rule30ClockMaskResearch` proves a local positive obstruction: with even
half-clock H, a full 2H clock on one column, a color reversal after H on the
next, and H clocks on its next two neighbors, the first-pair OR cannot have
period H. One more predecessor cannot have period H either. Every update and
clock hypothesis is explicit. This does not extend the clock through an
arbitrary prefix or prove finite-tail period nonloss.

`Rule30FiniteClockCertificateResearch` supplies a generic soundness proof for
finite temporal-profile certificates. `Rule30FiniteClockSixteenResearch`
checks 68 profile pairs: for every finite triangular orbit with full clock
dividing sixteen, any eventual head period is a period of the whole state.
Spatial width and transient are unbounded, and the head period is arbitrary.
The bound on the full clock is explicit. This gives no arbitrary-clock
induction and excludes no vertical center-column period.

The [review essay](controlled-response-essay.md) embeds the exact standalone
proof; the [evaluated notebook](controlled-response-essay.nb) carries that source
and its full LeanLink replay. The [diagram](profile-counter-figure.png) is
exported from its saved output. The notebook has not been sent to the prize API.

Validation records:

- [Catalog build and replay](catalog-verification.json): the standalone core
  catalog is built in dependency order, then every declaration in all six new
  modules is replayed with the unchanged checker.
- [Pinned standalone replay](standalone-verification.json): all 345 declarations
  and 28 selected headlines pass at kit commit `cc1e0e0`, with standard axioms.
- [Fresh-kernel notebook inspection](controlled-response-essay.nb.verification.json):
  exact saved source, all declarations replayed, standard headline axioms,
  zero message cells, and independently checked computation outputs.
- [Wolfram controls](wolfram-independent-controls.json): 104 full Rule 30 rewrite
  experiments, eight actual-feedback examples, 792 scalar cells in three profile
  cones, 192 qualifying clock cases, ten additional built-in Rule 30 cones,
  and eight finite-clock certificate cones with 36,564 compared scalar cells.
- [Python response controls](controlled_response_controls.json): exact response-tree
  partitions compared with the nonbranching signatures at widths 1 through 7
  and horizons 1 through 20.
- [Finite-clock controls](finite_clock16_controls.json): every word below 2^14
  and 128 expanded words up to width 200 accompany the arbitrary-width proof.
- [Profile discovery and controls](periodic_profile_counter_controls.json):
  independent integer evolution checks 12,288 cells. The finite search is not
  a premise of the unbounded Lean proof.

Reproduce with Lean 4.35.0, Python with `psutil`, and Wolfram with LeanLink:

```text
python research/controlled-response/verify.py --lake /path/to/lake
python research/controlled-response/generate_essay.py
python research/controlled-response/verify_standalone.py --project /path/to/pinned-kit --lake /path/to/lake
python research/controlled-response/generate_finite_clock16.py
python research/controlled-response/finite_clock16_controls.py
python research/controlled-response/controlled_response_controls.py
python research/controlled-response/periodic_profile_counter_controls.py
```

Set `RULE30PRIZE_KIT` to the prepared reference kit and evaluate
`build-notebook.wl` in a fresh Wolfram kernel. It builds without cached outputs,
replays all declarations, checks each computation output, and verifies that the
saved notebook retains the exact standalone source. It makes no submission call.
