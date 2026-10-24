# Nonlocal rank experiments and a verified finite constructor

Troy Lowry with OpenAI Codex, 2026-10-24. **Problem 1 remains open. No rank
was proved. No result in these numerical files is a Lean premise.**

The existing `Rule30PairedTraceResearch.problem1_of_flipRanking` proves a
conditional route to the exact official Problem 1. A natural rank on pairs
of finite rows with strictly nested support edges would suffice if it never
increased while the centers agreed and dropped at each common color change.
This experiment investigates nonlocal features, rather than enlarging the
previous local pattern windows.

## Kernel-verified contribution

[`Rule30FinitePackedTraceResearch`](../../lean/Ruliology/CellularAutomata/Rule30FinitePackedTraceResearch.lean)
connects the explicit packed inverse to the catalog's realization and
locality theorems. For every natural `N`, every desired temporal trace `c`,
and every fixed bounded initial right half `R`, `packedConf R c N` is a
finite initial configuration whose actual center agrees with `c` through
time `N`. It preserves the prescribed right half. Its left half is white
past depth `N`.

The realization principle was already in the catalog. The contribution is
the algorithmic bridge and its soundness, including the truncation endpoint.
It constructs neither a finite row with an infinite alternating trace nor
a prize counterexample. The working and pinned unchanged checkers each
replay **35 declarations** and all ten selected headlines:

- [Working report](finite-packed-trace-evidence/catalog/report.json).
- [Pinned report](finite-packed-trace-evidence/pinned/report.json).
- [Reproducer](verify_finite_packed_trace.py), including dependency source
  checks and refusal to overwrite a different pinned proof source.

## Exact coordinates

Bit `k` is at physical position `lo+k`. After a full step the packing origin
is `lo-1`, and

```text
F(a) = (a << 2) XOR ((a << 1) OR a).
```

The pair alphabet is `(outer_bit + 2*inner_bit)`. Nested support edges do
not imply cellwise set inclusion. For an exact lag `P` restart pair, the
packed outer is `F^P(row)`, the aligned inner is `row << P`, and the center
index is shifted by `P`. The lag relation is preserved after each step.
The scripts check these conventions against independent scalar evolution
and the catalog's opposite packing convention.

## What the diagnostics reject

The initial 292 natural features comprise regional letter counts, ordered
pairs at arbitrary distances with distance powers zero through two, and
fixed prefix-count squares. A seven-case **exact integer** dual rejects
this nonnegative feature cone on valid nested pairs. Those seven cases
are not restart pairs, so that obstruction is not substituted for one on
the seed orbit.

The broader conic model permits any positive semidefinite quadratic form
in each of four directional regional prefix-count vectors and a whole-row
count vector, together with the 252 nonnegative count/moment features.
A 65-case exact certificate rejects that five-block cone on actual lag-two
restart pairs. A separate **149-case exact certificate on the single-seed
orbit** rejects its color-dependent extension (ten Gram blocks). Every
chosen case satisfies the current and next center equalities required by
the proposed descent condition.

For each certificate, nonnegative integer multipliers combine the feature
increments into nonnegative linear gains and positive semidefinite Gram
gains while the weighted flip reward is positive. Hence the inequalities
cannot all hold for this specified cone. The saved principal minors are
recomputed in exact arithmetic; no solver status is treated as a proof.
[`verify_nonlocal_diagnostics.py`](verify_nonlocal_diagnostics.py) checks
the chosen rows, head conditions, restart/seed relations, all gains, and all
principal minors without invoking an optimizer. See
[its report](nonlocal-diagnostics-check.json).

These exact-arithmetic checks are **not Lean verified**. They reject these
feature cones, not all possible ranks or any prize statement. Independent
Wolfram `CellularAutomaton[30,...]` controls compare 644 seed rows covering
414,736 cells and reconstruct all ten weighted Gram matrices exactly:
[source](nonlocal-seed-check.wl), [report](wolfram-nonlocal-seed-check.json).

## Why the strongest fitted model was rejected

Regional global squares, radial prefix squares, and 336 run features escape
the preceding certificate. A color-dependent model with 1,484 variables
eventually fitted 1,180 actual lag-two restart transitions and passed both
frozen batches of 512 random pairs used in refinement. Those batches had
become training data; this was never an independent generalization proof.

The finite constructor produces starts with center alternation of arbitrary
prescribed finite length. The fitted model fails on those starts, with
increasing residuals at longer depths. A second model trained on 1,327
pairs, now including empty-right-half structured starts, passes the same
random batches but fails on independent structured starts with initial
right words `1,3,5,17,255`. See
[empty-right validation](restart-regional-structured-validation.json) and
[varied-right validation](restart-regional-structured-right-validation.json).
Neither fitted model is accepted. Small negative floating coefficients and
eigenvalues also preclude treating either as an exact natural rank.

Every structured start is forward checked through its entire prescribed
prefix before evaluating a rank. Eight separate builtin Wolfram cones,
with depths 16 through 256 and varied right halves, independently confirm
the packing and all requested center bits:
[source](structured-start-check.wl),
[cases](structured-start-cases.json),
[report](wolfram-structured-start-check.json).

## Reproduction and limits

Run `python research/overnight/verify_nonlocal_diagnostics.py` from the
repository root. The arithmetic audit uses NumPy, SciPy and SymPy. SDP
discovery scripts additionally use Clarabel 0.11.1; see its official Python
cone conventions. Nothing requires changing Wolfram authentication or
system configuration. The Wolfram controls are functions in their `.wl`
files; load each file, then evaluate its report function.

To replay Lean, run `verify_finite_packed_trace.py --lake <lake.exe>` and
again with `--project <pinned-project>`. The second project needs the exact
verified dependencies already present, as checked by the runner.

Solver errors, iteration limits, and failed rational reconstruction stay
unknown. The wider run-only cone is numerically infeasible on one finite
batch, without an exact certificate. The regional SDP resume option reads
one parent's added general finite-row counterexamples; it does not recover
an entire multi-generation training history. Do not resume the structured
report alone and assume that ancestral cases have been restored.

The remaining gap is an all-length descent or another structural argument
for every possible eventual period and transient. No finite training fit,
random validation batch, finite prefix realization, or bounded-period check
fills that gap.

A later [gap-maximum experiment](paired-gap-rank-notes.md) accounts for white
gap lengths using prefix, suffix and subarray maxima. Exact arithmetic
certificates reject that fixed nonnegative cone even on actual single-seed
restart pairs. It does not repair the one-step descent condition, and it
does not rule out ranks sampled at longer return intervals.
