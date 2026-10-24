# Sampling a gap score at rising-edge returns

Troy Lowry with OpenAI Codex, 2026-10-24. **Problem 1 remains open.**
These files contain candidate falsification and exact arithmetic controls,
not Lean-verified proofs or an accepted ranking function.

## The relaxed condition

The previous gap-score obstruction concerns a one-step descent condition.
Here the potential may increase inside a black or white run. Sample it only
when both center traces make a common `0 -> 1` transition, and require a
strict decrease between consecutive such occurrences. The traces must agree
at **every tick** through the second endpoint's next tick.

A hypothetical natural score satisfying this unbounded condition would
still be useful for the full problem: a nonzero finite start cannot have an
eventually constant center, hence has infinitely many rising edges. An
infinite sequence of strict decreases is impossible. This is the motivation
for the experiment; no new conditional Lean theorem or unbounded descent
proof is claimed here.

The score uses the same gap features as
[`paired_gap_rank_probe.py`](paired_gap_rank_probe.py). Both endpoints have
center color zero, so only its 391 center-zero features can be active. The
coefficient vector is shared across lags. This changes the timing of the
descent requirement, rather than increasing a local pattern window.

## Failed fit and exact obstruction

The initial sample contains 34 actual seed restart returns at times below
1,024. A fitted score passes that training set but fails on **101 of 183**
later returns at seed times 1,024 through 4,095. That later batch is then
explicitly promoted to training; it is not retained as independent evidence.
The resulting 217-return system is infeasible in this specified cone.

An exact reconstructed certificate uses **100** positive integer
multipliers. Its selected seed times lie between **14 and 4,073**, with lags
`2,3,4,8,16,32,64,128` and return durations two through six. Every weighted
feature increment is nonnegative, while the weighted unit descent charge is
strictly positive. Thus no nonnegative combination of these fixed features
can satisfy all selected return inequalities.

[`verify_return_gap_diagnostics.py`](verify_return_gap_diagnostics.py) uses
only the Python standard library. It rebuilds the actual seed orbit cell by
cell, verifies every time-shift relation, checks both traces at every tick,
and confirms that the two rising edges are consecutive. It independently
recomputes the maxima with scalar scans and Kadane's recurrence. All gains
and charges agree exactly. See the
[arithmetic audit](return-gap-diagnostics-check.json) and
[saved certificate](seed-return-gap-rank-probe.json).

The [Wolfram control](wolfram-return-gap-check.json), from
[`return-gap-check.wl`](return-gap-check.wl), independently evolves both finite
rows in every return: **200 builtin space-time frames and 3,899,160 cells**.
All intermediate observations, both macro endpoints, the consecutive rising
edges and all weighted feature gains match. The Python audit verifies the
seed-orbit provenance; this Wolfram calculation checks the finite frames.
Neither calculation is Lean kernel verification.

## Limits of the conclusion

This rejects the fixed nonnegative gap-feature cone even after allowing
temporary increases between rising edges. It does not reject all return
ranks, lag-dependent coefficients, nonlinear compositions, or the prize
statement. Enlarging the sample cannot repair the already certified
obstruction for this cone.

The same certificate also obstructs a finite lexicographic list of
nonnegative linear forms in these features. Take the first coordinate that
changes on any selected return. Its increments are nonpositive on all
selected returns and negative on at least one, so their positive weighted
sum is negative. The nonnegative aggregate feature increments force that
sum to be nonnegative. This deduction from the arithmetic certificate has
not been separately formalized in Lean.

## Reproduction

Discovery uses NumPy, SciPy and SymPy; the saved-certificate audit needs only
the standard library:

```powershell
python research/overnight/paired_return_rank_probe.py --refine-once --output research/overnight/seed-return-gap-rank-probe.json
python research/overnight/verify_return_gap_diagnostics.py --certificate research/overnight/seed-return-gap-rank-probe.json --output research/overnight/return-gap-diagnostics-check.json
```

In Wolfram, load `return-gap-check.wl` and evaluate `returnGapReport[]`.
