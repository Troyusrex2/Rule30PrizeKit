# Gap maxima do not supply this one-step rank

Troy Lowry with OpenAI Codex, 2026-10-24. Problem 1 remains open. These are
exact arithmetic diagnostics, **not Lean-verified proofs or prize claims**.

## Candidate and motivation

The verified `Rule30PairedTraceResearch.problem1_of_flipRanking` gives a
sufficient condition for the complete official Problem 1. A natural-valued
score on nested finite rows must never increase when the current and next
center observations agree between the rows, and must decrease at each common
color change. Neither that score nor its existence has been proved.

The earlier sparse construction shows that such scores must account for
arbitrarily long white gaps, even with only five versus three initial black
cells. The present candidate does so without another fixed local window.
Encode a spatial cell by `outer_bit + 2*inner_bit`, retaining the white gaps
inside the outer support edges. For each of the 65 nontrivial charge vectors
in `{-1,0,1}^4`, compute the maximum prefix sum, suffix sum and contiguous
subarray sum separately on each side of the center. The empty interval is
allowed, so every maximum is nonnegative. Directions without a positive
coordinate would contribute only zeros and are omitted.

This gives 390 features and a constant for each center color, or 782 features
altogether. Positive charges on the `00` symbol make these features sensitive
to arbitrarily long white gaps. The coefficient vector is shared across
restart lags. A nonnegative rational combination could be scaled to a
natural-valued score, but no combination works in this specified cone.

## Exact checks

`paired_gap_rank_probe.py` discovers the following obstructions. Its integer
features pass 40 direct-subarray controls, and the packed update passes 80
independent cellwise controls. Floating optimization proposes a dual support;
an exact linear solve then reconstructs and checks the multipliers.

| Transition domain | Training transitions | Positive-weight certificate terms | Result |
|---|---:|---:|---|
| General nested support edges | 1,912 | 67 | Exact arithmetic obstruction |
| Actual finite-row restart pairs | 1,470 | 118 | Exact arithmetic obstruction |
| Actual single-seed restart pairs | 369 | 87 | Exact arithmetic obstruction |

The final certificate uses actual seed times between 1 and 255 and lags
`2,3,4,8,16,32`. Thus the failure is not explained solely by arbitrary nested
pairs or by starts unrelated to the seed.

For each selected transition let `d` be the new minus old feature vector and
`r` its common color-change indicator. The saved nonnegative integer
multipliers give componentwise nonnegative `sum(weight*d)` and strictly
positive `sum(weight*r)`. A nonnegative coefficient vector would therefore
make the weighted descent inequalities contradictory. The arithmetic check
does not use an optimizer or its infeasibility status as a premise.

[`verify_gap_diagnostics.py`](verify_gap_diagnostics.py) independently
reconstructs every feature using scalar scans and Kadane's subarray recurrence,
evolves the rows cell by cell, verifies nested **edges** rather than cellwise
containment, checks current/next center agreements, and checks every restart
relation. For the seed certificate it rebuilds the actual seed orbit and
checks its times and packing origins. All gains and rewards match exactly.
See [the arithmetic audit](paired-gap-diagnostics-check.json) and the three
saved certificates: [nested](paired-gap-rank-probe.json),
[restart](restart-gap-rank-probe.json), [seed](seed-gap-rank-probe.json).

An additional [Wolfram control](wolfram-paired-gap-check.json), using
[`paired-gap-check.wl`](paired-gap-check.wl), passes on all 272 certificate
terms: 544 builtin one-step Rule 30 rows, 87 actual seed restart cases, and
all weighted feature gains and rewards. The initial Wolfram harness omitted
the packing offset when automatic cropping removed leading white cells.
Restoring that known origin fixes the harness; explicit leading-white
controls also pass. No Python certificate or mathematical target changed.

This rejects these 782 fixed features with nonnegative coefficients and a
one-step descent condition. It does not reject all nonlocal ranks, signed
scores with a separate positivity proof, lag-dependent coefficients,
multi-stage ranks, or the prize statement. No result in these files is used
as a Lean premise. Increasing the fitting horizon cannot repair this cone's
exact obstruction.

A subsequent [return-time experiment](return-gap-rank-notes.md) permits the
score to rise between consecutive common rising edges. A separate exact
certificate rejects this fixed feature cone under that relaxed condition too.

## Reproduction

From the repository root, discovery uses NumPy, SciPy and SymPy:

```powershell
python research/overnight/paired_gap_rank_probe.py --domain nested --output research/overnight/paired-gap-rank-probe.json
python research/overnight/paired_gap_rank_probe.py --domain restart --output research/overnight/restart-gap-rank-probe.json
python research/overnight/paired_gap_rank_probe.py --domain seed --output research/overnight/seed-gap-rank-probe.json
```

The saved-certificate audit needs only the Python standard library:

```powershell
python research/overnight/verify_gap_diagnostics.py --output research/overnight/paired-gap-diagnostics-check.json
```

In a Wolfram kernel, load `paired-gap-check.wl`, then evaluate
`pairedGapReport[]`. Both independent controls remain finite calculations,
not additional Lean proofs.
