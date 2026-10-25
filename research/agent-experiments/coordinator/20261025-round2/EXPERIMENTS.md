# Combined finite-history and future-phase model: final outcomes

These are **finite numerical model results**, not Lean impossibility proofs.
All nine runs are finished. No positive exact rational certificate was found.
The reader preserves the period-seven background, so the new absorbing-prefix
barrier alone does not explain these outcomes.

The model uses the actual finite-history transducer of depths d=2/3/4, a
1,110-state union reader for the fourteen phases of free periods 01, 011,
0111 and 01111, upcoming-free-bit energy phase of width K=2/4, and a future
guard of thirteen double steps. It retains entire moving fronts. Current/next
row delays are 2d and 2d+2; predecessor flush is 4(d+1), scored current flush
is 4d. Signed costs, phase offsets and uniform additive lower bounds are
allowed. There is no new formal Lean soundness bridge for this synthesis model.

## Native outcomes

| d | K | scale | Maximal-rate IPM, 90-second native limit | Fixed-positive-rate dual simplex, 600-second native limit |
|---:|---:|---:|---|---|
| 2 | 2 | 1 | optimum alpha=0, 7.571 s | not retried |
| 2 | 2 | 2 | numerical error (status 4), 47.919 s | timeout, no incumbent, 601.230 s |
| 3 | 4 | 1 | optimum alpha=0, 63.973 s | not retried |
| 3 | 4 | 2 | timeout, 96.481 s | timeout, no incumbent, 606.739 s |
| 3 | 4 | 3/2 | numerical error (status 4), 29.917 s | not retried |
| 4 | 2 | 1 | timeout, 101.977 s | infeasible (status 2), 183.097 s |

Times are model+solver elapsed time, so they can exceed the native solver limit.
See [case-summary.json](case-summary.json) and each raw case JSON for actual
statuses. A timeout or error remains unknown. Native zero/infeasibility is
not a kernel-checked theorem or an exact dual certificate.

Homogeneity permits rescaling any strictly positive rate to alpha=1, so the
retry fixes that bound and uses HiGHS dual simplex. It accepts a finite
positive incumbent even without an optimum only if rational reconstruction
satisfies **every original Fraction inequality and every variable bound**.
Neither timed-out retry returned an incumbent. The strict positive and
zero-cost negative calibrations are archived separately.

## Controls and resource bounds

Baseline controls passed 110,592 branch-language checks, 30,720 future-phase
partition checks, 51 shifted-phase checks, 51 reader-endpoint checks and 102
exact rational energy identities. Reverse growth is a positive calibration;
zero costs give the expected negative calibration. The configured-horizon
controls additionally passed 984 reconstructed/mutated path-language checks,
738 reader endpoints and 1,476 exact rational energy identities for actual
d=2/3/4, H=13, K=4, and scales 1, 3/2, 2, using a nontrivial eight-state reader.
These finite controls are not a universal semantic proof.

Baseline process guards: 300 seconds, 12 GiB tree RSS, minimum 16 GiB free.
Strict process guards: 900 seconds, same memory bounds. Two cases at a time.
All guards report normal completion. Baseline peak was 0.840 GiB; strict peak
1.018 GiB; minimum free memory across both was above 41 GiB. The unresolved
cases did not exhaust RAM. Recorded worker environment: Windows, Python
3.13.13, NumPy 2.4.6, SciPy 1.18.0. No wheel lock was captured.

## Sources and reproduction

`evidence/left-future-history-multi/` contains the exact seventeen-source
closure, source manifest, six case outputs, controls and guard summary.
`evidence/left-future-history-strict/` contains its eighteen-source closure,
three retry outputs and controls. Each original `sources.json` is retained
byte-for-byte. Configured controls and their raw log are in
`evidence/configured-controls/`. [artifacts.json](artifacts.json) hashes the
archive's actual bytes; verify these and each package's source manifest first.

In an isolated environment with the stated dependencies, from the baseline
package directory, examples are:

```
python left_future_history_controls.py
python left_future_history_cases.py --reader multi --depth 2 --memory 2 --scale 1
```

Run the identically named case entry point from the strict package directory
for a retry. It imports `left_future_history_strict_rank`. Copy the configured
control script to a **separate scratch copy** of either package and run it
there, so its imports resolve. Commands write outputs beside sources: preserve
the archived evidence and run only in scratch copies. Review scripts and use
explicit process/memory guards before running expensive cases. The archived
guard wrappers refer to the original worker installation; use your own guard
implementation rather than assuming those machine-specific paths exist.

## Decisions for the next round

The two scale-two models and fractional-scale error remain unresolved. Exact
dual witnesses or mathematically redundant cuts could improve their diagnosis.
Larger readers, different domains or right-coupled energies change the model
and need their own controls and proof interface. No candidate from these runs
currently supplies CQ01, Q01 or Problem 1.
