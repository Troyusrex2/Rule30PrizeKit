# Rule 30: the older boundary and finite observations matter

[REPORT.md](REPORT.md) separates new Lean theorems, Python discoveries, solver timeouts and remaining gaps. This archive extends the earlier edge-clock result; the combined module has99 constants/13 checked headlines, not99 additional constants.

The new exact results are:

- Free nonconstant older inputs permit arbitrarily deep recurrence-compatible strips ending in a genuine period-eight/period-two template pair.
- Genuine finite odd initial codes imitate that pair for arbitrarily long finite windows. No all-time period drop of those finite codes is asserted.

## Fresh Lean replay

```text
python canonical/verify.py --lean /absolute/path/to/lean.exe --out /new/empty/output-directory
```

The pinned Windows Lean4.35.0 binary hash is checked. A fresh five-source Lake build and the unchanged official checker replay all99 owned constants and check13 headline types. No Mathlib, network download, reused objects or full-catalog build is needed. Another platform requires a separately validated executable hash. INPUTS.json freezes all mathematical sources and the checker.

## Fast independent experiments

Standard-library Python is enough for:

```text
python -B context_graph.py
python -B literal_apparent.py
```

The optional SAT search additionally requires python-sat1.8.dev24 and psutil already installed in your environment. No installer is run by these scripts. clock_sat.py also looks for the coordinator's pre-existing scratch vendor directory; otherwise ordinary Python imports apply. Run in a fresh directory because case directories must not already exist:

```text
python -B run_sat.py
```

Each solver call has a three-second interrupt and an external eight-second/one-GiB cap. Timing-dependent UNKNOWN results are expected. No solver result is a Lean proof premise. SAT-DRIVER-NOTE.json records one original parent-exit recording failure and the subsequent correction/control. CNFs can be regenerated; their exact hashes are retained in the result records. The stored complete results also include the extra driver smoke control.

PROVENANCE.json identifies any diagnostic path normalization. Proof/checker bytes were preserved. MANIFEST.json hashes all payload files except itself. The earlier archive remains unchanged beside this one in research/edge-clock-drop.
