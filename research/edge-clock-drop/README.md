# Rule 30 edge-clock restrictions

Two unbounded local results, with a fresh kernel replay: no half-clock drop immediately after an antiperiodic parent; a constant column forces the entire older prefix white. Full no-drop and the Prize remain open. See [REPORT.md](REPORT.md) for exact hypotheses, provenance and limits.

## Replay the Lean result

With the pinned Lean 4.35.0 toolchain installed, run:

```text
python canonical/verify.py --lean /absolute/path/to/lean.exe --out /new/empty/output-directory
```

The verifier uses a fresh five-source Lake project, the unchanged official checker and seven exact headline declarations. It does not require Mathlib, download software, reuse proof objects or build the whole catalog. The executable hash pins this reproduced Windows toolchain; another platform needs its separately validated toolchain hash rather than deleting the check.

## Reproduce the finite experiments

From this directory, using standard-library Python:

```text
python -B probe.py
python -B clock_graph.py
python -B larger_clocks.py
python -B audit_graphs.py
python -B graph_collisions.py
```

The optional original-agent intake audit in probe.py runs only when that local inbox exists; the published INTAKE-AND-LOCAL.json preserves the six checked intake hashes. The mathematical negative controls do not depend on those private submissions. Graph programs regenerate state certificates locally; large generated state lists are omitted here. Audit hashes identify their exact deterministic contents. Timings may differ. q=128 is capped and incomplete. Python experiments are not Lean-verified claims.

PROVENANCE.json records original and published hashes for diagnostic logs whose absolute local path labels were normalized. No proof source or checker was normalized. MANIFEST.json hashes all published payload files; it excludes itself. No actual security keys or machine configuration were collected.
