# Unbounded past locality for a periodic Rule30 gate future

For G(r)=(r%5==0), any two n-bit pasts reconstruct spatial rows equal from depth1+620n. Every n and every past bit are quantified. Arbitrary legal futures remain open. See [REPORT.md](REPORT.md) for exact scope, limitations, proof mechanism and independent evidence.

## Fresh kernel replay

New module only, with its eight official dependencies:

```text
python canonical-package/verify.py --lean /absolute/path/to/lean.exe --out /new/empty/unit-output
```

All four modules in the expanded PR47, from twelve sources:

```text
python integration-package/verify.py --lean /absolute/path/to/lean.exe --out /new/empty/integration-output
```

Both check the pinned Windows Lean4.35.0 executable and unchanged official checker hashes. They require no Mathlib, downloads, cached objects or full-catalog rebuild. Another platform requires a separately validated binary hash. The unit result is125 constants/15 headline types; the integrated total is452/39, including the original327/24. Mathematical/checker source bytes were preserved exactly.

## Independent Python checks

These use standard-library Python only:

```text
python -B probe.py
python -B audit.py
python -B literal_histories.py
python -B other_future.py
python -B audit_other_future.py
```

probe.py and audit.py use the included CARRIER-SOURCE.json; their input paths were adapted for portability. The initial probe's reference index mistake is preserved in SYNC-RESULT-INITIAL.json and explained in REPORT.md; the current probe and independent audit use the correct indices. The next gap3,5 future is Python-only evidence, not a Lean theorem. Its nonperiodic spatial prefix is a real extra proof obligation.

INPUTS.json files freeze all proof/checker inputs. PROVENANCE.json identifies diagnostic path normalization. MANIFEST.json hashes all payload files except itself. Generated code uses ordinary decide and full kernel replay, with no new axioms, native evaluation bypass or solver proof premise.
