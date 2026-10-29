# Sharp onset of clock64 after the first seed defect

Combined corollary by Troy Lowry with OpenAI Codex, using ghywel's UniversalStart (PR54) and the ranked escape/sharpness results (PR55). This credits the imported results; it is not a new proof of either and does not solve the Rule30 Prize.

For an ordinary start with rightmost black cell0, let m>=2 be the first equal adjacent pair of seed bits, x(-m)=x(-(m-1)). The entire right-diagonal prefix through m+15 cannot have period32. By the already established dyadic prefix-clock existence, its clock is at least64. This applies with an arbitrary infinite left side when such a first defect exists. Every nonzero finite seed has one.

The constant15 is sharp: finite seed47649 has first defectm2, still has prefix period32 at diagonal16=m+14, and cannot have prefix period32 at17=m+15. The result is a whole-prefix statement, not scalar individual-period nonloss or vertical center-column aperiodicity.

Mechanism: the imported universal-start theorem gives a non-period-two diagonal at m+1. The imported sharp14-diagonal escape applies to it. The existing actual finite-seed witness attains the bound. This is a useful combination of two public contributions, with no new graph census.

The new bridge passed a fresh16-source closure and unchanged official checker: all18 owned declarations and7 headline types, no source warnings/new axioms/reused objects. Runtime83.06s, peak849,580,032bytes, within the fixed300s/8GiB/2GiB-available guard. Earlier attempts failed to normalize an Int zero-add index before proof application; the exact explicit normalization is now checked. This was a new user-authorized pass after the previous pass stopped, with no guard increase.

```
python replay/verify.py --lean /absolute/path/to/lean.exe --out /new/empty/output
```

Frozen imports include exact ghywel PR54 head7a3f1d8dcf5f412041f52000ee5a057872547160 and the PR51/PR55 dependency sources, on official pin932cf8dde039b89b1dcbe9636867bb1b2057fef0. The new module is catalog-ready once those dependencies are integrated; this archive supplies every required source for an independent replay now. The checker and pinned Windows Lean4.35.0 executable hashes are verified. Other platforms require separately validated executable hashes. This is a focused closure build, not a full-catalog build or Wolfram reviewer approval.

The actual build/check/type/axiom/guard receipts are in evidence/. All payloads except MANIFEST.json itself are hashed. `.gitattributes` preserves the exact checked source bytes. No Mathlib, cached objects, downloads, native evaluation bypass, solver premise, sorry, or new axiom is used.
