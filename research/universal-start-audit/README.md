# Independent replay of PR54: UniversalStart

This records an independent check of ghywel's contribution, not an authorship claim or a maintainer approval.

Audited PR: https://github.com/WolframInstitute/Rule30PrizeKit/pull/54

Exact contributor head: `7a3f1d8dcf5f412041f52000ee5a057872547160`.
Official dependency pin: `932cf8dde039b89b1dcbe9636867bb1b2057fef0`.

The fresh four-source closure passed the unchanged official checker: all258 replay constants, four selected headline types, no source warnings, no new axioms, and no reused objects. The selected headlines are `universal_start`, `universal_start_finite`, `universal_start_profiles`, and `cert`. The run took51.39seconds and peaked at1,153,318,912 owned RSS bytes, within a fixed300-second/8GiB guard.

The theorem concerns an initial configuration with its rightmost black cell at0. If m>=2 is the first equal adjacent pair of initial bits to its left, individual right-diagonal least periods at m+1 through m+6 are4,8,8,16,32,32; at m+7 the least period is32 or64. The finite-seed theorem supplies such an m. No conclusion beyond m+7, individual-period nonloss in general, or center-column aperiodicity was checked or inferred.

```
python replay/verify.py --lean /absolute/path/to/lean.exe --out /new/empty/output
```

The portable verifier freezes source and checker bytes, validates the pinned Windows Lean executable hash, builds from fresh sources, replays every declaration owned by the contributed module, and prints headline types and axioms. Another platform needs a separately validated executable hash. This is a focused dependency build, not a full-catalog build. `evidence/` contains the actual checker/build/type/guard receipts. `MANIFEST.json` hashes every payload except itself. `.gitattributes` preserves validated bytes.

A separate attempted bridge to the prefix-clock escape result was stopped at its fixed resource caps and is not included as a checked result. The completed audit above is independent of that unfinished elaboration work.
