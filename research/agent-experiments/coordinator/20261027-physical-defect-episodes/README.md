# Physical defect budgets and bounded mismatch episodes

For the actual single-seed Rule 30 pattern, a hypothetical positive center period P forces a uniform bound on uninterrupted mismatches in physical column 1. Choose Q=2P once. After T+Q, every Q+1 consecutive readings contain a zero of

```text
mismatch Q t = cell(t,1) XOR cell(t−Q,1).
```

This is [bounded_mismatch_episode](bundle/sources/Rule30PhysicalDefectEpisodeResearch.lean). It includes both endpoints and uses the fact that the compared streams are the same physical history Q times apart. Two identical P-blocks of center forcing cancel over Q updates. No common reset in column 2 or period of column 1 is assumed.

The same module proves that a true birth—mismatch false at t and true at t+1—occurs exactly when both compared column-one cells are white and the compared column-two cells differ. **How often these true births occur remains open. The subcritical upper budget and Prize Problem 1 are not proved.**

## The complete formal interface

The [budget source](bundle/sources/Rule30PhysicalDefectBudgetResearch.lean) counts white-center mismatches on half-open intervals. From the official doubling-window theorem it proves, for Q>0, center Q-periodicity from T, and n0≥T+Q,

```text
k   ≤ defectCount Q n0 (2^k * n0),
2*m ≤ defectCount Q n0 (4^m * n0).
```

Its conditional Problem1 theorem requires an upper estimate C+m for all sufficiently large m, with Q,n0,C,M chosen once for each hypothetical period P before m is quantified; Q must be a positive multiple of P. Neither the conditional theorem nor bounded residence supplies that upper estimate.

The [charging source](bundle/sources/Rule30PhysicalDefectChargeResearch.lean) proves the literal physical mismatch recurrence and a finite-horizon weighted charging inequality, retaining the initial contribution and full survival multiplicity. An injection at u first affects u+1, and the last possible injection before horizon X is X−2. The [episode source](bundle/sources/Rule30PhysicalDefectEpisodeResearch.lean) adds the uniform residence bound and exact true-birth event. All three sources use actual physical columns 0,1,2, without a moving-diagonal substitution. See the [source/type audit](SOURCE-TYPE-AUDIT.md).

## Paper-only upper-budget analysis

The exact [paper](paper/PAPER.md) explains signed XOR cancellations and derives the paper estimate

```text
N_Q(X) ≤ H_Q * (initial mismatch + number of true births before X−1),
```

where H_Q is the fixed number of white center phases in a Q-period. Each episode has at most Q readings, so it sees at most H_Q white phases; shorter intervals need not have the same total. The signed Duhamel equality, H_Q counting estimate, physical left-column transport, and signed-potential analysis remain paper arguments, as [clarified here](paper/README.md). Only the residence/birth statements listed in the Lean source are formalized. No sparse-birth or other subcritical upper estimate is claimed.

## Verification and reproduction

Independent validation covers 117 module-owned constants, 54 noninternal declarations, and 16 selected headlines, all PASS with no new axioms and zero source warnings. Counts include generated declarations. The [aggregate receipt](reproduction-receipt.json) combines two explicitly identified stages: the previous fresh two-source run (94 constants / 12 headlines) and a fresh build/full replay of only the new Episode leaf (23 / 4), using that exact previously verified research library. It is not described as a fresh single three-module run. All freshly printed headline types match the sealed originals.

The new leaf guard took 2.190 seconds with 0.726 GiB peak owned RSS and 41.63 GiB minimum available memory. [Its evidence](evidence/run_leaf.guard.json) and the [first-stage receipt](evidence/stage1-receipt.json) are retained. The first new-stage launch stopped at a Python guard-marker assertion before Lean started; its [preflight log](evidence/preflight/run_leaf.log) is preserved. The marker plumbing was corrected without changing proof sources or the 300-second / 8-GiB-owned / minimum-2-GiB-free limits. The unchanged checker retains its own existing replay-API deprecation warning.

The actual compiled official reference is `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0. All three needed official sources—MaskedJen, Prize and Jen—were independently Git-hash checked as byte-identical at `7d665044b904117af9e82328aeb90a30692b2b85`. [Compatibility data](bundle/CLOSURE-COMPATIBILITY.json) and [source/object references](bundle/summary.json) distinguish source compatibility from the compiled reference. The checker SHA256 is `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

The portable entry point freshly builds and checks all three sources when invoked. Supply Python 3, Lean 4.35.0, the unchanged checker, and the matching official library with the recorded object hashes. The output directory must be new and outside the bundle and official tools/library.

```text
python bundle/replay.py --verify-only
python bundle/replay.py --lean /path/to/lean --official-lib /path/to/kit/.lake/build/lib/lean --checker /path/to/kit/Check.lean --output /path/to/new-output
```

No private compiled research object is included or used by that portable entry point. Official source snapshots document the external compiled dependency; this is not a cold kit build or a backend verdict. [SOURCE-MAP.json](SOURCE-MAP.json) records artifact roles. The original worker reports remain historical provenance. The frozen 94-constant candidate and both author packages are unchanged. The archive excludes Cedar input artifacts, usage/session data, and monitors. Nothing has been submitted or published by this preparation.
