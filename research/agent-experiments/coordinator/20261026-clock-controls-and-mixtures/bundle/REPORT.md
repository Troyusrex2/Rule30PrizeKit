# Six verified research leaves

This candidate archive contains six independently root-checked Lean modules and their exact source dependencies. It combines five distinct partial results. It does not settle Prize P1, arbitrary-distance clock lifting, ReturnComplete, or automatic stripe entry.

| Module | Replayed constants | Result and limit |
|---|---:|---|
| EvenClockLifting | 17 | For any positive even P, append at most three cells to a genuine whole-prefix P-returning word. If the newest trace is P-periodic, the whole extension returns at P. The distance bound remains three. |
| CedarGenuinePlateauControl | 18 | A fixed genuine finite-white clock birth and its two one-cell extensions return after 32 ticks and fail to return after 16. Both extensions have newest traces that are neither 16-periodic nor 16-antiperiodic. This refutes blanket antiperiod persistence; it is not a Safe counterexample. |
| SingleSeedOnsetObstruction | 22 | The actual one-seed diagonal D32 differs at times 32 and 32+2^32. A closed 33-coordinate prefix repeats at times 36 and 44, and prefix autonomy supplies all subsequent repeats. This refutes onset by center-crossing time; eventual diagonal periodicity remains intact. |
| PhysicalEntryBarrier | 23 | A narrow incoming stripe regenerates the larger stripe under the existing padding bound. Failed narrow entry after L white ticks forces an all-black positive prefix through L-9N at the preceding black tick and a white column-1 cell at the earlier shield deadline. It does not force automatic entry, endpoint whiteness, or strict growth between cycles. |
| PhysicalMixtures | 58 | Maintains stripes through a finite cyclic schedule and excludes a repeating schedule when a specified adjacent pair of sufficiently large white gaps supplies warmup and capture. |
| PhysicalMixtureWord | 31 | Transports that schedule theorem to the official `EventuallyWord` statement for the literal concatenated word. No initial stripe premise is assumed; two designated large gaps remain required. |

For the last theorem, N>=1, r>=1, every block contains a black cell and has length at most N, and all r white gaps have length at least 19N+10. The gap before block 0 has length at least `warmup N`, and the gap after block 0 has length at least `bound N + 9*horizon N`, with `horizon N=2N+1`. These two gaps surround the same designated block cyclically. For r=1 both conditions apply to the same gap. The raw mixture modules are included here for reproducibility; their equivalent catalog theorem was already public in PR34, so this archive does not claim a newly discovered mixture theorem.

The six leaves account for **169 module constants**. Their **24 reused dependency modules** account for **1,148**, giving **30 modules and 1,317 constants** in the complete source replay. These are per-module checker counts, including generated internal constants, not counts of handwritten theorems or new mathematical results. `summary.json` gives exact hashes, direct imports, root evidence provenance, headline names, and the computed topological order.

Each source is copied byte-for-byte from its independent root replay phase and checked against that phase's source snapshot and report. Every bundled root report says `pass`, full module replay succeeded, and no new axioms were reported. The reports use official pin `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0, and checker SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. No compiled objects or worker binaries are included.

The assembly phase checked hashes, import closure, evidence consistency, and counts. It did not perform another Lean run. The portable replay script's full fresh execution is reserved for the coordinator before publication; an assembly preflight is not a fresh kernel replay.

## Reproduction

Provide Lean 4.35.0, the unchanged official `Check.lean`, and a previously built official library from the stated pin. The supplied library directory must expose the imported Ruliology and Mathlib modules. Private dependencies are all present in `sources/` and are rebuilt in the recorded order.

First verify the package without running Lean:

```text
python replay.py --verify-only
```

Then replay into a new directory outside this package and outside the supplied tool/reference directories:

```text
python replay.py --lean /path/to/lean --official-lib /path/to/official/lib/lean --checker /path/to/Check.lean --output /path/to/new-replay-output
```

The script checks the checker hash, Lean version, package hashes, and stored evidence; rebuilds all 30 modules without copying any private object files; and invokes the unchanged checker with each module's recorded headline names. It writes only to the newly created output directory and limits each subprocess to 300 seconds. Apply an external resource guard if needed. A successful run creates `receipt.json`; an exception is a failed or incomplete run. The pin is a prerequisite on the supplied official library, not inferred from an arbitrary collection of object files.

The group-theoretic paper audit, unrelated failed experiments, private assembly tooling, credentials, and resource/spending notes are not part of this candidate.
