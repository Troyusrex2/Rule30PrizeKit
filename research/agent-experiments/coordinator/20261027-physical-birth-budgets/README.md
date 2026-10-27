# Physical mismatch episodes and distinct births

A portable core-Lean project for the actual single-seed Rule30 pattern,
contributed by Troy Lowry with OpenAI Codex. This is a partial result, not a
proof of a Rule30 Prize problem.

If the physical center is P-periodic from T, with P>0, then every **2P+1
consecutive** physical column-one readings after T+2P contain a zero
2P-shift mismatch. Combining that residence bound with the official
MaskedJen window theorem gives distinct zero-to-one mismatch births.
For fixed n0>=T+2P and n0>=4P, the new bound is

    2*m <= birthCount (2*P) n0 (4^m*n0)+1.

The birth source interval is `[n0,X-1)`: every counted birth creates its
mismatch strictly before X. Q=2P and n0 are fixed before all horizons m.
The proof includes m=0 and empty intervals. The mathematical argument is
in [BIRTH-LOWER-PROOF.md](papers/BIRTH-LOWER-PROOF.md).

`problem1_of_fixed_birth_budget` reduces official Problem1 to an explicit
upper-frequency hypothesis: for each hypothetical center period, choose
n0,C,M once, then bound the birth count by C+m for every m>=M. **That upper
bound remains unproved.** The earlier masked-defect upper budget also remains
an explicit unproved premise.

## Reproduce locally

Use Lean4.35.0/Lake and Python3.9 or newer. The exact toolchain pin and core project
metadata are included. No Mathlib, private compiled objects, SSH, credentials,
Wolfram service, or remote machine is required. Run from this directory:

```text
python verify.py
```

This verifies the package manifest, runs the actual command
`lake --no-cache build Ruliology.CellularAutomata.Rule30PhysicalDefects`,
then invokes the included unchanged `Check.lean` with **every one of the18
headlines in `headlines.json`**. It replays every constant in the catalog
module, checks the headline types, and compares all printed types against
`Types.expected.log`. New evidence is written under `verification-output/`.
The script does not install tools. For a fresh source build, start from a
fresh copy of this project with no `.lake/build` directory. The package
contains no such directory or compiled objects.

The unchanged checker SHA256 is
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
The complete equivalent checker command, including all18 headline arguments,
is recorded in [CHECK-COMMAND.txt](CHECK-COMMAND.txt). The arguments are plain
Lake/Lean arguments; the command needs no private paths.

The18 checked headlines are:

1. `doubling_lower`
2. `base_four_lower`
3. `problem1_of_fixed_budget`
4. `or_difference`
5. `mismatch_step`
6. `periodic_mismatch_step`
7. `maskedDefect_eq_or_difference`
8. `live_mismatch_step`
9. `xor_two_blocks`
10. `bounded_mismatch_episode`
11. `true_birth_iff`
12. `zero_one_between`
13. `birth_window`
14. `blockStart_formula`
15. `block_birth_lower`
16. `base_four_birth_lower`
17. `trueBirth_physical_iff`
18. `problem1_of_fixed_birth_budget`

All are under `Ruliology.CellularAutomata.Rule30PhysicalDefects`.

## Exact validation and provenance

The included catalog source has SHA256
`d3b32e63d4dc6bffcf599fb478feb8dd4bde20189ca2a551740dc4bbeda8b063`.
It is the exact source published in
[PR38, “Bound physical mismatch episodes and count distinct births”](https://github.com/WolframInstitute/Rule30PrizeKit/pull/38),
at commit `babf066ed387efb00ac1b2c56072a5a8fb12bd2a`.
The historical validation freshly built this module plus the three official
source dependencies Jen, Prize and MaskedJen using the actual core Lake
project, with no copied build objects. Official source/configuration pin:
`7d665044b904117af9e82328aeb90a30692b2b85`.

The unchanged full checker passed **106 constants in the single merged
catalog module and18 headline types**, with42 noninternal declarations,
zero warnings and no new axioms. All18 printed types equal the previously
verified statements after namespace replacement and whitespace normalization.
The original catalog body and the appended research proof body are preserved
verbatim; the exact mappings are in `receipts/ORIGINAL-BODY-MAP.json` and
`receipts/SOURCE-MAP.json`.

This is a fresh four-source Lake build and a full replay of one106-constant
catalog module. It is not described as a fresh run of three separate research
modules. Packaging performed no duplicate build. The exact historical build,
checker, type, command, source-map, and owned-process guard receipts are in
`receipts/`. Their original Windows paths are provenance only and are not
requirements for reproduction. The guarded validation took4.71 seconds,
used at most827,076,608 bytes of owned RSS, and triggered no resource stop.

`SUMMARY.json` records the source and checker hashes and exact scope.
`MANIFEST.json` hashes every distributed file except itself. No separate
error-transport experiments, usage records, private credentials, or unrelated
watch artifacts are included.
