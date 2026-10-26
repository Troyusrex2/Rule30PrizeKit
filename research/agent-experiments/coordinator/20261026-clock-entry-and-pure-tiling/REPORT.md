# Intrinsic clock entry, pure tiling descent, and boundary obstructions

Five modules passed independent root compilation and full kernel replay: 124 declarations, including definitions and generated declarations. The new positive results give an intrinsic entry into the height-two problem and a descent under an explicit temporal tiling hypothesis. Two exact controls rule out boundary-free shortcuts. The whole-clock plateau, general mixed-mode descent, safety completeness, and Prize Problem 1 remain open.

All positive applications retain genuine finite words with an older white boundary. `Safe` means no consecutive whites in the newest temporal trace. Whole-word return and the period of one observed column are kept distinct.

## Clock entry without a supplied period

[SafeClockEntry](sources/SafeClockEntry.lean) proves, uniformly for every even P, that a Safe one-cell extension of a whole-word P-returning prefix returns at the same P. A failed return would force the newest cell to be anti-periodic with shift P. Safety would then prohibit both 00 and 11, forcing alternation, which contradicts an even anti-period.

If adding two final cells to a prefix increases its whole-word return clock, the intermediate column is therefore genuinely anti-periodic relative to a whole-return clock of the older prefix. The signed-height identity then gives an all-time white-height band of width two for that actual older column. The previously proved stronger short-extension theorem also makes that older **whole word** fail return at eight whenever the full Safe word does.

[SafeClockDichotomy](sources/SafeClockDichotomy.lean) removes the supplied-clock premise. It proves existence of a positive even whole-word return by one-leaf doubling and defines `evenClock` as the least such return. Its headline `safe_height_two_or_clock_plateau` proves that every Safe/non-F8 word of the form `(u ++ [c]) ++ [d]` satisfies at least one of:

1. The actual two-cell ancestor u has all-time signed white-height span at most two and fails whole-word F8.
2. The full word and u have exactly the same least positive even **whole-word** return clock.

The alternatives need not be exclusive. The second has not been eliminated. `evenClock` is not the least temporal period of the newest column.

## A genuine descent under a pure tiling hypothesis

[HeightTwoPureMode](sources/HeightTwoPureMode.lean) proves that every infinite concatenation of `10110` and `1011000`, with arbitrary block choices, has signed white-height in `[-1,1]`. Each block contributes zero total height; the proof checks the finite block identities, proves coverage of every natural time, and transports the actual time-parity sign. No periodicity or finite sampling premise is used.

If the literal immediate parent's trace of a height-two/whole-nonreturn word has this tiling, that actual shorter prefix is also height-two and whole-nonreturn. This excludes the tiling at minimum width among **all height-two/nonreturn words**. It does not identify that minimum with a minimum among Safe counterexamples.

The hypothesis `Tiled` explicitly starts a block at time zero. Classification into this grammar and phase alignment are not proved here. A phase-shift application must preserve actual finite-white evolution and whole-word nonreturn; rotating a freely supplied temporal strip is insufficient. Pure grammar need not survive descent, so no repeated pure-mode algorithm is asserted.

## Exact limits of local arguments

Both controls below deliberately leave their two oldest temporal profiles free. Neither is a finite-white counterexample or a minimum-width witness.

- [SafeEntryLocalControl](sources/SafeEntryLocalControl.lean) gives six period-16 profiles with four exact shared update equations and a Safe newest profile. Both immediate parents fail the height-two bound. The supplied profiles also pass the indicated finite periodic forbidden-pattern checks. Thus a Safe endpoint and those local conditions alone do not establish the actual-ancestor height entry.
- [HeightTwoMixedControl](sources/HeightTwoMixedControl.lean) gives seven period-32 profiles with five shared update equations, six adjacent transition-cover relations, and avoidance of `11011`, `00100`, `000111`, and `111000` in every supplied column, all proved for all time. The newest profile has closed all-time height in `[0,2]` and is not eight-periodic. Both parents have 00 and 11 occurrences and fail the height-two bound: their heights at time 32 are 7 and 3. This refutes a boundary-free alternative saying that a height-two child forces a Safe, coSafe, or height-two parent, even with those additional local constraints.

The second control contains genuine switching among the local derivative modes in the exploratory block description. That description is diagnostic evidence; the kernel headlines are the explicit equations, height bounds and failures above. The white anchor is the missing condition, not a condition these examples satisfy.

## Validation and remaining work

All five modules passed the unchanged official checker at `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0, with every declaration replayed, every requested headline checked, and no new axioms. Guarded root runs took about 6.0–6.8 seconds and at most 1.31 GiB of owned memory. Exact hashes and receipts are in [summary.json](summary.json), [formal](formal), and [evidence](evidence).

The root used its own previously replayed, hash-checked dependency artifacts. Sixteen prior dependencies contain 851 declarations and were not rebuilt in this root batch; no worker binaries were used. Three sealed worker packages were audited in full, totaling 222 artifact hashes. All 4,309 owned hashes in 48 prior archives were verified unchanged. These are local Lean checks and agent reviews, not Wolfram human evaluation or a prize award.

The [plateau audit](work/PLATEAU_AUDIT.md) explains the remaining clock obstruction. Half-clock shifting finds the first changed older column but does not transport anti-periodicity through a later plateau. Equal clocks do not permit deletion of actual spatial history: that requires equal full temporal profile pairs. No uniform repetition argument is proved.

Further work must retain the finite-white anchor while handling the plateau and mixed parent modes. The physical-center reader/observer bridge remains separate and open. No new Wolfram API essay or catalog PR is submitted by this research checkpoint; [PR33](https://github.com/WolframInstitute/Rule30PrizeKit/pull/33) remains the catalog contribution for the exact finite-state return criterion.

Developed by Troy Lowry with Cedar and OpenAI Codex, building on the [strict-descent and prefix-safety checkpoint](../20261026-descent-and-prefix-safety/REPORT.md).
