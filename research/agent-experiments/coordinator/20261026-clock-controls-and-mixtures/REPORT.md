# Verified clock controls, entry obstruction, and padded mixtures

The portable source bundle has now passed a fresh independent replay: all **30 modules and 1,317 module constants**, using Lean 4.35.0 and the unchanged official checker at pin `5473ffd075f63c9d626e63b8455805d4831b39ca`. The complete run took about 115 seconds. All sources were rebuilt; no private compiled objects were copied. The receipt and resource-guard log are included.

The six research leaves contain **169 module constants**. The other **1,148** belong to 24 reused dependencies. Counts include generated internal constants and are not counts of new theorems.

| Research leaf | Result | Boundary |
|---|---|---|
| EvenClockLifting | A newest P-periodic trace lifts a genuine whole-prefix P-return across up to three appended cells, for every positive even P. | The extension distance remains at most three. |
| CedarGenuinePlateauControl | A concrete genuine finite-white clock birth and both one-cell extensions keep whole-prefix period 32 and fail period 16; both new traces fail both 16-periodicity and 16-antiperiodicity. | Refutes blanket antiperiod persistence, not reader completeness. |
| SingleSeedOnsetObstruction | A one-seed diagonal can fail period 2^32 when started at center-crossing time 32. | Eventual diagonal periodicity survives; a later closed prefix gives period 8. |
| PhysicalEntryBarrier | Failed narrow stripe entry after a long white interval forces a specified preceding all-black prefix and an earlier column-1 white witness. | Necessary conditions only; automatic entry is open. |
| PhysicalMixtures / PhysicalMixtureWord | Excludes literal finite cyclic mixtures of black-containing blocks with sufficiently large designated adjacent white gaps. | Two large gaps surrounding one designated block are required; for one block they coincide. |

The equivalent mixture theorem is already public in [PR 34](https://github.com/WolframInstitute/Rule30PrizeKit/pull/34). This archive adds its raw source dependency closure and reproduction evidence, not a claim of a new discovery. The [sealed bundle report](bundle/REPORT.md) gives exact hypotheses, source provenance, and limitations. Its assembly-time statement that a fresh replay was pending is preserved unchanged; the subsequent successful [reproduction receipt](reproduction-receipt.json) supersedes that status.

**Prize Problem 1 remains open**, as do arbitrary-distance clock lifting, ReturnComplete, and automatic stripe entry. These results identify failures of specific proposed shortcuts and prove conditional or restricted-family statements.

To verify the sealed package without Lean, run `python bundle/replay.py --verify-only`. To rebuild and replay, use the command in [the bundle report](bundle/REPORT.md), invoking `bundle/replay.py` and supplying the pinned official library, Lean executable, unchanged checker, and a new output directory outside this archive and the reference/tool directories. The library pin is a prerequisite, not inferred from arbitrary object files.

All 4,855 recorded hashes in the preceding 51 owned archives were verified unchanged before packaging. `artifacts.json` records every file in this archive except itself.
