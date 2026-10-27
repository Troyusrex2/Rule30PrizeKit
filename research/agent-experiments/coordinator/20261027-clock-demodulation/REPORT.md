# Recovering older observations across a clock birth

Two new tools for the finite-word CA observer are now independently verified:

- If a penultimate appended bit flips after a supplied whole return of the
  older word, time-shifted differences of the newest observations recover
  both older output streams. A finite OR detects that condition. Equal
  observations transfer to the older words even when their lengths differ.
- At every width>=8, no two arbitrary scalar output functions support affine
  full-state decoding by fixed time-shifted XOR formulas. The proof supplies
  a conserved prefix polynomial and a general observation-module dimension bound.

The reconstruction is uniform in width, but requires the stated whole older
return and penultimate flip. It does not reconstruct across a zero-displacement
plateau or from a flip only of the newest bit. The decoder limitation leaves
nonlinear observation methods open. Neither result proves reader completeness,
the separate physical-center bridge, or Prize Problem1.

Read the [precise statements and reproduction instructions](bundle/REPORT.md).
The main positive theorem is in
[Rule30CAClockDemodulationResearch.lean](bundle/sources/Rule30CAClockDemodulationResearch.lean);
the method limitation is in
[Rule30CALinearBarrier.lean](bundle/sources/Rule30CALinearBarrier.lean).
All dependencies, exact headline types, source hashes, and full checker receipts
are included. Seven new modules contain413 kernel-replayed constants and25
headlines. With six previously published dependencies, the portable bundle
contains13 modules,1117 constants, and43 headlines. Counts include generated
declarations rather than only handwritten theorems.

The actual portable reproduction command passed a fresh full replay of all
thirteen sources in58.59 seconds, with no guard stop and no new axioms. See the
[reproduction receipt](reproduction-receipt.json). The official dependency
library was reused; this is not a cold Mathlib build. Partial checker typeMatches
does not perform an external expected-proposition comparison; source and exact
type review establish the scope. The checker and pin are unchanged.

All5,040 recorded hashes in the prior53 owned archives were checked unchanged
before publication. No Wolfram essay was submitted. artifacts.json records
every file in this archive except itself.
