# A verified two-output criterion for the reader problem

Reader completeness is equivalent to two all-time observation properties of
the finite-word CA return map. The proof treats different tail lengths,
both time phases, and the short canonical core. It includes an exact theorem
for the language accepted by the existing canonical DFA.

The main result is `Rule30CAObserverResearch.reader_complete_iff`:

    ReaderComplete ↔ Aligned ∧ PhaseSeparated

Here the outputs are the newest bit before and after the A half-step; the
second phase has an essential one-step lag. Neither property is proved.
This is an exact reformulation of the reader conjecture, not a proof of
reader completeness or an equivalence with Prize Problem 1. The separate
physical-center bridge also remains open.

The two new modules contain 187 module constants; four reused dependencies
contain 517. These counts include generated constants. The complete
six-module source closure passed an independent fresh official kernel replay
at pin `5473ffd075f63c9d626e63b8455805d4831b39ca`, then the actual portable
bundle command passed a fresh replay of all 704 constants in 30.30 seconds.
All 18 headline checks passed, with no new axioms. This uses a prebuilt
official dependency library, not a cold Mathlib build.

Read the [full scope and reproduction instructions](bundle/REPORT.md),
[sources](bundle/sources), and [portable reproduction receipt](reproduction-receipt.json).
The two new sources are
[the DFA language proof](bundle/sources/Rule30CanonicalLanguageResearch.lean) and
[the CA observer adapter](bundle/sources/Rule30CAObserverResearch.lean).
Exact elaborated headline types are included alongside the full checker
receipts. Partial-checker `typeMatches` is not an external expected-type
comparison; the hash-bound source and type review establish the scope.

No new Wolfram essay was submitted. All 4,985 recorded hashes in the prior
52 owned research archives were checked unchanged before publication.
`artifacts.json` records every file in this archive except itself.
