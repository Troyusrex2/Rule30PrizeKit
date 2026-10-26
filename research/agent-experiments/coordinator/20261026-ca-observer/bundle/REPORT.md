# An exact two-output formulation of the canonical reader

The existing reader-completeness conjecture is equivalent to two explicit
observation properties for the finite-word map T = C after A. Here A is the
literal white-boundary Rule 30 scan, C is the scan with its black boundary
state, r is the last bit, and s is the last bit after A.

* Aligned: equal r and s observations at every T-time determine the entire
  nonempty input word, including its length.
* PhaseSeparated: no two nonempty inputs have all-time observations matching
  after swapping r/s and advancing the second r stream by one T-time.

`Rule30CAObserverResearch.reader_complete_iff` proves this equivalence.
`canonical_observer_iff` proves the corresponding canonical-language form.
The proof includes unequal tail lengths, both phases, empty-word edge cases,
the period-at-most-two core, and cancellation of a trace shift using actual
finite-word periodicity. The DFA language is proved by `canonical_iff` in
`Rule30CanonicalLanguageResearch`, not assumed from a regular-expression comment.

**Both observation properties remain open. Reader completeness and Prize
Problem 1 remain open.** This is a reduction of the reader problem, not a
proved equivalence with the prize statement. In particular it does not
identify a finite observation window or prove the separate physical-center
bridge. The maps here are finite list actions; no surjectivity of a map on
unbounded natural-number seeds is assumed.

The two new modules contain 187 kernel-replayed module constants, including
generated constants. Four unchanged reader dependencies contribute 517;
all six modules total 704. The independent fresh source replay passed the
unchanged official checker at the recorded pin in about 33 seconds. All
18 headline checks passed and no new axioms were introduced. Exact types
are recorded in `formal/*/types.log` and were reviewed against the source.
For partial claims the checker's `typeMatches` does not compare against an
externally supplied expected proposition. Sources and types establish scope.

The first independent run passed the first module's checker but stopped on
an unsupported formatting option in an optional type transcript. Removing
that option allowed the full independent replay; no proof source changed.
The original failure remains in the private research audit, and the exact
script correction is recorded in `evidence/ROOT-CORRECTION.json`.

Check the archive without invoking Lean:

    python replay.py --verify-only

Rebuild all six sources and replay every declaration using a Lean 4.35.0
environment whose official library was built at the pin in `summary.json`:

    python replay.py --lean /path/to/lean --official-lib /path/to/pinned/lib/lean --checker /path/to/pinned/Check.lean --output /new/separate/output

The output directory must not already exist and must be outside this bundle,
the official library and tool directories. No private research objects are
needed. A prebuilt official dependency library is a prerequisite, not a claim
of a cold Mathlib build. The script verifies source hashes, ordered imports,
the checker hash, counts and recorded headline names. `MANIFEST.json` seals
all files in this bundle except itself.
