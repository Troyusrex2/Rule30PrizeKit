# Safe entry: a genuine height-two ancestor or an exact whole-clock plateau

The strongest new uniform theorem is
`SafeClockDichotomy.safe_height_two_or_clock_plateau`. For every genuine
finite-white word `((u ++ [c]) ++ [d])` that is Safe and does not return as
a WHOLE after eight steps, it proves:

```lean
(SpanTwo (tr u) ∧ evolution 8 u ≠ u) ∨
  evenClock ((u ++ [c]) ++ [d]) = evenClock u
```

The first branch supplies the literal ancestor two cells earlier, with
all-time signed WHITE-height span at most two and whole-word F8 nonreturn.
The second branch is an explicit unresolved alternative: the complete
Safe word already has exactly the same least positive EVEN whole-word
return clock as that ancestor. The theorem requires no supplied temporal
clock, anti-periodic profile, minimum-width condition, or global Safe
completeness. It does not eliminate the plateau branch.

## Verified sources

| Module | Kernel-replayed declarations | SHA256 |
|---|---:|---|
| SafeClockEntry | 21 | 102fdfe2c55b8bafad83405af0c0baf3026917b401dbff8449eb6d695fa3086d |
| SafeEntryLocalControl | 22 | 94f02bc4336e60d851c1dda12097a51b49060ac37f31db51c328896bff2946af |
| SafeClockDichotomy | 17 | 6c4260ae599c7cf74df7715d8c358f6caee50d5cccd7c697f66e2642958a2d5f |

All 60 declarations passed unchanged official full kernel replay. The root
independently replayed the first two exact sources (43 declarations) and
reviewed the third source; its independent replay is pending at this seal.
Every worker receipt, exact source snapshot, build/check log, and guard
receipt is retained under `formal/` and `evidence/`.

Official pin `5473ffd075f63c9d626e63b8455805d4831b39ca` and checker SHA256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`
are unchanged. No proof placeholders, new axioms, native decision methods,
checker weakening, or shared-reference edits were used. Final leaf guards
took 6.30, 5.88, and 6.32 seconds, each under 1.29 GiB owned RSS; the
300-second / 8-GiB / minimum-2-GiB-free limits were unchanged.

## Mathematical bridge

1. If the WHOLE parent u returns after P steps but `u ++ [v]` does not,
   exact `evolution_snoc` makes the latter row at P equal `u ++ [!v]`.
   Time restart and leaf-flip transport therefore prove that its newest
   column is anti-P at every time. No column period was substituted for
   the supplied whole-word return.
2. A Safe trace cannot be anti-P for even P. Anti-periodicity would
   transfer its no00 condition to no11, forcing alternation. An even
   shift preserves an alternating trace, contradicting the anti shift.
   Thus `safe_extension_preserves_even_return` is uniform in EVERY even P:
   a Safe one-cell extension retains the SAME whole-return clock.
3. Suppose u returns at even P but the Safe two-cell extension does not.
   Its one-cell intermediate prefix cannot return at P, by step 2.
   Step 1 gives its actual anti-P leaf. The actual leaf of u is P-periodic,
   and the last child is Safe. The exact `RootAntiPeriodHeight` identity
   now bounds the WHITE-height of `tr u` in an interval of width two for
   all time. This derives the needed periodic/anti-periodic triple from
   a literal whole-clock jump; it does not assume that triple exists.
4. RootReturningPrefixSafety's three-cell extension theorem says that a
   returning F8 prefix followed by at most three cells cannot have a Safe,
   nonreturning extension. Consequently this actual two-cell ancestor u
   also fails whole F8 whenever the full Safe word fails whole F8.
5. Every genuine word has a positive even whole-return clock: adding a
   leaf at most doubles any parent return clock, as proved directly from
   step 1 and the return alternative. An induction on word length starts
   at the empty word. `evenClock` is the minimum among these positive even
   returns. Prefix autonomy makes this clock nondecreasing with width;
   `safe_last_clock_equal` proves equality across any Safe final cell.
   Comparing the two-cell ancestor's clock with the full clock gives the
   stated intrinsic height-two-or-plateau dichotomy.

The least positive EVEN whole return is deliberately defined separately
from the least positive column period. It also avoids silently treating
an odd base clock as even. Neither kind of clock is substituted for the
other anywhere in this result.

## Fixed boundary-free control, distinct from the bridge

The following period16 profiles, oldest to newest, use little-endian
integer encoding (bit t is the value at time t):

`[15894, 29669, 21850, 23210, 38227, 27309]`.

The two oldest profiles are FREE periodic input histories. The four newer
columns obey every shared Rule30 recurrence for all natural times. The
newest trace is Safe. Both immediate parents have signed WHITE-height
span at least six, so neither has span at most two. All six profiles avoid
11011 and 00100 cyclically, and each of the five older profiles contains
both temporal00 and11; these additional finite properties are separately
kernel certified. The expected periodic/anti-periodic pairing at shift8
fails in either driver ordering.

This refutes a proposed ancestry-free local implication from those shared
recurrences and a Safe endpoint to a height-two immediate parent. It is
NOT a finite-white realization, a minimum-width counterexample, or a
counterexample to Safe completeness. No claim is made that its two oldest
inputs satisfy their own Rule30 equations. The explicit all-time headline
`free_boundary_control` quantifies exactly four updated columns with two
oldest profiles left free. The small Python producer and literal cyclic
audit are retained separately from the kernel certificates.

## Remaining problem

For a minimum-width Safe/non-F8 counterexample the known root lemmas force
the prefixes one, two, and three cells earlier to fail whole F8 and contain
both temporal00 and11. The earlier height-one transfer also rules out
all-time height span at most one for such nonreturning prefixes. None of
those facts rules out equality of the whole-word clocks across the last
two cells. The newly proved result handles a clock jump and precisely
isolates that equality case.

The missing step is a finite-white boundary-sensitive reduction of this
plateau, or an independent extraction of a genuine height-two/nonreturn
word from it. Shifting time preserves a genuine word but does not shorten
the plateau. The first column that doubles an older-prefix clock is
anti-periodic; there is no proved transport of that fact through an
arbitrary later plateau to the Safe endpoint. The fixed control confirms
that the currently stated local endpoint conditions alone do not supply
that transport. No unconditional Safe-to-height-two entry, D3, sink
separation, physical-center nonperiodicity, or Prize P1 proof is claimed.

## Reproduction and provenance

Fourteen dependency sources and their prior full replay receipts are
copied under `dependencies/` and `dependency-receipts/`. `sources.json`
records their exact source and compiled hashes and original owned phases.
These include the frozen HeightOne semantics/periodicity work, RootEventHeight,
RootAntiPeriodHeight, RootReturningPrefixSafety, the existing 36-state
catalog, and literal finite-word transport. No dependency was modified.

`prepare.py` checks those source hashes and constructs the replay manifest.
`replay.py` checks dependency source/compiled hashes plus the official
checker before compile and full replay. Reproduction order is
SafeClockEntry, then either SafeEntryLocalControl or SafeClockDichotomy.
Commands are `python guard.py replay.py <module>` in the owned G913 phase.
`verify_artifacts.py` verifies the local seal and every source/receipt,
headline, checker, and successful guard match without launching Lean.

No publication, PR, or submission API action was performed by this worker.
