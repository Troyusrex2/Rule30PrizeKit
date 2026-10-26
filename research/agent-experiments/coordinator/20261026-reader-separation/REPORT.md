# Complete outside the sink; the sink remains open

Problem 1, CollisionClock, unconditional subset preservation and the
fixed-center past extension remain **open**. This follow-up proves that the
[sound reader](../20261026-column-reader/REPORT.md) is complete outside one
invariant state. It also kernel-checks a finite counterexample to a proposed
three-times-width separation horizon. Neither result completes the reader.

These are local full kernel replays. No Wolfram backend verification, human
review, kit adoption, prize award or new prize submission is claimed.

## New unbounded reduction

For every paired initial word, the reader's state after one exact triangular
Rule 30 update is `phase` of its old state, where

```text
phase = [0,1,2,3,5,4,7,6,10,11,8,9,12,14,13,15,16].
```

This permutation is an involution. The *entire reader state*, not just its
acceptance bit, is therefore a period-two factor of the dynamics. The finite
facts are checked on the existing 47-state certificate and lifted to arbitrary
words. `sink_time_iff` proves membership in state 15 is invariant through
every future time for actual histories, at every prefix length.

`reader_complete_outside_sink` proves: for arbitrary right-bounded actual
histories a,b and n>0, if their initial paired length-n prefix does not end
in state 15, then reader acceptance is equivalent to equality of their last
columns at **every** future time. `nonsink_two_times` strengthens its usable
test: agreement at times 0 and 1 already implies agreement forever, under
that explicit nonsink hypothesis. Every nonsink rejection exposes a difference
by time 1. The proof has no width or clock bound.

The outstanding statement is now precise:

```text
For every actual a,b and n>0 whose paired initial prefix ends in state 15,
there exists t with a(t,n-1) != b(t,n-1).
```

It is **not proved**. The sink contains difficult cases, rather than a
negligible leftover. In the small independent audit, 1,252 sink words even
agree for both of the first two times. Removing the nonsink hypothesis from
the new theorem is unjustified. This classification is at fixed right-edge
depth, which follows a moving physical ray. It is not the prize's vertical
center observation. Completing it would still require further bridges to P1.

## A false separation bound, checked independently in Lean

The first exact profile experiment through width 16 suggested testing a
linear horizon of three times the prefix width. A new finite-prefix search
falsifies that candidate at width 22. Initial rows encoded by the synthetic
integers 1,393,025 and 956,974, low bit first, have last-column agreement at
times 0..71 and a difference at time 72. Both values are generated research
inputs, not computer configuration or credentials. Their reader state is 15.

`Rule30LateSeparationResearch.example_first_difference` independently
computes 73 observations by the exact `stepWord` update and proves their
equality flags are 72 true values followed by false. Separate headlines check
the width and sink state. Ordinary kernel reduction checks this trajectory;
it does not trust the Python search. The initial prefix can be continued
with zeros on the left without changing these fixed-depth observations.

Since 72 > 3*22, the proposed bound fails. This example supports separation
for this pair; it is **not** a counterexample to reader completeness or P1.
It neither disproves every linear bound nor proves any general delay bound.
The search completes widths 1..21 and stops partway through width 22 on this
witness; its width-22 census is not exhaustive. Finite profiles carry 72 exact
time bits. Deduplication requires the already proved reader's acceptance for
both adjacent full columns; it never relies on a guessed repeating tail.
An initial extension cap was repaired before the final run so a larger
full-period bound does not prevent checking an early actual difference.

## Other falsified and unresolved templates

Temporal Newton degree is not a monotone spatial rank. Define degree d by
the largest binomial coefficient index in the mod-two temporal expansion,
equivalently for a nonzero power-of-two-periodic profile the least d with
its (d+1)-st forward difference zero. A 65,814-case Boolean Moebius control
checks the fast degree computation. Literal Rule 30 row iteration and repeated
cyclic differences independently verify these counterexamples:

| Initial row | Width | Depths | Degrees |
|---|---:|---|---|
| 545 | 12 | 9,10,11 | 29,31,31 |
| 3361 | 14 | 11,12,13 | 31,30,28 |

Thus strict growth of individual degree fails, and even the maximum degree
of two consecutive columns can fall. These degree controls are Python
evidence, not Lean theorems. No period decrease was found by the corrected
finite test through width 14; this is not an unbounded nonloss proof.

New rank templates include DFA state, preceding paired context, signed local
weights and optionally the first spatial moment. One-symbol context with and
without that moment, and two-symbol context without it, return UNSAT in the
stated sufficient graph-potential template. The original combined job reaches
the unchanged 300-second guard during the two-symbol moment case despite its
requested solver timeout. A follow-up gives each remaining owned case a real
20-second process cap. All five remaining cases reach that cap. Exact
statuses are in `context-rank-complete.json`;
unfinished cases are **unknown**, not UNSAT. No verified rank or impossibility
theorem for all ranks follows from these searches.

## Validation and reproduction

`Rule30ReaderSeparationResearch.lean` is 109 lines, SHA-256
`b47e4ee93484c4dc33b966b313411f20ebc93e4ae965ada6b499e54183006fe0`:
all 18 declarations and six headlines pass the unchanged official checker.
`Rule30LateSeparationResearch.lean` is 29 lines, SHA-256
`3f2a9cf2997c35f01816479a59ad5fd17ebe481cd94248bc35f0daf9b41db8ab`:
all 12 declarations and three headlines pass. Counts include generated
declarations, not 30 independent new theorems. Neither proof adds axioms or
uses native decision, a modified checker or replaced official definitions.

Both import the byte-identical reader and CommonPast sources, included with
their earlier 119- and 100-declaration full replays. Those are dependencies,
not new results. Remote dependency source hashes were read back again.
Pin `0090056412733accaa27643d3cbbf982104f2251`, Lean 4.35.0, checker SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

Build plus replay on G913: separation 1.631 seconds, 777,920,512 bytes peak
owned RSS; late example 1.737 seconds, 807,763,968 bytes. The original
300-second / 8-GiB owned-tree / 2-GiB minimum-free guards remain unchanged.
The late search takes 4.338 seconds, peak 524,783,616 bytes. Development syntax
and missing-module failures are not successful checks.

The independent audit passes 5,461 factor controls, rejects a wrong phase,
checks both degree counterexamples by literal rows, and confirms all 73
observations of the late pair. These Python audits are not Lean verified.
Run `python verify_artifacts.py` to audit exact recorded bytes and scope.
Prepare the pinned kit and compile the four included modules in order:
CommonPast, ColumnReader, ReaderSeparation, LateSeparation. Copy them to the
project root and use, for each module name M:

```text
lake env lean -o .lake/build/lib/lean/M.olean M.lean
lake env lean --run Check.lean M --claim partial
```

`check_formal.py` records the exact headline arguments and isolated Windows
paths. Adjust paths, not the checker, to reproduce elsewhere. Python guards
need psutil; rank searches need z3-solver, optionally via `RULE30_Z3_DEPS`.
All publication statuses are local verification only. No new external theorem
is adopted, and no historical-priority claim is made.
