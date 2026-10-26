# A fixed nearby defect can remain invisible for arbitrary time

For every natural T, there are two **finite** initial states, differing only
at the same four nearby cells, whose observed columns agree through time T.
Their source at depth 4 differs at **every** future time, their right neighbor
is nonconstant, and their paired initial word is in the reader's invariant
state 15. Three new modules pass full kernel replay. This proves a limitation
of defect-local bounds, **not** eventual separation inside the sink or P1.

All observations here are in the right-moving triangular frame
`x[k] XOR (x[k+1] OR x[k+2])`. A fixed k follows a physical ray p=t+k,
not the vertical center of the prize. The white right boundary is real for
the finite examples, rather than an artificial edge inside a causal cone.

## Exact unbounded statement

`Rule30SinkDelayResearch.arbitrary_sink_delay` provides, for every T, states
x,y with the following properties:

- Both are white at every depth k>=N, with N=2*T+8.
- Their initial differences are the fixed cells 1,2,3,4; cell 0 agrees.
- The complete right tail k>=5 is shared at every time.
- Cell 4 is opposite at every time, while shared cell 5 changes between times
  0 and 1.
- Reading their finite length-N paired word from the white right boundary
  ends in reader state 15.
- Their observed cells k=0 agree at all times 0..T.

The source never disappears. Its effect can nevertheless stay invisible at
the observed cell for arbitrarily long as the **shared background** grows.
`no_background_independent_bound` rules out a uniform detection deadline
based only on this fixed defect and its distance from the observation.
This does not refute a deadline depending on total prefix width, nor does it
show that any finite example stays equal forever. Full sink separation,
CollisionClock, unconditional subset preservation and P1 remain open.

## Construction and proof

The construction first gives two infinite right tails with exact temporal
period eight. At each spatial position a byte encodes its eight time bits:

```text
A: 170,  93, 162,  83, 178, (202,43,172,178) repeated
B: 170, 170, 117, 138,  77, (202,43,172,178) repeated
```

The common tail starts at position 5. Their initial rows differ exactly at
positions 1..4. Their head profiles are identical; source profiles 178 and
77 are complements. A finite table checks the official Rule 30 update.
Modular-index lemmas lift it to all times and all spatial positions.
`shared_tail_resynchronization` proves both states individually have infinite
support, their initial difference is finite, the tail is shared, the source
is permanently opposite, and the head is identical forever. Finite initial
**difference** alone therefore does not replace finite individual backgrounds.

There is a known precursor: the earlier
[eight-clock period-loss example](https://github.com/Troyusrex2/Rule30PrizeKit/blob/bb508cd6b7569d7268773f04453a70e578e4c50e/lean/Ruliology/CellularAutomata/Rule30PeriodicProfileCounterResearch.lean)
contains A's profiles to the right of the head after a six-step time shift;
its head is complemented. The independent audit checks this match. The
period-loss phenomenon is not claimed as a new discovery. The new result
uses a shared-tail pair and proves the arbitrary finite delay and sink-state
conditions in standalone sources against the current pin.

Cut both common tails to white at N=2*T+8. A generic locality lemma proves
that matching initial states below N give equal observations whenever
k+2*t<N. This preserves head agreement through T and the two initial
neighbor observations. A separate triangular-tail induction proves the
right tails stay shared and the source remains opposite for **all** times.

Finally, the finite paired word is reversed into the reader's orientation.
Any identical higher prefix leaves its state in {0,3,12}; the preserved seven
cells immediately below it force state 15. Thus these are genuine examples
in the unresolved reader domain, not examples already covered by acceptance.

## Experiments and rejected shortcuts

An independent literal Rule 30 truth-table simulation checks 41,280 scalar
cells in exact shrinking causal cones through time 128 for the infinite
pair, checks its fixed difference support, and rejects an altered tail bit.
No zero boundary is placed inside those cones.

Thirteen finite cuts with requested delays 0..1024 all start in state 15 and
eventually differ in the tested computation. The largest has width 2056 and
first differs at time 1373. These are samples, not an unbounded proof of
eventual divergence. The formal theorem only guarantees agreement through
the requested delay. Separate literal controls compare 1,916 scalar cells
with the finite integer update `x XOR ((x>>1) OR (x>>2))`.

A proposed difference-profile shortcut also fails: two genuine right-bounded
width-five starts 1 and 23 have difference profile 0x1111 over their full
period bound 16. It has no adjacent black cells, but minimal period four,
not two. That Python-checked falsification is not a new Lean theorem.

The first split search imposed only local admissibility and produced a seed
that cannot extend to an actual right tail; it was discarded. Requiring an
infinite predecessor path in the fixed-clock graph gives the explicit
periodic tail above at clock eight. Its absence from the clock-eight white
graph is only a graph fact: it does not rule out every hypothetical different
realization using larger clocks farther right. The constructed pair's own
infinite support is proved directly in Lean. No finite-support counterexample
to reader completeness is claimed.

## Verification and reproduction

| New module | Lines | Full replay declarations | Headlines |
|---|---:|---:|---:|
| Rule30SharedTailCounterResearch | 108 | 58 | 9 |
| Rule30SharedTailDelayResearch | 116 | 23 | 5 |
| Rule30SinkDelayResearch | 84 | 15 | 2 |

Counts include generated declarations, not 96 independent theorems. Every
module passes the unchanged checker with no new axioms. No sorry, native
decision, altered checker or replaced official statement is used. Source
hashes, final full reports and guards are included. The reader and CommonPast
dependencies are byte-identical to their prior 119- and 100-declaration full
replays; those are reused work. Early beta-reduction, namespace and induction
argument errors were repaired before the final successful checks.

Pin: `0090056412733accaa27643d3cbbf982104f2251`, Lean 4.35.0. Checker SHA-256:
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
Final build/replay guards: 4.011s, 1.738s and 1.632s; each peaks below
779 MB owned RSS, with over 46 GB system free on G913. The original
300-second / 8-GiB owned-tree / 2-GiB minimum-free guards are unchanged.

Run `python verify_artifacts.py` for exact byte/scope checks. To replay Lean,
prepare the pinned kit, copy the included Lean sources to its project root,
compile CommonPast, ColumnReader, SharedTailCounter, SharedTailDelay, then
SinkDelay, and run the unchanged checker on each new module. For module M:

```text
lake env lean -o .lake/build/lib/lean/M.olean M.lean
lake env lean --run Check.lean M --claim partial
```

`check_formal.py` lists the exact headline arguments and paths used. Numerical
scripts use the standard library, apart from psutil for guards. Python audits
are not themselves Lean verified. This is local kernel verification, not a
Wolfram backend pass, human review, kit adoption or prize award. No new essay
was submitted. At 04:11:59 UTC the official pin, 40 entries and skill 1.17.3
were unchanged, and there was no new ready agent reply.
