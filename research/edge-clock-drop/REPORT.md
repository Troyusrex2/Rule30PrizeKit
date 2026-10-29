# Period-drop follow-up: two unbounded branches closed

The Rule 30 Prize remains unsolved. This phase formalizes two restrictions on period drops for arbitrary initial right-edge codes; it does not prove full monotonicity or a claim about the physical center column.

## Intake and correction

Two new coinailyzer-swarm Claude R4-05 responses were found in agent-inbox, not claude-responses. All six manifest hashes matched. The width-20 full-cycle census is finite evidence. The accumulator argument bounds prefix clocks above by doubling, but cannot supply a lower bound for an individual column. The proposed final reduction to arbitrary equal-period binary sequences is false: period-four complementary sequences have constant OR and even half-period parity. Even the local necessary constraint `older <= delta(previous)` admits false positives, exhaustively witnessed for clocks 4, 8, 16. Finite white ancestry must remain in the question.

## New kernel-checked statements

For the official Rule30FrozenRuler.T / iter, on ANY initial code c:

1. If column j has period h and column j+1 has antiperiod h, column j+2 does not have period h. The clock h is unrestricted, and finite support is unnecessary. If the next column hid the flip, its driver would be h-periodic, forcing column j to be identically black. Both newer columns would then alternate, so their XOR is constant and they cannot disagree about the h-shift.
2. If column j is constant, every older column i<j is identically white at every time. A constant newest bit forces its OR driver to be zero; descending through the recurrence forces the entire older prefix white. Thus a nonconstant column cannot be followed by a constant column.

The first is Claude's subcase B, with a shorter proof that avoids inferring a prefix period from the period of its final column. The second closes drops to clock one. The remaining case is a drop after an equal-clock plateau, retaining genuine finite white ancestry. Older checked even-clock rigidity results constrain some short plateaus, but do not close arbitrary plateau lengths.

Research replay: attempt04, module Rule30ClockDropResearch. Canonical replay: canonical-evidence2, module Ruliology.CellularAutomata.Rule30EdgeClockDrop. Both replayed 16 owned constants, seven headline types, with no new axioms and no proof-source warnings. The canonical validation used a fresh five-source Lake build from exact pin 932cf8dde039b89b1dcbe9636867bb1b2057fef0, no reused objects, and unchanged Check.lean SHA-256 b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905. Canonical source SHA-256 43940ad1694856e90775feced5db5b9b1a7d9c3ca10157d86dba81be85685240. The whole catalog was not rebuilt. Checker deprecation messages are separate from proof-source warnings. Earlier failed attempts are retained privately; none is labeled passing.

## Fixed-clock graph: arbitrary spatial width

At a fixed positive temporal clock q, represent each column by its cyclic q-bit temporal word. Starting from two identically white older columns (0,0), append C exactly when `delta(C)=A OR B`. Integration gives exactly two possible C, complementary to one another, if the driver's parity is even; otherwise there is no q-periodic extension. A finite white-boundary word with orbit period dividing q yields precisely such a path. Conversely, every such finite path satisfies the full cyclic recurrence and gives a genuine mask-truncated finite-word orbit. Induction on path length therefore covers ALL widths, but only at the specified clock.

Complete graphs, with no period drops on any edge:

| Clock q | Reachable states | Edges |
|---|---:|---:|
| 2 | 8 | 12 |
| 4 | 12 | 16 |
| 8 | 36 | 40 |
| 16 | 68 | 72 |
| 32 | 2,116 | 2,120 |
| 64 | 171,780 | 171,784 |

An independent implementation regenerated every edge using literal Boolean time steps, tested least periods over every divisor of q, and checked exact reachability and closure of every stored state set. Both implementations agree. These are Python results, not Lean theorems. At q=128 the run hit its 400,000-state cap (400,002 stored at the atomic two-child boundary), leaving 36,689 frontier states: INCOMPLETE, no conclusion.

An additional diagnostic found exactly four multiple-parent states in each complete graph, all of temporal period dividing two. Every higher-clock reachable state has a unique parent in these graphs. This could motivate an ancestry invariant, but neither its unbounded-clock generalization nor its implication for no-drop is proved.

## Claude handoff and resources

R5-01 was written to agent-assignments/20261029-period-drop-followup/coinailyzer-swarm.md, with the corrected gap, exact source paths, old rigidity lemma, and new graph diagnostic. It requests 60–90 minutes at most and a new unique response in agent-inbox; no paid subagents or larger census. There is no connected Claude dispatch tool, so the task is prepared and has no acknowledged receipt. The README supplies the exact prompt for the existing Claude session.

Baseline displayed weekly usage: 4% used; additional allowance: four points; absolute ceiling 8% used. Work cutoff 7%. No reset or paid worker was launched, no computer settings were changed, and the broad prize goal was not resumed. All remote proof jobs were guarded at 300 seconds / 8 GiB with at least 2 GiB system headroom. No prize essay or submission was made.
