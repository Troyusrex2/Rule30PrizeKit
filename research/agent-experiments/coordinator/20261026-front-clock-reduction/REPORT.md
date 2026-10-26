# Subset preservation reduces to stability at the first mode cell

**P1, Q01, CQ01, unconditional subset preservation and the fixed-center
past extension remain open.** This checkpoint proves a reduction and a
uniform clock case. It does not prove the remaining collision-clock conjecture.
No new prize essay or API submission was made.

## Proved reduction

Write delta=a XOR b for two actual histories in right-edge coordinates, and
let h obey their linear divided-difference equation and all-time common wedge
constraint. Suppose the initial delta has finite support. Then these two
properties are equivalent:

- Every mode initially supported inside delta stays inside delta at every time.
- For every such mode, at its first nonzero right-edge depth k, delta(t,k)
  remains black at every time.

This is `preservation_iff_front` in the
[Lean module](work/Rule30FrontReductionResearch.lean). The implication toward
global preservation uses a finite induction, not an assumption that a linear
mode is physical. A mode's first source stays black, while all smaller depths
stay white. The common constraint then makes the adjacent delta column white.
If delta at the source also stays black, its suffix is itself a common mode.
Subtract that suffix to remove the source and continue. The finite initial
difference makes the induction terminate. Sums of these suffixes lie inside
delta at every time.

The previous [past-lift theorem](../20261026-common-past/REPORT.md) required
all-time subset. This reduction isolates what would justify that stronger
premise from the original initial-only assumption. It does not yet justify it.

## Proved clock obstruction

The module also proves `period_two_source_stable`, uniformly in source depth
and time. If the shared column immediately to the source's right alternates
every step, and the next-right delta column repeats after two steps, the
source delta cannot change color.

The underlying temporal lemma is more general. At a possible source, write f
for delta there, x for the next-left mode value, and z for the next-left delta.
The common constraint gives z=f AND x. The recurrences imply that f can change
only when x at the next time is white. If x reverses after P steps while the
change sequence of f repeats after P, every prospective change is exposed at
both colors of x and is impossible. This is `clock_no_flips`.

The period-two background case supplies that reversing clock with P=2. All
recurrences and clock assumptions are explicit. No numerical clock detector
or claimed universal collision classification is used by Lean.

## Exact remaining background-only statement

The source defines `CollisionClock a b` as an **unproved hypothesis**. For each
n, if delta at depth n+1 is always white and delta initially at n+2 is black,
it asks whether either:

1. delta at n+2 stays black forever; or
2. the shared background column at n+1 alternates every step, and delta at n
   repeats after two steps.

`preservation_of_collision_clock` proves that this statement would imply
subset preservation when the initial delta is finite. Its hypothesis is not
an axiom, a verified conjecture, or a theorem asserted for actual backgrounds.
Even proving it would leave the fixed-center past condition unresolved.

## Exact-prefix experiments and falsification controls

A finite prefix is autonomous in these coordinates. The earlier proved period
bound `2^j` lets us calculate its complete temporal columns, rather than accept
a long finite survival as permanence. For every pair of initial prefixes
through depth 14 with a possible initially supported source, the test enumerates
shared adjacent columns and changing source deltas.

Across these tested depths it found 2,288 changing-front candidates. Every
candidate has a shared period-two column and a next-right difference of period
one or two, so every candidate meets the proved clock obstruction's exact
premises. None has even one valid next-column extension. This is an exhaustive
finite-prefix result at the stated depths, **not** a proof at arbitrary depth.
The candidates at different depths are not counted as independent theorems.

The earlier time-cutoff test was also extended as a separate falsification:
29,185,024 nontrivial width-ten modes, 114,488 common survivors through 128,
and no subset-violating survivor. This is finite evidence only. It is not the
basis of the kernel proof or a replacement for CollisionClock.

An independent scalar audit checks all eight next-column initial triples for
one representative clock, all 32 period-two clock inputs and initial states,
and a 64-step suffix decomposition. It rejects an incorrect cut. The temporal
column constructor is compared with 2,730 literal prefix iterations. These
computations are not themselves Lean verified. Sources and exact results are
included. No native decision or solver shortcut is used in the formal proof.

## Kernel validation

The final 397-line module has SHA-256
`c6e009b69c20c73aa4eff738be4e7fc04a5ffe280793e9af0af2a8877a304a3f`.
The unchanged official checker replays all 81 module declarations and accepts
all six headlines, with no new axioms. Counts include generated declarations,
not 81 independent new theorems. Its exact 100-declaration CommonPast dependency
is included with its previous full replay; that is reused work, not another
100 new results.

Pin: `0090056412733accaa27643d3cbbf982104f2251`, Lean 4.35.0.
Checker SHA-256:
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
Final build plus full replay took 1.968 seconds on the Windows offload machine,
with 778,792,960 bytes peak owned RSS and 46,232,862,720 bytes minimum free.
The existing 300-second / 8-GiB owned-tree / 2-GiB minimum-free guards were
unchanged. Repaired simplification errors are not counted as successful runs.

Run `python verify_artifacts.py` to audit exact bytes and scope. To reproduce
Lean, build the pinned kit, copy both work/*.lean modules into lean/, compile
CommonPast first, then FrontReduction, and run the unchanged checker:

```text
lake env lean -o .lake/build/lib/lean/Rule30CommonPastResearch.olean Rule30CommonPastResearch.lean
lake env lean -o .lake/build/lib/lean/Rule30FrontReductionResearch.olean Rule30FrontReductionResearch.lean
lake env lean --run Check.lean Rule30FrontReductionResearch --claim partial
```

check_formal.py lists the six headline arguments. Python experiments use the
standard library, apart from the psutil resource guard. All numerical jobs are
terminal. The public refresh at 02:26:32UTC found the same verifier pin, 40
entries and unchanged skill 1.17.3; no new external theorem was adopted.

The next proof target is CollisionClock, or a genuine counterexample to it.
A possible experiment is to learn a small automaton for exact temporal-column
equality and inspect its invariants. Any learned classifier would need a
separate proof; accuracy or another depth increase would not establish the
unbounded statement. No historical-priority claim is made for this work.
