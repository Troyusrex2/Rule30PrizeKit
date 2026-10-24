# Trace-completeness investigation

**Problem 1 and EdgeObservable remain open.** This checkpoint records exact
paired-row identities, a proved obstruction to one proposed finite recovery
bound, and finite falsification experiments. Research and formalization by
OpenAI Codex, working with Troy Lowry.

The existing kit's `Rule30TraceEdge.problem1_of_edgeObservable` proves that
recovering the left edge from an entire center trace of a nonzero finite
configuration would imply the exact official Problem 1. Recovering the full
initial row is a stronger question. The new stripe relation in
[PR 13](https://github.com/WolframInstitute/Rule30PrizeKit/pull/13) supplies
whole-trace ambiguity and constrains first entry into that relation, but does
not prove either recovery claim.

## Verified paired-difference laws

Let `D=a XOR b` in the moving integer frame. At bit `i`, the difference of
the two evolved rows equals the Rule 30 update of `D`, XOR a forcing term:

```text
Phi(a) XOR Phi(b) = Phi(a XOR b) XOR crossDefect(a,b)  [bitwise]
crossDefect at i = (a[i-1] AND b[i-2]) XOR (a[i-2] AND b[i-1]).
```

Indices below zero are white. `paired_difference_step` proves this for every
integer row and bit index. `local_polarization` checks the Boolean identity
in the kernel; `before_xor` supplies the exact boundary semantics.

If the current and next center observations agree, `same_center_gate` gives
the exact physical neighbor constraint

```text
left difference = (NOT common center) AND right difference.
```

A shared black center can mask a right difference. Thus the paired
difference cannot generally be treated as an unforced Rule 30 history; see
the [independently verified XOR-rigidity audit and premise obstruction](../catalog-review/README.md#xor-rigidity-audit).

## A rejected full-row recovery horizon

The proposed implication from `2*n+2` equal observations of two `n`-bit
rows to an early stripe relation is false. Rows **33 and 45**, center index
**5**, both fit in six bits. Their observations agree at every time
`t < 58` and differ at time `58`. Neither the initial pair nor its first
step is stripe-related. These statements, including the negated early
relation, are proved in `Rule30TraceHorizonCounterexampleResearch.lean`.

The negative relation proof uses the all-time trace-preservation theorem:
an early stripe relation would contradict the checked difference at time 58.
It does not assume an unproved numerical-normalizer interpretation.

Both rows have the same highest bit, hence the same physical left edge.
The example therefore rejects the proposed full-row horizon without
refuting an edge-only bound or EdgeObservable.

Both proof modules passed full replay with the unchanged official checker
at `2f63afda261888e04ec57237290e723190914a1d`: **9 forcing-law declarations
and 8 counterexample declarations**, with eight selected headlines and only
standard axioms. See [the complete reports](evidence/report.json).

## Finite edge-recovery probe

The edge-only candidate tested was: for nonzero rows below `2^n` and center
index `0 <= c < n`, equality through `2*n+2` observations determines their
highest bit. This is an **unproved conjecture**.

The experiment enumerated every nonzero row for 69 selected `(n,c)` domains,
with `4 <= n <= 17` and up to five center indices per width. No counterexample
to that candidate was found. It does not test every center index or prove
an unbounded statement. The full report gives every domain and witness.

For each domain, all observed trace buckets are checked for conflicting
highest-bit labels. Sorting fixed-length trace words in observation order
then gives the longest common prefix across different labels by examining
adjacent label changes. This avoids enumerating every pair at large widths.
The algorithm is independently checked by a direct all-pairs calculation in
24 small domains, covering 142960 different-edge pairs. A physical
position-indexed Rule 30 truth table independently checks 640 observations,
including the 58-step witness. See [the control report](probe-controls.json).

The earlier full-recovery probe stops at a finite collision requiring more
than forty observations; it verifies that the pair separates by time 512.
Its unresolved finite collision is not an infinite-trace counterexample.
All experiment reports explicitly mark completeness and Problem 1 unproved.

## Reproduce

Prepare the reference kit and first run the twelve-module
[`normalization-first-meeting/replay.py`](../normalization-first-meeting/replay.py)
against it. This supplies the exact semantic proof dependencies. Then run:

```text
python research/trace-completeness/verify.py --project /path/to/pinned-kit --lake /path/to/lake
python research/trace-completeness/trace_completeness_width_probe.py
python research/trace-completeness/edge_completeness_width_probe.py
python research/trace-completeness/control_probes.py
```

The proof runner checks prerequisite source hashes and the original checker,
guards every owned compiler/replay process, and fully replays both new modules.
The numerical probes have separate time and memory guards and report partial
scope on interruption. Logs and Python caches are ignored.
