# A kernel-checked inverse-cone method and its current limits

Developed by Troy Lowry with OpenAI Codex, 2026-10-24. Full Problem 1 and
`C3w(011)` remain open. No prize or priority claim is made.

## What is actually proved

[`Rule30ThreeConeResearch`](../../lean/Ruliology/CellularAutomata/Rule30ThreeConeResearch.lean)
generalizes the catalog's zero-boundary reconstruction and packed update to
an arbitrary driven boundary. Its `history_eq_recon` and `packed_sound`
connect the inverse update directly to the official `Rule30DrivenLeft.L`.
The mathematical reconstruction method is already present in the kit; the
generalized bridge and certificate interface support these experiments.

For the prescribed boundary `010`, let `FitsPrefix s N` mean that the head
matches `(*,0,1)` at every time before `N`. The new `prefix_code` theorem
proves that the first `N` initial left cells then belong to a family indexed
by a natural number smaller than `2^((N+2)/3)`. Thus only `ceil(N/3)` temporal
bits are free. It assumes finite trace agreement, not an infinite constraint.
There is no restriction on `N` or on the rest of the initial configuration.

`coneCheck_prefix_sound` and `coneCheck_failure` prove that, for **every**
pair of natural sizes `W,N`, a true finite `coneCheck W N` forces an actual
head-constraint violation before `N` for every initial row white beyond `W`.
`coneCheck_sound` gives the corresponding negation of `Constrained`.
These are generic soundness theorems. No assertion that certificates exist
at every width is made.

The width-eight, time-seventeen check is decided by the ordinary kernel as
a small regression test. It is not a new numerical bound. The unchanged
working and pinned checkers each replay **68 declarations**, with fourteen
selected headlines, no new axioms, and all checks passing:

- [Working replay](three-cone-evidence/catalog/report.json).
- [Pinned replay](three-cone-evidence/pinned/report.json).
- [Reproduction runner](verify_three_cone.py), which also checks dependency
  source correspondence and refuses to overwrite different proof source.

## Exact coordinates and independent controls

Bit `i` of an initial left word is at physical position `-(i+1)`. Its forward
update under boundary bit `b` is

```text
U_b(a) = (a >> 1) XOR (a OR (a << 1) OR b).
```

For temporal column words `A,B`, the inverse spatial step is
`(B >> 1) XOR (B OR A)`. The `advance` function comes from the earlier packed
reconstruction module. The new theorem permits a nonzero first column.

`three_inverse_cone_probe.py` checks 96 arbitrary temporal profiles against
both independent cellwise forward evolution and the packed forward formula.
Its solver experiments return UNSAT at width 24 / 42 observations, and
UNKNOWN at widths 32 / 54 and 40 / 66 after fifteen-second limits. UNKNOWN
does not mean that a witness exists or that the finite system is impossible.

`three_inverse_width_probe.py` enumerates the free temporal bits for the
first `W` observations, reconstructs the `W`-cell initial row, then checks its
future. The optimized two-limb implementation has independent full-integer
carry controls and exhaustive comparison against every initial row through
width twelve. It discards no observable information before its explicit
128-step guard and never continues a truncated state beyond that guard.

The [finite numerical report](three-inverse-width-probe.json) records
widths 24,32,40,48,56,60, with latest first violations 37,49,59,68,77,80.
The optimized Python implementation and these larger bounds have **not**
been kernel certified. They are not new numerical territory: the existing
kit documentation already reports a C search through width seventy.
The purpose here is to validate a reproducible inverse-cone implementation
and a general Lean certificate interface, not to raise the numerical bound.

Eight independent built-in Wolfram `CellularAutomaton[30,...]` cones compare
**111,918 cells**, including the exact latest-failure witnesses, two sparse
inverse prefixes, and the rejected potential witness. All pass. See
[`three-cone-check.wl`](three-cone-check.wl) and
[the saved controls](wolfram-three-cone-check.json). These calculations are
independent controls, not additional Lean proofs.

## Density and variation hypotheses tested, not proved

The anti-diagonal inverse recurrence can be updated with prefix XORs. The
boundary contribution at depth `k` is `driver(k-1)`; dropping this term
would incorrectly reuse the zero-boundary recurrence.
`three_inverse_weight_beam.py` checks that recurrence against 128 complete
inverse/forward round trips before searching. Its incomplete beam retains
1,024 states at each depth. Every saved witness is forward checked.

At depth 1,536 it finds a valid constrained prefix with only 281 initial
black cells. Thus a proposed bound `N <= 4*weight + K` needs `K >= 412`
on this example; the factor-five version needs `K >= 131`. This does not
refute either estimate with an arbitrary offset, and a beam's best retained
weight is not a global minimum. No positive density estimate follows.

`three_inverse_density_lp.py` tests a two-diagonal local amortized potential,
first charging every reconstruction step, then charging changes in the
free head bits. A phase/mode controller handles the latter. All models
include the prescribed boundary and the two necessary ribbon bounds;
8,064 independently generated actual ribbons satisfy their coverage checks.

The nonnegative density model, a signed density model with all-length graph
lower-bound inequalities, and both analogous variation models are
numerically infeasible in the tested class. This is not an exact Lean
refutation or a claim about all potentials. The signed finite-length density
fit without a graph lower bound reports coefficient zero, but an actual
depth-twelve ribbon makes its rationally reconstructed potential **-1**.
The report includes the initial word 3679, trace 2861, anti-diagonals
2749/1442 and the independent forward check. The candidate is rejected.

The graphs here bound the proposed potential below at all lengths; the
descent constraints were only fitted at bounded lengths. Even a feasible
fit would still require an all-length descent proof and Lean replay.
None of these numerical models is used as a Lean premise.

The subsequent `three_inverse_reachable_lp.py` removes the ribbon
overapproximation and fits the same nonnegative variation score on actual
histories through depth 42: 98,294 transitions, 97 variables. This finite
system is also numerically infeasible. Thus the failure of this particular
nonnegative two-diagonal score is not explained solely by spurious abstract
ribbons. No exact Farkas or Lean impossibility theorem is claimed.

`three_inverse_variation_beam.py` directly searches for violations of
`variation <= C*initial_weight + K`, retaining 1,024 states through depth
1,536. The factor-one run finds variation 392 with weight 341, requiring
`K >= 51`. Factor-two and factor-three runs find no positive score. These
are incomplete searches, not proofs of either estimate. Every saved row,
weight and variation count is independently forward checked. The estimates
remain hypotheses; increasing a failed local score window without a new
invariant is not an established route to proving them.

## Audit and full-problem route

The latest PR heads and official kit main were unchanged at the 09:00 UTC
audit. `ghywel/placego` did have 26 new commits, through
[`ded0f2d`](https://github.com/ghywel/placego/commit/ded0f2deecb2e7544478ce1089aada2c3957ae5a).
The new Lean file is a revised **bounded width-sixty Q01 certificate**;
its record also describes a previous verifier memory failure. That revision
has not been independently replayed here and is not adopted as a proof
premise. The four previously audited files remain credited upstream and
separate from this new candidate. No newly verified unbounded argument was
found in this audit.

The full-problem left-edge observability hypothesis is still open. The
additional `left_edge_trace_probe.py` run is a repeated finite control:
65,535 nonzero initial words, width sixteen, center index eight, 128 trace
bits, no cross-left-edge collision. The earlier symmetric-width-nine
experiment was already larger. This repeat is retained for provenance;
it is neither new evidence of an all-time theorem nor grounds for simply
raising the search bound. The existing conditional implication to the full
prize statement remains the relevant verified result.

The substantive gap is still an **unbounded** argument: a density or
variation estimate, a termination invariant with additional structure, or
a direct trace-separation proof. The certificate method alone supplies none
of those steps, and solving this period-three constraint alone would still
not settle every possible eventual period.

## Two further simplifications tested

`three_inverse_mealy_probe.py` treats the inverse construction as a causal
code: one free temporal bit is read, and three initial spatial bits are
emitted. Two prefixes require different states in a deterministic Mealy
encoder if some common continuation produces different subsequent output.
The script compares the complete continuation functions, rather than just
one selected continuation. With sixteen free bits exhaustively enumerated,
two-symbol continuations distinguish **3,418** residual functions after
fourteen input symbols. Four-symbol continuations distinguish **1,137**
after twelve input symbols. One-symbol continuations reach only 32 distinct
functions. See [the finite report](three-inverse-mealy-probe.json).

These are exact finite lower bounds on states for an encoder valid on those
prefixes. They reject a small-state simplification. They do **not** prove
that no finite-state encoder exists: each fixed continuation length permits
only finitely many signatures. Sixty-four independently simulated forward
traces and sixty-four causal-prefix controls pass. No claim here has been
kernel certified.

`three_white_block_probe.py` checks another proposed simplification: a
spatial run of empty three-cell blocks might permit at most one or two
changes in its associated free temporal modes. Exhaustive enumeration of
all 65,536 sixteen-bit mode words disproves those proposed bounds. The mode
word **10890** reconstructs the initial row **246298651725408** (both packed
least-significant bit first). Its zero blocks at indices **11 through 14**
correspond to four alternating modes, hence **three internal changes**.
There is also a change on entering the run; this latter transition is not
counted as internal. Independent scalar and packed forward simulations
reproduce the entire prescribed 48-bit trace.

The [report](three-white-block-probe.json) also records the maximum of
`variation - 2 * number_of_nonzero_blocks` over these same finite words:
**-5**. This does not establish a uniform variation estimate. Charging
changes separately to each empty gap is invalid; any such proof needs to
account for information carried from preceding nonempty blocks.

Reproduce the finite diagnostics from the repository root:

```powershell
python research/overnight/three_inverse_mealy_probe.py --symbols 16 --continuations 1 2 3 4 --output research/overnight/three-inverse-mealy-probe.json
python research/overnight/three_white_block_probe.py --symbols 16 --output research/overnight/three-white-block-probe.json
```
