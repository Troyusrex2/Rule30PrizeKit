# A global route under investigation

**Status: no full prize problem is solved here.** This is a research checkpoint
from 2026-10-23. The new Lean theorem is a conditional implication, with an open
hypothesis. The experiments are finite. This directory has not been submitted
to the prize API. The two earlier verified submissions are described in
[`../six-tail/SUBMISSION-STATUS.md`](../six-tail/SUBMISSION-STATUS.md).

The renewed investigation targets all eventual periods in Problem 1, rather
than extending the existing padded-word certificates. Those certificates
cannot settle the alternating case just by increasing their strip width.
The kit's `Rule30ZeroBoundaryBarriers` and
`Rule30PeriodTwoSideways` explain the relevant proved barriers and open cases.

## The global question

Let `Tr(x)(t)` be column zero at time `t`, starting from a finite nonzero row
`x`. Ask:

> If `Tr(x) = Tr(y)` for two finite nonzero rows, must their leftmost black
> cells have the same position?

This is `Rule30TraceEdgeResearch.EdgeObservable`. It is **unproved**. We do
not assume that the whole starting row can be recovered: the catalog's stripe
seeds `1`, `11`, `101`, `1011`, ... already give distinct finite rows with the
same center trace. See
[`TransformsSeeds.lean`](../../equivalents/Rule30Equivalents/TransformsSeeds.lean).

Why this question would be enough: suppose a finite orbit's center became
periodic with transient `T` and positive period `P`. The rows at times `T` and
`T+P` would have identical future center traces. If the initial left edge was
`a`, their left edges would be `a-T` and `a-T-P`, which are different.
Edge observability would contradict that.

The new module
[`Rule30TraceEdgeResearch.lean`](../../lean/Ruliology/CellularAutomata/Rule30TraceEdgeResearch.lean)
proves this implication for every nonzero finite starting row, and then proves
`problem1_of_edgeObservable` with the exact official Problem 1 as conclusion.
It does **not** prove its `EdgeObservable` premise. It also proves the easy
unconditional case where both edges start at or to the right of the observation
column: their first arrival determines their positions. The difficult case has
edges to the left, with unknown finite right halves.

The unchanged checker replayed all 14 generated constants successfully, with
no new axioms, in both the working catalog and pinned reference commit
`cc1e0e0e7c1ae8c971aec5c14aaabb47c7b8c554`.
[`pinned-verification.json`](pinned-verification.json) expressly records
`conditional_only: true` and `full_problem_claim: false`. Passing a partial
headline check is not verification of the open premise or a full prize solution.

## Finite evidence for edge recovery

`trace-observability.py` enumerates all rows supported in `[-W,W]`, including
zero, and computes 128 center observations with exact Python integers.
The minimum observation lengths separating *different left-edge positions*
are:

| W | Number of rows | Minimum observations |
|---:|---:|---:|
| 0 | 2 | 1 |
| 1 | 8 | 4 |
| 2 | 32 | 7 |
| 3 | 128 | 7 |
| 4 | 512 | 15 |
| 5 | 2,048 | 15 |
| 6 | 8,192 | 24 |
| 7 | 32,768 | 24 |
| 8 | 131,072 | 25 |
| 9 | 524,288 | 28 |

These minima concern the stated finite support bounds. They are neither a
uniform bound in `W` nor a proof of the infinite hypothesis. Zero is assigned
a separate edge label. Each minimality witness is included in
[`trace-observability.json`](trace-observability.json).

`symbolic-edge-search.py` encodes two independently evolving finite rows in
Z3 and asks for equal bounded traces with different left edges. Every SAT
witness is rechecked with Python integer evolution through another 4,096
observations. UNSAT results remain exploratory solver evidence, not Lean
proofs. In particular:

- The original model independently found UNSAT at `(W,H)=(4,15), (6,24),
  (9,28), (10,40), (12,48)`.
- A tighter model, discarding high bits that cannot affect observations,
  found UNSAT at `(12,40)`.
- At `(12,38)` it found rows `20110911` and `10934896`, with left edges
  `-12` and `-11`, whose first center difference is time `38`.
- At `(12,39)` it found UNSAT. Together these give an exact minimum of
  39 observations for radius-12 nonzero rows in the solver model. This
  bounded conclusion has not been replayed as a Lean theorem.
- Radius 16 and 20 searches timed out. These are recorded as **unknown**.

The original model also allowed the second row to be zero. The refined model
restricts both rows to be nonzero, matching `EdgeObservable`, and uses the
triangular dependence of `Phi` to truncate unused high bits. The historical
reports are retained separately; they are not timings from the refined code.
The executable defaults and report filenames are described below.

## Long agreement is not permanent equivalence

An initial probe of full trace injectivity failed on the known stripe seeds.
Further probes tested whether other finite agreements reduce to stripe tails.
The normalization prototype is exploratory, with no new infinite theorem.
Among 131,072 radius-eight rows, grouping by 1,024 observations gives 65,152
representative collision pairs; all meet the prototype's stripe reduction
at time zero or one. This is a finite classification experiment, not a proof
that all infinite trace fibers have that form.

It is particularly easy to mistake long finite agreements for exact
collisions. For example, in the encoding below:

- Rows `329` and `337` at radius 7 first differ at time **132**.
- Rows `3487` and `3625` at radius 6 first differ at time **139**.
- Rows `19204870` and `8785767` at radius 12 first differ at time **37**.

Wolfram's built-in `CellularAutomaton` independently confirms these times and
the packed encoding, and reproduces the exhaustive edge minima for radii
zero through four. See [`wolfram-independent-check.json`](wolfram-independent-check.json).

## The actual period-two compatibility problem

The kit proves that each finite initial right half `R` has one candidate left
half `Psi R` that would keep the center alternating forever. It remains open
whether this candidate can ever be finite. Even `CQ01Empty`, where `R` is all
white, remains open. This is not resolved by the edge experiments.

`sideways-candidate.py` reconstructs this candidate directly. Starting from
the imposed center column `c` and the driven right-neighbor column `r`, the
next column to the left is

```
l(t) = c(t+1) XOR (c(t) OR r(t)).
```

For the empty right half the first 65,536 left cells contain 32,846 black
cells; the last observed black is at depth 65,534. There are no internal white
runs longer than 19 in this prefix. **These counts do not prove infinitely
many black cells, bounded white runs, or any limiting frequency.**

The regression checks reconstruct different cone sizes independently and
compare them with ordinary full-row evolution. For six right halves and
128 truncation widths each, the first failure of alternation occurs exactly
at the first omitted black depth, as predicted by the catalog's existing
exact-death theorem.

## What was tried, and what is still missing

The investigation followed both finite halves, the backward four-state
transducer, stripe absorption, the coupled period-two statement, the frozen
boundary/automaton-group formulation, and the catalog's finite-state ranking
barriers. These readings did not supply a missing proof.

In particular, inverse-time width descent is not available for arbitrary
finite rows: finite predecessors need not exist. A right-quiescent inverse
can acquire an infinite black tail, and further inversion can produce a
spatial period-three tail. Replacing that failure with an assumed finite
predecessor would invalidate an induction.

The next mathematical step for this route is an invariant or reconstruction
argument that forces different finite left edges to produce a different
center observation, without assuming a bound learned from the table. Another
possible outcome is a counterexample to edge observability; that would close
this route without deciding Problem 1. Rules 90 and 150 supply explicit
negative controls: their reflected single seeds have equal center traces and
different left edges. A proof using only shared left permutivity and moving
edges would therefore fail.

The existing padded-tail theorems remain unconditional. This checkpoint adds
an accurately checked global implication and reproducible experiments, not
an unconditional exclusion of period two or a new full prize claim.

## Reproduction

Python uses the standard library except for the optional symbolic search,
which was run with `z3-solver==5.3.1.0` installed outside the repository.

```text
python research/global-periodicity/test_experiments.py
python research/global-periodicity/trace-observability.py --max-width 9 --horizon 128 --extension 1024
python research/global-periodicity/sideways-candidate.py --depth 65536
python research/global-periodicity/collision-normalization.py --width 8 --trace-horizon 1024 --meeting-horizon 32
python research/global-periodicity/symbolic-edge-search.py --cases 12:38 12:40 16:64 --timeout-ms 60000 --output symbolic-edge-refined.json
python research/global-periodicity/symbolic-edge-search.py --cases 12:39 --timeout-ms 60000 --output symbolic-edge-w12-exact.json
python research/global-periodicity/verify_trace_edge.py --lake /path/to/lake
python research/global-periodicity/verify_trace_edge.py --lake /path/to/lake --pinned-project /path/to/pinned-kit
```

The last command creates only this research module in the pinned worktree,
removing the current catalog's public-module wrappers, and refuses to
overwrite a different existing file. Proof bodies are unchanged. Builds and
checker output are captured locally; sanitized JSON summaries are versioned.

In a Wolfram kernel, `Get` the file `wolfram-check.wl` and evaluate
`globalTraceReport[]`. Its independent CA calls observe offset `W` in the
explicit initial list, since Wolfram aligns offset zero with the list's
**first** cell, not its middle.

Encoding: bit `W-p` of the initial nonnegative integer is the cell at spatial
position `p`. One CA step in the moving integer frame is
`Phi(n) = n XOR ((n << 1) OR (n << 2))`; the center at time `t` is bit `W+t`.
The unit tests also check this formula against a position-indexed truth-table
implementation, independently of both the packed and Wolfram code.

Executed validation: all six instrument tests passed; the independent Wolfram
checks passed; both Lean builds and both complete kernel replays passed.
`symbolic-model-controls.json` records SAT/UNSAT pairs matching the exhaustive
minima on each side of the cutoff at radii two and four. Larger solver
timeouts remain explicitly unknown in their reports.

## Sources and provenance

- [Official prize kit](https://github.com/WolframInstitute/Rule30PrizeKit): the
  statements, existing reductions, barriers, and checker. No checker or
  security/authentication settings were modified for this pass.
- [Condrey, *Finite Configurations Cannot Generate a Constant Trace in Rule 30*](https://arxiv.org/abs/2609.09431):
  the constant-trace classification and the still-open next period case.
- [Wolfram `CellularAutomaton` documentation](https://reference.wolfram.com/language/ref/CellularAutomaton.html):
  independent execution and initial-list coordinate convention.
- The public research notes
  [ghywel/placego/PERIOD-TWO.md](https://github.com/ghywel/placego/blob/main/PERIOD-TWO.md)
  and [fabianxvogt/rule30](https://github.com/fabianxvogt/rule30) were consulted
  as research leads. Their unverified claims are not proof premises. In
  particular, the latter repository retracts a predictive-class counting
  argument; we do not use it.

Research and formalization by OpenAI Codex, working with Troy Lowry. The
edge-recovery hypothesis is recorded as an investigated question, with no
claim of literature novelty or resolution.
