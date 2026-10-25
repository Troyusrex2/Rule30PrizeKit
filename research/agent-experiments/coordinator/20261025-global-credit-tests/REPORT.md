# Global credit, source-aware gaps and a renewal-clock experiment

Troy Lowry and Codex,25 October2026. **Experiments only: no new Lean theorem
is claimed in this archive. Problem1, Q01 and CQ01 remain open.** The preceding
[checked causal block-cycle theorem](../20261025-causal-block-cycle/REPORT.md)
leaves global cross-block credit, location and source history outside its
scope. This batch tests those openings instead of assuming the theorem rules
them out. The [conservation catalog PR21](https://github.com/WolframInstitute/Rule30PrizeKit/pull/21)
remains separate, already checked and open for review.

## Whole-multiset credit without causal-parent restrictions

Canonical lag16 pairs are sampled at distinct effective onsets n in0..4095.
Maximal contiguous disagreement blocks carry time phase mod16, a one-cell
paired halo and their first/last paired letters. The first candidate family is

```
rank(block) = alpha(type)*length + beta(type), alpha,beta >= 0.
```

Its global ordinal resource is the multiset of these natural block ranks.
Credit can move across every block; no parent-specific monotonicity, split
or merge inequality is imposed. For a total natural base order, strict
multiset decrease is tested by lexicographically comparing descending sorted
rank lists. A separate signed-count implementation cancels equal ranks and
checks the sign at the greatest remaining rank. Both implementations agree
on all4900 pairs of nondecreasing rank words over0..3 of length at most4,
and on every tested fitted state, including ties and zero ranks.

The exact SMT formulation aggregates multiplicities when different descriptor
types have equal numerical rank. It times out after16 seconds on the initial
23-onset batch. A cheaper sufficient dominant-residual formulation also times
out. An incremental exact run starting with four onsets times out after10
seconds. These are **UNKNOWN**, not infeasibility proofs or rank refutations.
Their guards finish normally; that does not turn an inner timeout into success.

A numerical discovery run then optimizes a smooth global comparison on a
GeForce RTX2080Ti. It uses all106 guarded onsets n<1024 for training and375
guarded onsets1024<=n<4096 for held-out evaluation. Every type exists in the
model from the outset. Training/model/quantization selection uses training
only; the held-out failures are not used for refitting.

The run completes20000 steps. Its selected nonnegative integer table is from
step5000 at scale8. Under the **exact integer multiset comparison**, it passes
all106 training cases and fails165 of375 held-out cases. Thus the fitted
table is invalid as a universal rank. The smooth training loss is not evidence
of a theorem. The full integer coefficient table and exact failing onsets are
retained in `trained-global-block-rank.json`.

## Global sums also overfit

We separately test natural-valued **sums** of block scores. Unlike ordinal
multiset comparison, ordinary sums allow a numerical loss on one block to
pay for gains on others. The score is a nonnegative polynomial in block
length, conditioned on boundary type and phase. A parity-conditioned variant
also allows different polynomials on even/odd lengths. Nonnegative integer
coefficients guarantee nonnegativity for every length.

Linear programs fit the same106 training onsets. Each floating table is
scaled and rounded to nonnegative integers, then checked with exact Python
integer arithmetic. All four tables pass training and fail on later onsets:

| Polynomial degree | Length modulus | Exact held-out failures out of375 |
|---:|---:|---:|
|1|1|179|
|2|1|170|
|3|1|174|
|2|2|175|

These are failed fitted tables, **not** proofs that every coefficient table
or every global credit function fails. More fit parameters were not treated
as progress toward an unbounded proof.

## Search for a global, rank-independent obstruction

A separate conic search asks for a nonzero positive integer combination of
guarded events whose union of old block descriptors is componentwise contained
in the union of new descriptors. Such an **exact** certificate would contradict
strict multiset decrease under any descriptor-to-ordinal assignment, without
the earlier causal-credit restrictions. A two-event synthetic cycle supplies
an independently checked integer positive control; a single deletion is an
infeasible negative control.

With full block words, phase and one-cell halos, the actual data have15319
descriptor types and481 events. HiGHS reports the cone infeasible. With only
boundary letters, phase and the unbounded length, it has2815 types and again
reports infeasible. Neither run supplies an actual-data integer obstruction.
Floating infeasibility is not a kernel proof, and absence of this sufficient
obstruction does not construct a universal rank. **Global block-word ordinal
ranks remain unresolved by this batch.**

## Source-aware gap resources

The next test uses the checked greedy frontier of the **least initial
disagreement source**, rather than every disagreement. Its root set is the
left cut determined by that frontier. The packed greedy update is compared
with the full root-mask recurrence on10681 steps.112 finite seed-pair cases
produce11087 distinct guarded two-step root transitions. Duplicates are keyed
by effective onset n, lag P and current root cut j: n alone does not identify
this history-dependent root state. This differs from the unlabelled pair's
T+t duplication corrected in the preceding investigation.

Three explicit well-founded resources are tested: the gap-length multiset
followed by frontier distance, the root-block-length multiset followed by
distance, and distance followed by the gap multiset. They fail on5224,5616
and2165 recorded transitions respectively. A nonnegative linear combination
of twelve natural population/gap features is numerically infeasible.

One tiny actual witness already explains the problem. Take onset0,lag4.
The center observations of the two seed histories agree as1,1,0. The least
source has descendants{-4} initially and{-6,-5} after two steps: the frontier
retreats from-4 to-5, population grows1to2, and there is no internal gap at
either endpoint. The twelve listed natural features all stay equal or grow.
An independent physical-coordinate selected-parent simulation verifies this
witness without using the packed root-mask implementation.

Therefore these proposed monotone gap/population resources do not pay for
this retreat. This does not exclude signed potentials with a separate lower
bound, different context, history-dependent hydra ranks, or arbitrary
source-aware mechanisms. The finite witness and simulations are **not a new
Lean proof**; they are grounds to discard these candidate formulas.

## An actual-driver renewal test

The existing official `Rule30ZeroBoundary.free_bits_clock` gives another
possible unbounded route. If `Psi empty` had finite support with last black
depth m, a run of C consecutive equalities `f(s+p)=f(s)`, starting at r,
would imply

```
2*(C-r-p) <= m.
```

This follows by putting ell=C+p-1 into the official inequality
`2*ell+2 <= 2*r+m+4*p`. Unbounded values of this expression for the actual
empty-right driver would therefore prove infinite sideways support. That
unbounded premise has not been established.

We generate262144 actual free bits, without right truncation. For periods
1..64 and128,256,512,1024 every onset is examined. A linear Z-array algorithm
also checks **every lag** at21 preregistered onsets (0..7 and2^k-1,k=4..16).
Independent scalar controls check504 run-detector cases and864 Z-array
queries. Four physical simulations check the packed CA on380 update steps.

The best observed clock bound is274: period7,start1,145 consecutive
comparisons. The apparent early growth stops at that value by the256-bit
prefix and stays there throughout the sampled262144 bits. The longest
period-five comparison run is195, starting at146238, so it gives no useful
late clock bound. For the known absorbed right halfR31, the positive control
does find a large bound8184 in4096 bits.

This is a diagnostic renewal test, **not an improvement of the kit's existing
finite sideways certificates** and not a proof the renewal bound stays
bounded. The current data give no evidence of the needed unbounded growth.
The exact clock factors were checked against the official theorem before
the final run; the earlier coarse draft is not used for the reported values.

## Evidence, limitations and next direction

All ten final guarded jobs finish normally within300 seconds,8GiB owned-tree
RSS and2GiB minimum free memory. The exact initial SMT job peaks at1.26GB;
the learning job peaks at0.82GB and runs79.31 seconds. The solver timeouts and
floating LP statuses remain explicitly separate from exact candidate checks.
No mathematical claim here is inferred from a process exit code.

Python3.12.3, NumPy1.26.4, SciPy1.14.1, psutil5.9.8, PyTorch2.6.0+cu118,
Z3 5.3.2.0. Scripts retain original private dependency paths; see
[REPRODUCE.md](REPRODUCE.md). No solver binary or GPU model checkpoint is
included; numerical and integer coefficient tables are included.

The15:05UTC public refresh still has45 entries, no new entry and the same
3eca reference pin. No new public proof was adopted. The existing PR21 has
no listed GitHub checks and remains open; no new prize essay was submitted.

The tested rank tables fail, the simple root-gap resources fail, and the
renewal test has no observed unbounded growth. General global multiset credit
and least-source escape remain open. Further work needs a mechanism for
actual source cancellation or new history/position information, not another
interpretation of training success as a proof.
