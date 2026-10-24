# Column separation and limits on reconstruction

This continues the global investigation on 2026-10-23. **Problem 1 and the
unbounded edge-recovery statement remain open.** The spatial-column essay was
submitted as a partial result and passed the automated verifier; see
[submission status](SUBMISSION-STATUS.md). No novelty is claimed for the
known mechanism of distinct Rule 30 configurations having the same image.
The kit's [`Preimages.lean`](../../equivalents/Rule30Equivalents/Preimages.lean)
already proves noninjectivity for left-asymptotic rows. The explicit example
below records the finiteness distinction and its consequence for uniform
reconstruction; it is not presented as a discovery of noninjectivity.

## Unbounded separation of single-seed columns

[`Rule30ColumnSeparationResearch.lean`](../../lean/Ruliology/CellularAutomata/Rule30ColumnSeparationResearch.lean)
proves that **every pair of different spatial columns p and q** in the
single-seed pattern has a differing observation at a time
`t <= max(abs(p),abs(q))+18`. In particular, for every m>0 the mirror columns
-m and m differ at time m+j for some j<=18. This is a theorem about all
integer positions, not an extrapolation from finitely many sampled columns.

Different distances from the seed are distinguished by their first black
arrival. For equal distances the proof uses the first 20 cells at each moving
edge. The right window is 256-periodic from time zero; the left window is
4-periodic after time 20. Ordinary kernel certificates establish the cycles,
all 256 phase cases, and the small initial exceptions. Induction carries
these facts to arbitrarily large column positions. The window encoding is
proved directly against the catalog's cellwise diagonals.

All 85 generated constants pass unchanged-checker kernel replay in both kit
versions, with standard axioms only. See `columns-catalog-verification.json`,
`columns-pinned-verification.json` and `columns-evidence/`. Independent
cellwise Python and Wolfram checks confirm the cycles, all 256 finite phase
cases, and 512 sample mirror pairs. Python also checks 1,176 column pairs and
negative controls using rules 90 and 150. Their sample sizes do not limit the
Lean theorem's quantifiers.

This proves injectivity of the **complete traces starting at time zero** for
the single-seed pattern. It does not exclude eventual equality of columns or
prove any column temporally nonperiodic. `EdgeObservable` for arbitrary finite
starting rows, and the full prize problem, remain open. No literature-first
claim is made for this spatial distinction.

The evaluated computational essay is available as a
[Wolfram notebook](column-separation-essay.nb) and
[readable output from ReadNotebook](column-separation-essay-evaluated.md).
Its self-contained proof carries all 85 declarations, checks them in a fresh
Wolfram/LeanLink process, and preserves the exact source. The saved notebook
has zero message cells; its verification and inspection reports are adjacent
to the notebook. With Troy Lowry's explicit consent, this exact notebook was
submitted as `R30-20261024-ad6cac` and passed the prize system's automated
verifier. Human review and catalog merging remain pending.

## A stronger induction assumption is false

It is tempting to strengthen edge recovery to recovery of every initial cell
on the left from the center trace. That strengthening fails for left-finite
configurations with infinite right halves, even when both configurations
become finite after two steps.

Here are two explicit rows. Coordinates -3 through 0 are shown before the bar;
the words on the right repeat forever, and all cells left of -3 are white:

```text
x = ...000 1010 | 010010010010...
y = ...000 1100 | 100100100100...
                 ^ position 1 follows the bar
```

Both leftmost black cells are at -3, and both center cells are initially
white. Their initial cells at -1 differ. Nevertheless their *entire* center
traces agree. This is an exact theorem, not an inference from a long match.
After one step their full rows are identical: black at every position at
least -4 except -2. After two steps both rows are finite, black exactly at
positions -5, -4 and -1.

[`Rule30TraceRigidityResearch.lean`](../../lean/Ruliology/CellularAutomata/Rule30TraceRigidityResearch.lean)
proves every part, including that neither initial row is finite. The unchanged
checker replayed all 84 generated constants in the working catalog and the
prize's pinned reference environment, with no new axioms. See
[`rigidity-pinned-verification.json`](rigidity-pinned-verification.json).

This is **not** a counterexample to `EdgeObservable`: the edges agree. It is
not a counterexample involving two finite initial rows. It rules out a
stronger reconstruction argument if that argument discards right finiteness
or replaces initial finiteness with eventual finiteness.

The same module proves the complementary distinction:
`EventualFiniteEdgeObservable ↔ EdgeObservable`. Edge positions can be pulled
back through a finite restart because each moves left by one cell per step.
That equivalence does not prove either open edge-recovery statement.

An independent Wolfram built-in CA check confirms the 512-cell trace prefix,
finite windows of the one-step and two-step images, and agreement with the
finite row after two steps. The full-image and all-time assertions come from
Lean, not from those windows or 512 observations.

## An all-horizons obstruction using finite initial rows

[`Rule30TraceAmbiguityResearch.lean`](../../lean/Ruliology/CellularAutomata/Rule30TraceAmbiguityResearch.lean)
proves a stronger consequence of this example: **for every observation horizon
H**, there are two **finite** initial configurations with left edge -3 and
different initial cells at -1 whose first H center observations agree.
Truncate both periodic right tails beyond position H. Causality preserves the
H observations, while both finite witnesses retain their different left
neighbors and common left edge.

Consequently no finite horizon depending only on the fixed left depth can
recover even that one initial left-neighbor cell when the finite right support
is unbounded. This is an unbounded theorem about every H, not a numerical
pattern inferred from tested horizons. All 14 generated constants pass the
unchanged kernel checker in both environments; see
[`ambiguity-pinned-verification.json`](ambiguity-pinned-verification.json).
An independent Wolfram check also verifies the finite witnesses at eight
sample horizons from 0 through 1,024; `wolfram-ambiguity-check.json` records
those samples separately from the all-horizons proof.

This does **not** produce two finite rows with equal entire infinite traces:
the finite witnesses depend on H. It does not refute `EdgeObservable`, since
their edges agree. It does rule out extending the fixed-depth edge-certificate
method to uniform recovery of the entire initial left half.

There is a sharp contrast at depth two. The same module proves that four
center observations recover the initial cell at -1 whenever the left edge is
-2, even for an infinite right half. If the four observed Boolean values are
`c0,c1,c2,c3`, the decoder is `!c1` when `c0` is black, `c2` when `c0` is white
and `c1` is black, and `c2 && !c3` otherwise. The other initial cells on the
left are already fixed by the edge and the time-zero center observation.
Depth one is immediate for the same reason. Thus depth three is the first
left depth where a uniform finite horizon cannot recover the initial left
half.

## Removing the finite right-box assumption

The earlier radius-W experiments bounded both sides of each starting row.
The new asymmetric search fixes only the two left-edge positions. At an
observation horizon H it allows arbitrary initial right cells through H-1.
Every possible infinite right completion has one of those prefixes, and cells
farther right cannot affect these H observations. Thus a correct finite-cone
separation is uniform over **all** right halves, including infinite ones.

Examples of exact cutoffs in the solver model are:

| Left edges | Minimum observations | Evidence |
|---|---:|---|
| 0, -1 | 2 | enumeration, Wolfram, Lean |
| 0, -2 | 3 | enumeration, Wolfram, Lean |
| -1, -2 | 9 | enumeration, Wolfram, Lean |
| -2, -3 | 15 | enumeration; complete current and pinned kernel replays |
| -1, -4 | 18 | solver, independently checked SAT witness |
| 0, -8 | 25 | solver, independently checked SAT witness |
| 0, -12 | 22 | incremental solver, independently checked SAT witness |
| 0, -16 | 29 | incremental solver, independently checked SAT witness |

“Minimum” uses both UNSAT at that horizon and SAT at the preceding horizon.
The concrete Lean separation theorems certify the upper bounds; they do not
assert optimality. The larger solver-only bounds have not been replayed as
Lean proofs. Other larger searches ended with unknown/canceled, explicitly
recorded in `incremental-asymmetric-larger.json` and
`incremental-asymmetric-medium.json`. Changing the maximum cone and timeout
changes where the solver stops; it does not turn an unknown into separation.

The initial 64-observation queries timed out for some small pairs even though
shorter queries later proved separation. Incremental queries expose the short
contradiction first. A timeout is never treated as a counterexample or proof.

## A general kernel certificate method

[`Rule30TraceSeparationResearch.lean`](../../lean/Ruliology/CellularAutomata/Rule30TraceSeparationResearch.lean)
proves soundness of the finite-cone test with no right-finiteness premise.
It packs the relevant initial right prefix and finite left half, proves the
moving-frame integer update directly against the official cellwise dynamics,
and collects
all possible temporal signatures for each left edge separately. Disjoint
signature sets force a difference in the observed center prefix.
The proof uses core Lean only and builds in the standalone `lean/` project;
it does not import the kit's Mathlib equivalents layer.

The first certified signature-set sizes are:

| Horizon | Left depths | Signature counts | Disjoint |
|---:|---|---|---|
| 2 | 0, 1 | 1, 3 | yes |
| 3 | 0, 2 | 1, 7 | yes |
| 9 | 1, 2 | 15, 29 | yes |
| 15 | 2, 3 | 79, 122 | yes, complete current and pinned kernel replays |
| 3 | 1, 1 | 4, 4 | no, negative control |

The complete 16-module separation chain passes the unchanged checker in both
the working catalog and pinned reference kit: all 298 generated constants,
with no new axioms. This includes the soundness proof, all four positive
certificates and the negative self control. The larger 15-observation
certificate has 196,608 initial assignments across its two
sides. A monolithic attempt was stopped for memory use before completion.
The published source instead uses generated equalities over small chunks and
combines their proved masks. Every leaf uses ordinary `decide`, and every
declaration must pass full kernel replay; no native decision shortcut or SAT
oracle is used. The complete current and pinned validation reports are
`separation-catalog-verification.json` and
`separation-pinned-verification.json`; only a final `verdict: pass` signifies
that the entire chain completed.

An initial concrete-rewrite aggregation also hit the runner's five-minute
per-job limit. The generator now proves one symbolic combination lemma before
specializing it to the large cones. This prevents Lean from unnecessarily
unfolding the ground enumeration again while joining already proved chunks.
It changes neither the finite statement nor the kernel checker.

## Additional stress tests

`periodic-right-fibers.py` checks 11,242 left-finite configurations with
primitive right periods up to four against 512 center observations. It finds
no mixed-edge classes in that finite search, and 599 classes with different
initial left prefixes. Some examples have exact one-step full-image merge
certificates; others remain finite trace agreements. They are not all claimed
permanent. This search recovered the explicit period-three witness above.

`finite-preimage-caps.py` tries to turn a right-infinite ambiguity into a
finite one by taking finite ancestors of stripe-tail extensions. For source
22, 2,049 cap lengths and inverse depths 1, 3 and 5 were checked. Every
nonempty cap changed the required initial trace prefix. This defeats that
particular construction within the tested range; it does not prove that no
finite counterexample or different construction exists.

`finite-alias-construction-search.py` broadens that probe to sources 1 through
255, inverse depths 1 through 7 and cap lengths 0 through 24. It checks 20,800
constructions satisfying the stripe-anchor conditions. Of these, 5,440 pass
the initial trace constraint and a further 128-observation cross-check; none
changes the initial left prefix. This is still a finite construction search,
not a proof of left recovery or a classification of all trace equivalences.

All ten independent instrument tests pass, including a cellwise truth-table
comparison, negative controls with rules 90 and 150, a long finite agreement
that eventually separates, the right-cone cutoff, and the exact periodic-tail
merge example. Neither the tests nor a solver result substitute for a Lean
proof of an unbounded claim.

## The missing unbounded argument

A sufficient statement is that for every pair of different finite left-edge
depths, some finite observation horizon gives disjoint signature sets. No
proof of that statement or usable induction on the depths has been found.
It would establish edge recovery even with arbitrary right halves, which is
stronger than the finite-row hypothesis needed for the prize reduction.

The checked stronger-reconstruction counterexample prevents using equality
of the entire initial left half as an invariant after dropping right
finiteness. The finite certificates establish individual base cases. Neither
they nor the solver table justify a uniform horizon bound or an induction
step. Advancing two colliding rows increases both left depths by one.
Reversing that move is not a valid induction: an arbitrary finite row need not
have a finite predecessor. Rows in the single-seed orbit do have their actual
ancestors, but a proposed periodic trace can only be pulled back to its unknown
transient, not necessarily to time zero. An argument exploiting finite left
support, or a more specific property of the single seed, is still required.

Two related primary sources reinforce this distinction. Kopra's
[*A natural class of cellular automata containing fractional multiplication
automata, Rule 30, and others*](https://arxiv.org/html/2202.13809), Section 4,
leaves the width-one trace problem open and notes the Rule 90 counterexample
to extending the general expansivity argument. Nersissian's
[*Diagonal Bases and Diagonal Periods of Elementary Cellular Automata*](https://arxiv.org/html/2609.25078v1),
Section 10.2, distinguishes a supplied fixed-diagonal representation from the
cost and behavior of the growing-depth center readout. Neither paper supplies
the missing single-column argument, and neither is imported as a proof premise
in the new Lean modules.

## Reproduction

The simulations use standard-library Python. Symbolic searches additionally
use `z3-solver==5.3.1.0`. The resource-bounded verification runner uses
`psutil` and checks every generated module, including all certificate leaves.

```text
python research/global-periodicity/test_experiments.py
python research/global-periodicity/periodic-right-fibers.py
python research/global-periodicity/finite-preimage-caps.py
python research/global-periodicity/finite-alias-construction-search.py
python research/global-periodicity/enumerate-separation-masks.py
python research/global-periodicity/generate-separation-chunks.py
python research/global-periodicity/verify_trace_rigidity.py --lake /path/to/lake
python research/global-periodicity/verify_trace_rigidity.py --lake /path/to/lake --pinned-project /path/to/pinned-kit
python research/global-periodicity/verify_trace_rigidity.py --ambiguity --lake /path/to/lake
python research/global-periodicity/verify_trace_rigidity.py --ambiguity --lake /path/to/lake --pinned-project /path/to/pinned-kit
python research/global-periodicity/verify_trace_separation.py --lake /path/to/lake
python research/global-periodicity/verify_trace_separation.py --lake /path/to/lake --pinned-project /path/to/pinned-kit
python research/global-periodicity/verify_column_separation.py --lake /path/to/lake
python research/global-periodicity/verify_column_separation.py --lake /path/to/lake --pinned-project /path/to/pinned-kit
python research/global-periodicity/column-front-check.py
python research/global-periodicity/incremental-asymmetric-search.py
```

To rebuild the essay, set `RULE30PRIZE_KIT` to a prepared reference kit and
evaluate `Get["build-column-notebook.wl", CharacterEncoding -> "UTF-8"]` from
this directory in a fresh Wolfram kernel with LeanLink installed. The script
uses the official MarkdownToNotebook converter with caching disabled, checks
the embedded source and complete kernel replay, and never submits anything.
`generate-column-essay.py` synchronizes the standalone source and its embedded
Wolfram string if the catalog proof is edited.

In Wolfram, `Get` `wolfram-rigidity-check.wl`, `wolfram-separation-check.wl`
and `wolfram-ambiguity-check.wl`, then evaluate `rigidityReport[]`,
`separationReport[]` and `finiteAmbiguityReport[]`. For the spatial theorem,
load `wolfram-column-front-check.wl` and evaluate `columnFrontReport[]`.
Their saved independent output is versioned alongside
the source. Wolfram observations remain distinguished from all-time Lean
theorems throughout.

## Clean catalog integration

This contribution branch is based directly on upstream commit
`9679f830d345efc7b4e6a5c30dc5468836e30e21` and is independent of the padded-tail
PR. Its six public modules are imported by `lean/Ruliology.lean` and listed
in the catalog README. The complete standalone core catalog builds, and all
six public-module headlines pass unchanged-checker replay on that base.
See `catalog-integration-verification.json` and `integration-evidence/`.

Reproduce this additional integration check with:

```text
python research/global-periodicity/verify_catalog_integration.py --lake /path/to/lake
```
