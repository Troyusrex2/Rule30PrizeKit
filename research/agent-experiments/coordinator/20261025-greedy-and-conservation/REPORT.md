# Uniform conservation classification, exact ancestry front, and inverse design

Troy Lowry and Codex, 25 October 2026. **Problem 1, Q01 and CQ01 remain open.**
These are new locally checked research additions after the seven-agent
[round-two review](../20261025-round2-review/REPORT.md), not a prize solution.

The main formal result removes the arbitrary-window cutoff from one algebraic
question in the backend response: **at every positive window width, an integer
density conserved by four Rule 30 steps on all closed overlapping-word walks
is exactly a constant plus a shift coboundary**. The local-current premise has
been eliminated constructively. Both directions of the classification pass
the full unchanged checker. This closes that precise conservation question;
the proposed implication from a physical ranking premise to this class is
still unproved. It does not exclude all possible ranks, readers or invariants.

A separate checked ancestry theorem gives an exact greedy update for the
rightmost descendant of the least disagreement source. Experiments validate
the implementation on canonical seed pairs, while periodic-background controls
show why the local update alone cannot yield positive drift. A new inverse
design experiment tests whether the earlier troublesome driver traces are
actually compatible with the coupled right half. It has produced finite
models and failed traces, not an infinite counterexample or positive bound.

## Exact conservation statement and proof

For a Boolean input word X of length m+8, `image X` is a word of length m
obtained by four shrinking Rule 30 updates, and `crop m X` is the old m-cell
window starting at offset four. `image_eq_four` proves this semantic equality
for every word length using the official `Rule30Jen.rule`.

`CyclicConserved m h` means the following exact finite-word condition. On
every closed walk whose states are Boolean words of length m+7, append a
bit, score `h(image X)-h(crop m X)`, and drop the first bit. The sum of these
changes is zero. These are closed walks of overlapping input windows: the
usual cyclic spatial windows, with the conservation condition expressed
without a separately supplied current.

The headline is `cyclic_conserved_iff_trivial`: for every m>0 this condition
is equivalent to existence of an integer c and a word function B with

```
h(v) = c + B(v.tail) - B(v.dropLast)     for every word v of length m.
```

Consequently every cyclic rolling-window score is c times the cycle length;
the boundary terms telescope. No positivity or boundedness of B is assumed.
Values of these word functions on other lengths are irrelevant. This is an
integer, four-step theorem. No separate real/rational-valued classification,
physical-rank reduction, or bi-infinite configuration API is claimed here.

The proof is uniform in m, not an enumeration of widths:

1. A constructive preimage realizes every desired interior output word with
   eight white trailing input cells. Two outer input bits then vary the two
   endpoint outputs independently, leaving that interior arbitrary.
2. Four endpoint choices in the conservation equation cancel the current and
   old density. The mixed endpoint difference of h vanishes at every width.
3. An explicit gauge writes h as a shorter density plus a boundary difference.
   The transported current is proved independent of its last input bit, so
   the conservation equation survives shortening. Induction reaches one cell,
   where conservation forces both values to agree.
4. A generic directed-word lemma constructs the current from zero closed-walk
   sums by comparing two loops through an all-white state. Conversely all
   constant-plus-boundary densities satisfy the local and cyclic equations.

The all-white-state graph argument is standard mathematical structure, and
the conservation-law literature predates this work. Hattori and Takesue give
local continuity conditions for additive conservation in their
[1991 paper](https://doi.org/10.1016/0167-2789(91)90150-8); Takesue recalls this
construction in [Staggered Invariants](https://content.wolfram.com/uploads/sites/13/2018/02/09-2-3.pdf).
Kari and Taati prove a broader absence-of-conservation theorem under strong
transitivity in [Theorem 47](https://arxiv.org/html/1311.2319#S4.SS3).
We do not establish that theorem's dynamical hypothesis for Rule 30 here or
claim literature novelty. The contribution is the supplied direct uniform
Lean proof for the stated class and its use in evaluating our proposed route.
Credit the backend agent's R2 conservation question for motivating this step.

## Exact greedy ancestry and the open growth premise

The ancestry module builds on Cedar's checked selected-parent construction
and the round-two least-root recurrence. If r is the rightmost descendant of
the least initial source, that source's descendants are exactly the current
disagreements at positions <=r. At the next time they are exactly the next
disagreements at positions <=r+1. Thus the new frontier is the rightmost next
disagreement at or to the left of r+1. It can retreat; the theorem hides no
lower bound on its displacement.

In the packed canonical pair at onset T and lag P, let F=T+P and use

```
A0 = Phi^T(1) << P; B0 = Phi^(T+P)(1); Phi(a)=a XOR ((a<<1) OR (a<<2)).
j0 = 2*F
j_next = j + trailing_zero_count((Phi(A) XOR Phi(B)) >> j)
front(t) = -F + t - (j(t)-j0).
```

The independent physical-coordinate and selected-label simulation agrees on
384 small steps. All small test cases also compare the greedy representation
with the entire root mask. All 99 stress pairs hit the center within the
chosen horizons, including T up to 65535 and P up to 4096. The largest observed
first hit is 132637. These are finite observations, not an escape theorem.

The missing fact is a uniform bound on accumulated skipped zero cells that
forces the front to reach the center. It cannot follow from the local Rule 30
update in unrestricted backgrounds: all 93 tested phase/residue front cycles
between two infinite periodic ether histories are stationary. One explicit
same-center control cycles through fronts -3,-2,-1,-4. These use coarsened
left/right source labels on infinite periodic backgrounds, not a minimal
source in a canonical finite seed pair. Their finite-state computations and
semantic argument are not Lean premises. They show why actual seed history
and finiteness must enter a proposed progress proof.

## Inverse design and language refinement

The earlier explicit Golden trace with spatial density 3/14 contains the
already checked forbidden coupled word `010110` at index52. Its failure of
the broader Golden density floor therefore does not challenge the actual
finite-right charge target. A new randomized search enforces all four checked
exclusions `00`, `11111`, `010110`, `1011010`, and still finds a full temporal
state cycle with six black outputs per28 spatial cells. Its entry is at depth
1108, with a 192-time prefix and period-four tail. Thirty-two scalar columns
independently check the packed reconstruction. This is again an explicitly
defined stream, not an actual finite-right driver.

Full causal-cone inverse constraints then report that its first12 bits cannot
come from any right half. This is an unverified solver report, not a Lean
exclusion. A counterexample-guided experiment proposes nine additional
forbidden words, each from a full finite cone. They are heuristic constraints
until kernel checked and are not imported by any proof in this archive.

A later candidate survives all thirteen word constraints and has the same
3/14 spatial cycle. Exact inverse design finds finite starts matching its
first32 and40 free bits, independently replayed in packed and physical
coordinates. Those actual starts depart from the target at indices36 and40;
their n=5000 measurements have negative C=3 excess even with allowance zero.
These finite measurements establish no asymptotic bound. The solver reports the target's first48 bits impossible. Again that
last statement is a solver result, not an accepted proof. No actual infinite
finite-right counterexample was obtained, and C=3 remains open.

This exercise changes the experiment: a low-density trace must pass actual
right-half compatibility, not merely a Golden grammar or a few forbidden
words. It does not justify enumerating more excluded words as prize advances.
Several deliberately larger inverse jobs timed out. Unknown results are
recorded as unknown. A full256-cell cone with irrelevant future constraints
timed out even at eight requested bits; exact-size independent cones avoided
that modeling overhead. The bit-zero boundary in the initial packed control
was corrected before the final recorded job and independently replayed.

## Validation and limits

Seven new modules passed full local replay: **199 owned declarations**,
including generated/internal declarations, not199 discoveries. The source
build logs are warning-free. All headlines import the official statements,
have only standard axioms and no new axioms, and use `--claim partial`.
The checker itself retains its existing deprecation warning.

| Module | Replayed declarations |
|---|---:|
| Rule30GreedyAncestryFrontResearch | 9 |
| Rule30ConservationCornerResearch | 63 |
| Rule30ConservationWordResearch | 25 |
| Rule30ConservationDescentResearch | 26 |
| Rule30ConservationTrivialityResearch | 25 |
| Rule30ConservationCycleResearch | 36 |
| Rule30ConservationClassificationResearch | 15 |

Pin: `3eca23c0a9fa6b153313655e6d51835406c2d06e`, Lean4.35.0. Unchanged
checker SHA-256: `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
The independent corner controls check all512 nine-cell inputs against four
physical updates,3120 interior/corner realizations,3120 nontrivial boundary
score identities and780 negative endpoint-product tests. Experiments and
solver answers remain distinct from the kernel proofs.

All final jobs completed within the300-second,8-GiB owned-tree RSS and2-GiB
minimum-free-memory guards. Solver package Z3 5.3.2.0 was installed only in
the private task directory; no binaries, credentials or machine configuration
are published. The reference refresh still listed45 public submissions at
13:34 UTC, with no new entries relative to the previous review.

See [REPRODUCE.md](REPRODUCE.md), [proof-summary.json](proof-summary.json), raw
reports/logs and [artifacts.json](artifacts.json). No new prize essay or PR was
submitted. Earlier archives and incoming agents' directories were untouched.
Next work must supply actual least-source escape, physical coupling/capacity,
or unbounded odd-source rank growth. None is established here.
