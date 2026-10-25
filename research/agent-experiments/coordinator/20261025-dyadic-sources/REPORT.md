# Dyadic run-boundary sources and a failed determinant-wall rule

Troy Lowry and Codex, 25 October 2026. **Prize Problem 1 remains open.**
This archive has one new uniform seed-source theorem and finite diagnostics.
It is not a prize submission, an accepted catalog contribution, or a full proof.

## Kernel-checked result: one selected source in a growing strip

Let `R(d,s)=cell(s,s-d)` be the official right-edge diagonal. Define the
actual black-to-white run-boundary source

```
b(d,s) = cell(s,s-d) AND NOT cell(s,s-d+1).
```

The local identity is `rule30(l,c,r)=(l XOR r) XOR (c AND NOT r)`.
In the [Lean source](work/Rule30DyadicSourceResearch.lean), `source_physical`
links the diagonal definition to these actual cells and
`rule90_source_identity` proves that identity for every neighborhood.

For `H=2^e`, consider source times `s<2H-1`, depths `d<=e`, and the explicit
binary mask

```
d even,    (H-1-d/2) AND (2H-2-s) = H-1-d/2.
```

**`selected_event_iff_outer` proves, for every e, d, s with d<=e, that the
mask selects a nonzero actual source exactly when d=0 and s=H-1.** Both
scale and strip depth are unbounded. This is not a finite-depth certificate.
The proof uses the catalog's right-diagonal periodicity and finite seed cone.
All diagonal bits up to depth e are black at phase H-1. At positive depth
the run-boundary source therefore vanishes at that phase; just after H,
the early seed cone also makes it vanish. The binary mask can select only
those times or an early time outside the cone. At depth zero it selects
exactly s=H-1, where the outer source is black.

The unchanged official checker at commit
`3eca23c0a9fa6b153313655e6d51835406c2d06e` freshly replayed **56 owned
declarations**, including generated constants, and accepted all four
headlines with no new axioms. [Raw report](work/evidence/Rule30DyadicSourceResearch/report.json).
The final build had no source warnings; the checker printed its existing
replay-deprecation warning. Guard: 16.875 seconds, about 1.16 GiB peak owned
RSS, normal exit. The first draft incorrectly imported a non-module umbrella;
the final module imports the official core Prize and Diagonals modules.

**Formal scope matters:** the theorem is about that exact binary mask.
The expected interpretation as a Rule90 binomial Green-function support
has independent finite checks and the derivation below, but its full
Duhamel bridge is not formalized here. No conclusion about the full center
sum or sources deeper than e has been proved. We are carrying this as a
research module until that bridge and its usefulness are assessed.

## Different source expansion, and the cancellation it must handle

Pack the physical seed row as `F_s(x)`, bit i representing position i-s.
Then Rule30 is `L90(F_s)+S_s`, where `L90=1+x^2` and the run-boundary source
is `(a<<1) AND NOT a`. Its rightmost wall is the monomial `x^(2s+1)`.
The entire propagated outer-wall polynomial has the elementary closed form

```
Outer_n(x) = sum(s<n) x^(2s+1) (1+x^2)^(n-1-s)
           = x*((1+x^2)^n + x^(2n))                 over GF(2).
```

The geometric sum telescopes because `(1+x^2)+x^2=1`. Thus the outer
center signal is 1 exactly at positive n=2^k-1: for odd n=2m+1 its
coefficient is `choose(2m+1,m) mod 2`, and Lucas' criterion gives
`m AND (m+1)=0`. Even n give zero. This algebraic derivation is not a
separate Lean theorem in this archive. All 65,536 full polynomial
decompositions and outer formulas were checked exactly.

An odd boundary signal can be cancelled. **At n=7 exactly two active
source events contribute:** the outer source at (s=3,p=3), and an interior
source at (s=5,p=1). Their XOR is zero, the actual center value. The source
presence argument therefore fails already at time 7.

For positive even depth d=2r and n=2^k-1, put H=2^(k-1). The binomial
support restricts the contribution to times `H-1+r-u`, for submasks u of r,
or early times where the source is already zero. The Lean theorem proves
pointwise source vanishing at depths d<=k-1, rather than merely cancellation
within a strip. Consequently the intended fixed-strip contribution is
eventually just the outer 1. The unrestricted interior can still cancel it.
This observation does not prove infinitely many zeros at these dyadic
times, and it does not exclude an eventual center period.

## Finite validation and falsification

- `number_wall.py` tested D(n,t)=det(c(t+i+j)) over GF(2). Its proposed
  next-scale rule from only a 3x3 coarse patch fails for all four fine
  parities. For example the same patch at (n=2,t=5) and (n=2,t=16) predicts
  different D(4,10) and D(4,32). All eight reported Rule30 / complemented
  source-sequence contradictions were independently checked using physical
  cells and the Leibniz determinant formula. This refutes this particular
  patch rule, not every tiling or finite-state representation.
- Leading determinant diagnostics used 65,536 center bits. The 64-bit
  fingerprints of dyadic subsequences are all distinct at each tested
  level, giving 1,2,4,...,256, versus two at levels 1..8 for the Thue-Morse
  control. This is finite evidence, not nonautomaticity. Leading values
  were extracted with Berlekamp-Massey; 5,120 exhaustive short determinant
  checks, 4,096 Leibniz checks, 4,288 direct elimination checks and 260,096
  division-free Jacobi identities passed. No large determinant theorem is
  inferred. Periodic and rules 90/150/210 controls behaved as expected.
- `source90.py`: 4,096 local-row identities, 129 physical seed steps,
  128 direct polynomial convolutions and 65,536 complete polynomial splits
  passed. `dyadic_strip.py` checked 20 depth channels through time 65,535,
  the sampling formula and pointwise zero predictions.
- `control_selected_events.py` used the opposite, official right-edge
  packing and checked 21,810 event predicates, with 1,858 binomial/mask
  comparisons, independently of the channel implementation.
- All six final guarded jobs exited normally within 300 seconds, 8 GiB
  owned RSS and 2 GiB system-free limits. No unrelated process or computer
  setting was changed. The G913 was not used.

The 15:45 UTC public refresh still has 45 submissions, the same verifier
pin, and no new, removed or changed entry (including existing statuses and
source fields). No external unverified result was adopted. No new essay,
API submission or pull request was made for this batch.

The next proof task is the exact Green/Duhamel bridge. The mathematical
obstacle after that is control of the deeper source remainder, rather than
another finite strip or determinant table. The full goal remains active.

## References

The existing [catalog](../../../../equivalents/CATALOG.md) already has
the center Duhamel identity and unbounded Hankel-rank equivalents; neither
is claimed as new. Number-wall motivation: [Lunnon, 2009](https://arxiv.org/abs/0906.3286)
and [Han, 2014](https://arxiv.org/abs/1406.1586). The incoming sanity-agent
source-parity proposal motivated this change of expansion. Previous
[source-parity discussion](../20261025-round2-review/REPORT.md) records the
different Rule150 cancellation controls. No historical novelty claim is
made for elementary binomial or geometric-sum identities.
