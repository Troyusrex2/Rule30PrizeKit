# Uniform escape from every fixed right-edge band

The exact canonical bounded-band case is now PROVED, at every width. The
new result is included in the expanded
[PR28](https://github.com/WolframInstitute/Rule30PrizeKit/pull/28), head
b75e62d12ed804bbc81b85a3814f5ff0b242a335. Problem 1, Q01, CQ01 and the
canonical center observer remain open.

## The statement and the missing bridge

In right-edge depths j>=0, let a(t,j)=R_j(U+t) be the actual older canonical
row, b(t,j) any Boolean coefficient field, and h satisfy

    h'(0)=h(0),  h'(1)=h(1)+h(0),
    h'(j+2)=h(j+2)+(1+b(j))*h(j+1)+(1+a(j+1))*h(j).

All arithmetic is F2. For EVERY initial nonzero h, EVERY starting time T and
EVERY depth L, there is a later t>=T and j>=L with h(t,j)=1. In particular,
h cannot eventually stay in any fixed finite band. There is no common-gauge
W premise, no initial subset premise and no evolution assumption on b.

The ordinary-coordinate corollary is checked against the original D update:
for every canonical U>=V, any nonzero initially upper-bounded D field visits
positions p<=U+t-L after every time T, for every L. This means arbitrarily
far BEHIND THE MOVING RIGHT FRONT, not arbitrarily negative absolute positions.

The center is the moving depth U+t. Arbitrarily large depths do not force
a black value at that exact depth. Moreover, the canonical difference itself
already has a moving left edge. The new theorem eliminates fixed-band
auxiliary countermodels; it does not resolve that central observation gap.
It must not be described as a solution of the prize problem.

## The unbounded mechanism

The kit proves periodicity of each fixed right diagonal. At time 2^E, all
depths through E return to the seed prefix. Subsequently that prefix follows
the seed's ordinary evolution. A field confined to a band 0..L-1, L<=E,
would therefore have to avoid the expanding white region above that seed.
Peeling its high cells backward forces them zero. Triangular injectivity
then forces the entire initial field zero.

The finite theorem is explicit: if U+tau=2^E and L<=E, any nonzero field
escapes the band at some time tau+k with k<=ceil(L/2). This is uniform in
U, E, L and the arbitrary second coefficient field. No finite census or
solver verdict is a premise. The proof reuses the known dyadic returns;
no novelty claim is made for that existing background fact.

This proves the exact-canonical version of the previous checkpoint's
bounded-band conjecture. The stronger arbitrary-background conjecture based
only on three initial bits remains UNPROVED; those backgrounds need not
have the required returns to the single-seed prefix.

## Verification and controls

The research source passes full unchanged official kernel replay of 52
declarations. Its catalog integration includes the ordinary-coordinate
bridge and the prior exterior-rigidity result: all 164 declarations and
seven headlines pass, without new axioms, at reference commit
0090056412733accaa27643d3cbbf982104f2251. The core-only catalog build and
check took 7.44 seconds and peaked at 832 MB owned-tree RSS. The catalog
source is 547 lines and its SHA-256 is
4a397a0d6699aa1632b58f4d1d7e74e8a83ebd15471065a6d056b1a15470759e.
Counts include generated declarations and the previous 95 declarations;
copies and integrations are not additional mathematical discoveries.

Independent controls compare 5,280 physical-coordinate D steps, examine
502 initial band states and exhaust 120,903 arbitrary-b transitions. Every
nonzero state exits within the asserted reset window. A known noncanonical
older pair retains its two-cell escaping mode for all 65 tested steps,
checking that the canonical-background condition matters.

The exploratory removal of W still rejected all 43,688 tested prefix cases.
A separate finite solver control also found no periodic mode at five small
widths with b allowed to vary freely. These prompted the simpler proof;
they are not Lean premises, and overlapping cases are not added together.

## Essay preparation

The complete current standalone source has the mandatory `import
Rule30PrizeKit`, embeds the proof and passes all 164 declarations and seven
headlines with the unchanged checker. This took 57.64 seconds and peaked
at 2.79 GB owned RSS. Its SHA-256 is
14d953c5c4eb3aa15f42dabd4702f6bed8500de18b1e7b65600a7ef28233c8f5.

The seven-cell computational essay has a source-exact iconized UNEVALUATED
preview. Packaging passed, with notebook SHA-256
2c7c194f81c7c3984d6cac6f87e3021ce8124f2c69bb19d914c388dcd5f4f6b8.
The Wolfram exploration cells separately pass the center prefix, local gap
and dyadic-return controls. Neither result is a full notebook evaluation.

The full build did not start: 6,361,735,168 available bytes was below the
unchanged 10,500,000,000-byte launch threshold. The engine was not launched
for that build; there is no fresh full-notebook verification and no new API
submission. No memory waiter is running. The older 95-declaration draft was
preserved privately; it is superseded here by the complete 164-declaration
draft, not counted as another proof. The separate PR27 notebook remains
in its earlier pending state.

## Reproduction and next work

Run `python -B verify_artifacts.py` to audit the frozen bytes and exact scope.
Copy work to scratch. Adapt Windows paths while retaining the reference pin
and unchanged checker. The research replay is `guard.py replay.py
Rule30BandEscapeResearch`; the standalone replay is `guard.py replay.py
Rule30Submission`. The latter carries every proof and imports no PR-only
module. `check_catalog.py` documents the separate core-only catalog build.

The current essay is in `work/essay-combined`. Its preview is explicitly
unevaluated. Only `build_combined_essay.py` followed by
`fresh_combined_essay.py`, sequentially under the original guard, can finish
its notebook validation. Do not lower the launch threshold or substitute a
preview, CLI check or exploration pass for that evaluation.

The next mathematical task is the exact canonical zero-center observer or
all-time backward compatibility, not a larger fixed-band census. A possible
route is to extract a confined mode from a hypothetical backward-compatibility
failure, then apply this escape theorem. That extraction is a proposal, not
a proved implication, and backward lifting alone has not been shown to solve P1.
