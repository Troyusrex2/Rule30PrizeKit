# Ancestry corrections and an unproved safety classification

Problem 1 remains open. This checkpoint adds experimental evidence and a
fully replayed external contribution; it adds no new Lean theorem of ours.
The two uniform clock lemmas in the preceding archives remain unchanged.

## Correction to the previous interpretation

The stored six-cell mode collisions from the previous checkpoint do not
establish that a global white-boundary argument is necessary. Both fail
when extended by just one older cell: the oldest supplied profile n is
black at a time when the derivative of m is zero. No older input can fix
that violation of `m' = m XOR (n OR o)`.

That does not invalidate the earlier clock proofs or the precisely stated
six-cell counterexamples. It limits their interpretation. They refute an
inverse on that six-cell relaxation; stronger local constraints can reject
them before any white boundary is imposed.

We therefore tested arbitrary-clock older extensions. At P=16, with k
anti-8 and l 8-periodic, a time-phase product graph considers all possible
older inputs, without forcing their periods to divide P. Among 576 k/l
pairs, 576, 320, 240 and 112 survive older strips of widths 4, 5, 6 and 8
ending at k. At the final width no S-to-q collision survives. Both phases
of h are checked. This is a finite-clock result, not a uniform inverse.

At larger clocks, cyclic SAT finds and literally checks collisions in
total strips of width 10 and 12. The two oldest inputs remain arbitrary.
These examples show that the extra local test at clock16 does not extend
unchanged to the larger tested clocks. They do not prove failure of every
fixed local context. Four SAT searches with a genuine white boundary,
including actual mode collisions and adjacent period drops, all time out
after 8 seconds; none establishes SAT or UNSAT.

## A cubic mode decoder fails

This test concerns q from the lower readout S, distinct from the older
cubic decoder of the raw head. Cubics interpolate the tested mode targets
at clocks4,16,32. At clock64 the 41,792 observations have cubic rank41,600,
and q(0) is outside that span. A compact witness contains 20,726 literal
finite parent words. Its XOR annihilates all 43,745 monomials of degree at
most three in S, but sees q(0). A separate script checks all those moments,
2,652,928 packed scalar prefix updates, cyclic returns, canonical status,
and the older prefix's clock. These are exact Python checks, not Lean.
This refutes only the cubic template, not an unrestricted mode observer.
No larger polynomial-degree search is proposed here.

## New safety target, not a theorem

Let F update a finite Boolean word from older to newer cells, with white
cells outside its older end:

```text
F(x)[0] = x[0]
F(x)[1] = x[1] XOR x[0]
F(x)[j] = x[j] XOR (x[j-1] OR x[j-2])  (j >= 2).
```

Call a nonempty word safe when its newest cell never has two consecutive
white observations. Equivalently, for widths at least3, the newest three
cells never are all white. The conjecture is:

**For every finite nonempty word x, safety implies `F^8(x)=x`.**

The weaker guess that only period2 occurs is false: the six-bit word with
integer encoding33 (`[1,0,0,0,0,1]`, older first) has a safe period8 trace.

We decomposed every orbit of all 4,294,967,296 words at width32, without a
time or period cap. There are 773,950 orbits; the largest period is131,072.
Exactly339 words lie on safe orbits. A proposed 13-state DFA accepts exactly
those339 words. Independent literal-cell checks establish that every
accepted word through width32 returns after8 steps, and a separate complete
literal orbit enumeration agrees on every word through width12. The DFA
is constructed from the earlier sound reader and eleven six-bit reference
words. Its all-width completeness is NOT proved.

The width30/32 stress job took42.397s and peaked at4,425,486,336 bytes on
G913, within the unchanged8-GiB research guard. Earlier selected widths6..26
agree. Canonical safe words have their first black cell within the newest
six cells in these tests. The maximum finite safe run at width26 is116;
this does not establish a uniform linear escape bound.

One additive DFA-score ranking template and four positive discounted
variants are infeasible by exact rational SMT. This excludes only those
specified sufficient systems, not all ranks or the conjecture. No uniform
proof or direct implication for the physical center is claimed. F follows
a moving diagonal; it is not observation at a fixed physical column.

## Fresh external work and public activity

During this audit [PR31](https://github.com/WolframInstitute/Rule30PrizeKit/pull/31)
appeared, by **AIOvernight with Claude, with independent Codex review**.
Its head is `16250824c5e80964495ca5ba6bb82fa69394a35a`.
We fetched the exact Git objects and separately replayed both new modules
against the unchanged checker at kit5473ffd0, Lean4.35.0:

- `WhiteEndNineChecks`: all38 constants, seven selected headlines;
  build42.617s plus replay41.993s, guarded peak3,964,104,704 bytes.
- `Rule30WhiteEndNine`: all29 constants, four selected headlines;
  the complete guarded job took34.065s, peak784,101,376 bytes.

All pass with no new axioms. These are their67 constants, not ours.
The result excludes eventual `1 0^q` for all q>=9. More generally,
`not_eventually_word_mode` proves soundness of a mode certificate for any
word, strip width, warm-up and selected white phase. It permits one
ambiguous phase whose labels obey 1->0 and 00->0, forcing eventual
2-periodicity of the adjacent OR observation and contradicting Masked Jen.
This differs from our lower-readout mode; they are not identified.

At the14:26UTC public-feed refresh there are41 entries,38 under other
authors' bylines. Three currently listed Troy Lowry submissions all carry
Lean Verified, Human Verified and Kit Contribution tags. The GitHub audit
finds15 PRs from Troyusrex2 (including revisions/replacements,7 open),
and15 from other accounts. Before this checkpoint the public coordinator
history has61 commits. PR29 explicitly credits and reuses our finite-clock
machinery. Private work is outside the visible record.

No new prize submission or PR accompanies this checkpoint. The prior3,081
selected hashes across37 archives were checked unchanged. See
[BRIEF.md](BRIEF.md) for the next targets and [REPRODUCE.md](REPRODUCE.md)
for exact validation scope.
