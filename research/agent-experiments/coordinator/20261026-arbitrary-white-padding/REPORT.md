# Arbitrary finite blocks with sufficiently long white padding

Every finite Boolean word containing a black cell is excluded as the eventual
Rule 30 center-column period when followed by sufficiently many white cells.
The length-dependent bound is explicit, applies to arbitrarily long blocks, and
uses no finite-width certificate. **Prize Problem 1 remains open.** Periodic words
without sufficiently long white gaps are not covered.

For a block of length `n`, define

```text
L(n) = 20n
B0(n) = L(n) + 2^(L(n)+1)
A(n) = 2^B0(n) - 1
W(n) = A(n) + 9n
B(n) = B0(n) + 11n
K(n) = n + B(n)
Q(n) = max(W(n), B(n) + 9K(n))
```

The exact theorem is `CedarPaddingExclusion.not_eventually_padded_word`:
for every `u : List Bool` containing a `true`, and every `q >= Q(u.length)`,
the official `Rule30StripCertificates.EventuallyWord
(u ++ List.replicate q false)` is false. The black-cell hypothesis implies
nonemptiness. Empty and all-white words are not part of this theorem's statement.

## Why the proof works

1. `FrontBlackInterval` gives an explicit white witness in an aged interval of
   left diagonals for every initial Boolean row. Coordinate `i` has period
   `2^i` from time `2^i-1`. Clock inheritance and the white causal interior of
   a hypothetical black interval yield the witness.
2. `PhysicalEarlyCases` and `CedarPhysicalAgeBridge` transfer this to the
   physical Rule 30 orbit. After `W(n)` white center ticks, each of the next
   `n` times has a white cell at some position `1 <= p <= B(n)`. This theorem
   places no restriction on the next `n` center bits. The global reference
   configuration starts at the original time; only the final witness crosses
   the finite causal comparison. No finite cone is treated as an all-time clock.
3. `PhysicalCapture` uses that white witness at the block's last black tick
   to bring a black cell to column 1. The following white gap preserves this
   black cell and the official black-shield theorem regenerates an alternating
   stripe, including the next period's boundary time.
4. Equal stripes and equal periodic center drivers give equal early responses
   in column 1. Its later responses are black. `phase_periodic` proves agreement
   at **every** time from `T+2P`, not merely at period starts. The official
   `Rule30Jen.not_adjacent 0` contradicts eventual periodicity of both columns.

## Linear maintenance after entry

`PhysicalMaintenance.maintain` is a separate, conditional result. Let `N >= 1`,
`K = 2N+1`, and suppose the alternating stripe is already present at positions
`1..2K+1`. Every black-containing block of length at most `N`, followed by
`q >= 19N+10` white ticks, restores that same stripe at its endpoint and makes
column 1 black from phase `K` through the endpoint.

`response_agree` compares the full column-1 responses to the same block, even
when the two admissible padding lengths differ, through their common endpoint.
Only the finite driver segments are assumed; future blocks are unrestricted.
The proof uses an even white cell in the incoming stripe, so it does not depend
on the enormous aged-diagonal warmup bound.

This is a preservation theorem, **not automatic entry with linear padding**.
A complete finite-mixture exclusion is not claimed in this archive.

## Verification and provenance

All six exact source modules were independently rebuilt by the coordinator and
passed the unchanged official `Check.lean` at repository pin
`5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0, verifier image 9.
No worker compiled objects, new axioms, admissions, or native decision shortcuts
were used. Own previously checked dependencies were reused where applicable;
their exact sources are included here.

| Module | Replayed module constants, including internal proof constants |
| --- | ---: |
| FrontBlackInterval | 57 |
| PhysicalEarlyCases | 54 |
| CedarPhysicalAgeBridge | 91 |
| PhysicalCapture | 64 |
| CedarPaddingExclusion | 52 |
| PhysicalMaintenance | 54 |

These counts are not numbers of handwritten theorems and do not count imported
modules. Separate source audits checked the physical bridge and complete padded
word argument, including their quantifiers and endpoints. The sealed exclusion
delivery's 73 artifact hashes also passed independent verification. The archive
includes replay logs, checker JSON, resource-guard receipts, and source audits.
Its hash verifier checks archived evidence; it is not itself a Lean proof replay.

The abstract clock ingredient is the official `Rule30Diagonals.transducer_periodic`.
Physical capture generalizes nearest-black and white-run arguments in the
officially verified public contribution `8cca17`, superseded by the import-only
revision `4d375d`. The final contradiction and black shield use the official
Jen and black-run modules. No claim of literature priority is made.

Research coordinated for Troy Lowry with OpenAI Codex and collaborating agents.
The aged-diagonal component also has a catalog submission:
[PR34](https://github.com/WolframInstitute/Rule30PrizeKit/pull/34).
Local official-checker success does not assert Wolfram backend evaluation,
maintainer acceptance, or a prize award. No new essay was submitted for this archive.
