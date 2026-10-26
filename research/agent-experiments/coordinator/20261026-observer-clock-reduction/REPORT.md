# A one-bit observer criterion, a clock inverse lemma, and cubic filters

Two new modules passed the unchanged reference Lean checker. One proves
that reconstructing just the penultimate initial bit of canonical rows,
uniformly over all widths, is equivalent to full sound-reader completeness.
The other proves a uniform OR inverse lemma for a clock-extending column
and formally refutes a proposed local extension to the plateau case.

**The uniform decoder remains open. This is not a proof of reader
completeness, Q01, or Prize Problem 1.** No prize submission, Wolfram backend
verdict, human verification, or mathematical priority is claimed.

## The narrower all-width target

The preceding checked canonical language is

`C = 0* Sigma^{<=2} union 0*1(00|11)Sigma+`.

The formal definition is the seven-state DFA in the byte-identical
`Rule30ReaderCanonicalResearch.lean`. Every word has a unique
reader-equivalent canonical word; normalization commutes with the sheared
white-boundary update. Its trace is the final bit after each update.

`Rule30ReaderObserverReductionResearch.ParentBitObserver` asks only this:

> If equal-length canonical rows `xs ++ [x]` and `ys ++ [y]` have identical
> final-bit traces at every time, then the final initial bits of `xs` and
> `ys` agree.

`parent_bit_complete_reduction` proves this property **if and only if** the
sound reader is complete at every width. Thus an explicit uniform filter
recovering that single previous bit would suffice; it need not reconstruct
all coordinates in one formula. The property itself is not proved here.

There are two substantive steps in the reduction:

- `extension_words`: an accepted reader prefix extends to an accepted word
  if the appended head agrees at times 0, 1 and 2. A 250-state, two-update
  memory automaton proves this for arbitrary word lengths. Its closure and
  output checks are split into five chunks each to keep kernel memory low.
- Time covariance upgrades one-bit reconstruction to the whole parent
  trace. Induction then normalizes the shorter prefixes and uses the
  extension certificate. This handles the fact that truncating a canonical
  word need not leave a canonical word, and that the reader has a core
  alias for which a naive append argument fails.

`same_snoc`, `parent_observer_iff`, and `parent_bit_complete_reduction` state
these steps explicitly. Their dependencies retain all hypotheses from the
earlier canonical and soundness proofs.

## A uniform nonlinear OR inverse

For temporal profiles `g,h`, write `r(t)=g(t) OR h(t)`. Suppose

`g(t+P)=NOT g(t)` and `h(t+P)=h(t)`.

Then the exact identity is

`r(t) XOR r(t+P) = NOT h(t)`.

`Rule30OrClockObserverResearch.older_recovered` compares a second
realization with a constant half-clock flip flag. If `h` has at least one
zero, equality of OR traces forces that flag to be one and recovers `h`.

The newer profile is recovered using a separate uniform lemma:
`hidden_difference_impossible`. When a shared mask is black, both newer
profiles must flip at the next step. A difference hidden behind the mask
would therefore persist forever. Periodicity supplies a future zero in the
mask, where equal OR outputs forbid that difference.

`actual_or_clock_observer` applies this to arbitrary actual white-boundary
Rule 30 rows. The second row's flip flag follows from the proved
`shift_flag` lemma for periodic xor drivers. Its premises include a common
period for the relevant older profiles, antiperiodicity of the first newer
profile, and a zero in the mask. The period is any positive natural number;
it need not be least or dyadic. The theorem resolves this clock-extending
case, not every inverse edge.

The zero premise matters: two opposite alternating newer profiles hidden
behind a constantly black mask have identical OR traces. The independent
controls include this negative example.

## Why the plateau case needs more than a local band

A proposed weakening used antiperiodicity of the older column while the
newer column merely had the same full clock. It failed even with two exact
Rule 30 equations and periodic upstream inputs. A fixed counterexample has
period eight and driving half-clock four:

| Side | Newer g | Older h | Upstream k | Upstream l |
|---|---|---|---|---|
| A | 01010111 | 01101001 | 10011001 | 10101010 |
| B | 00110101 | 01001011 | 01010101 | 11001100 |

Both OR traces are `01111111`, but the newer profiles differ. Both `h`
profiles flip after four steps, `k,l` repeat after four, and both equations
`g'=g XOR(h OR k)` and `h'=h XOR(k OR l)` hold cyclically at every time.
`plateau_local_counterexample` and `band_facts` prove these assertions for
all natural times in Lean.

These bands have **free upstream inputs**. They do not certify a finite
white spatial ancestry and do not refute the canonical observer. They
prevent using that weaker local statement as an unbounded inverse proof.

## New finite evidence: cubic temporal filters

On all canonical rows of a fixed width, form the Boolean function space
generated over F2 by constants, final-bit observations at every time in a
working period, and products of at most three such observations. The new
experiment found every canonical raw coordinate in this cubic space for
each tested width **3 through 14**. This includes the penultimate bit needed
by the new reduction.

This is a **conjectural route**, not an all-width theorem. Two GF(2)
implementations agree on all common layers through width 13. The compiled
implementation also checks raw coordinates and completes width 14. At
width 14 there are 8,192 canonical rows; the degree-1/2/3 space dimensions
are 130, 3,106 and 7,073. The cubic space is not the full function algebra,
yet it contains all the coordinate functions in that finite test.

For something inspectable beyond ranks, `newton-decoder-filters.json`
contains explicit filters for the penultimate bit at widths 4 through 10.
Define `d[k] = XOR { f[i] : i is a bit-subset of k }`. The filters use XOR
of products of at most three `d[k]`. Since each `d[k]` is linear in trace
bits, these remain degree at most three in the trace. The filters contain
respectively 1, 4, 7, 19, 30, 63 and 132 terms. Independent literal
truth-table trajectories validate every filter on every canonical row at
its width: 1,016 rows and 443,648 Rule 30 cells in total.

Already at width five, an affine parity-only decoder cannot recover the
penultimate bit. Four canonical rows `11101`, `00011`, `01111`, `11111`
have full eight-step head profiles whose XOR is zero, but their penultimate
bits XOR to one. Four rows also cancel any affine constant. The literal
certificate is `penultimate-linear-negative-control.json`. This refutes
that decoder template, not observability or a different encoding.

The earlier three-state Mealy probe is also included. Its complete closed
automaton on positive compositions of length at most eight has 9,841
different actions; no short relation was found to simplify return sections.
There are 15,246 literal/section controls. This is a bounded composition
experiment, not global semigroup freeness or a general impossibility claim.

## Full-kernel and independent validation

All six modules were freshly rebuilt and fully replayed on G913 against
kit `0090056412733accaa27643d3cbbf982104f2251`. The unchanged checker hash is
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

| Module | Replayed declarations | Headlines | Source SHA-256 |
|---|---:|---:|---|
| CommonPast | 100 | 7 | `17eb07047e8b1780b25de532e72dcb73385f20eaffa91db366e92c210b394ec3` |
| ColumnReader | 119 | 3 | `ad1d09b6d460b1849017fcf7c99151ad0304ceee8dfc80e78f43bfc1a917da3b` |
| ReaderEquivalence | 83 | 5 | `574920fd28265f590b6f030784bb22979770f0fb1da023f328825bc3cade6dd7` |
| ReaderCanonical | 215 | 7 | `832fd7632331f8ad6101bc4725a7b954e81e692843017c7df529a52a3901641a` |
| OrClockObserver | 24 | 6 | `9928288f7c038406e6979852d845f6de17a5d8f887bddefe3d31494e2b8b83c2` |
| ReaderObserverReduction | 129 | 4 | `ed0266339602889151012650bc5b0fe0a53c46d7d706c29a44544f5e7b41f805` |

Every declaration passed kernel replay with no new axioms. The new
observer-reduction module takes about 26 seconds and 1.71 GB sampled owned
RSS; the OR-clock module about 1.7 seconds and 0.78 GB. The original guards
remain 300 seconds, 8 GiB owned RSS and a 2 GiB minimum free-memory floor.
No skipped kernel checks, custom axioms, native decision shortcuts, changed
official statements or checker modifications were used.

Independent inverse controls cover all admissible periodic pairs at clocks
1 through 7 and 508 periodic xor-driver cases, including odd clocks and the
constant-mask negative example. Local Wolfram Language 15's built-in
`CellularAutomaton[30,...]` checks 510 initial rows, 2,568 older-profile pairs
and 404 antiperiodic instances, with 2,924 mask-recovery comparisons. These
are local software controls, not a cloud/backend verification.

The public list and response inbox were refreshed at 2026-10-26 08:55 UTC:
40 public entries, no new or changed entries, no new READY responses or
revisions. The reference pin and skill 1.17.3 are unchanged.

## Remaining work

The best next target is a uniform penultimate-bit decoder, or a
counterexample to the cubic conjecture. The current finite filters have no
proved coefficient recurrence. A proof must retain the white ancestry and
canonical hypotheses; the free-band counterexample shows why two local
equations are insufficient. More finite ranks alone will not prove it.

Full reader completeness would activate the already checked collision-clock
and finite-defect preservation bridge. Connecting the sheared system to
the fixed physical center is still a further open step. The prize objective
is unchanged. Sources, diagnostics, full reports, guards and hash checks
are archived here; all older archive hashes remain unchanged.
