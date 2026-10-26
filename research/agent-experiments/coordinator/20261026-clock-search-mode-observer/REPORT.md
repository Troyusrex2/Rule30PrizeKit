# A finite-window clock decoder and a lower-clock mode observer target

Three new modules passed full kernel replay: a computable decoder in the
clock-extending case, exact identities and parity constraints for a
lower-clock plateau observation, and generic cubic-annihilation transfer.
There are 97 new declarations. All 41 research modules in this dependency
set, totaling 1,068 declarations, were rebuilt and replayed against the
official verifier's newly deployed kit commit.

**The unrestricted observer, the fixed-center bridge and Prize Problem 1
remain open.** The promising mode-observer test below is finite evidence,
with an additional ancestor-clock restriction. No prize submission, new
pull request, backend verification or new result in the official catalog
is claimed.

## An explicit decoder with a proved observation window

Let consecutive profiles be `c,g,h,k`, with

```
c(t+1) = c(t) XOR (g(t) OR h(t)),
g(t+1) = g(t) XOR (h(t) OR k(t)).
```

Suppose `P>0`, `g(t+P)=NOT g(t)`, `h(t+P)=h(t)`, and `h` has a zero.
Then `Rule30ClockSearchResearch.actual_head_clock_window` gives a
computable recovery of `g(0)` from the head observations `c(0),...,c(2P)`.
The algorithm computes `r(t)=c(t+1) XOR c(t)`, compares `r(t)` and `r(t+P)`
for `t=0,...,P-1`, and stops at their first mismatch `u`. Its answer is
`r(u) XOR (u mod 2)`.

The proof explains termination and correctness. The comparison equality
is exactly `h(t)`. Before its first zero, `h=1` forces `g` to flip at each
step. At the zero, `r=g`. Periodicity moves any zero into the first `P`
positions. `decodeHead_congr` proves that no observations after time `2P`
are used. This is a decision-list algorithm whose length grows with the
clock; it is not a cubic polynomial filter.

Every clock and zero assumption remains explicit. The decoder does not
handle the plateau case. Independent Python controls checked 1,302
admissible periodic-driver cases and 23,940 phase/horizon comparisons,
including counterexamples when each structural premise is omitted. Local
Wolfram Language 15 tests used built-in `CellularAutomaton[30,...]` on
1,022 initial rows: 916 qualifying cases and 25,440 comparisons passed,
including decoding from head differences.

## A precise lower-clock observation for the plateau case

Write consecutive actual profiles as `g,h,k,l`. Assume

```
h(t+P) = NOT h(t),
k(t+P) = k(t),
g(t+2P) = g(t).
```

Define the observable and hidden mode by

```
r(t)   = g(t) OR h(t),
rho(t) = r(t+P) XOR r(t),
q(t)   = g(t+P) XOR g(t),
S(t)   = NOT (rho(t+1) XOR rho(t)).
```

`Rule30ClockModeResearch.actual_lower_observer_data` proves

```
q(t+1) = q(t) XOR NOT k(t),
S(t)   = q(t) OR (NOT k(t) AND NOT l(t)),
q(t+P) = q(t).
```

`lower_readout_parity` proves that the cyclic XOR of `S` over `P` steps
equals the parity of `P`; in particular it is zero for `P=2n`.
`older_recovered_of_modes_equal` proves that equal recovered mode traces
would recover `k`, since `k(t)=NOT(q(t+1) XOR q(t))`.

**No theorem recovers `q` from `S` here.** The mode is not asserted to be
an actual row, and this observation is not asserted to lie in the original
observer's input class. A uniform reconstruction theorem would need a
proved class of admissible modes, with its finite white ancestry retained.
Even then, extension/clock arguments and the fixed-center bridge would
still require proof.

## Finite evidence for the new target, and failed shortcuts

`mode_descent_probe.py` exhausts fixed-clock white-prefix graphs, then
appends `h,g` and a white head, retaining canonical initial words. It
requires **every ancestor in the enumerated prefix to have period `P`**,
not just the displayed `k`. It keeps `h` antiperiodic over `P` and `g`
periodic over `2P`. No spatial word-length cutoff is imposed within that
fixed-clock graph.

| Ancestor clock P | Canonical plateau rows | Distinct S | Distinct q | S-to-q collisions |
|---|---:|---:|---:|---:|
| 4 | 16 | 4 | 4 | 0 |
| 16 | 128 | 32 | 32 | 0 |
| 32 | 2,048 | 512 | 512 | 0 |
| 64 | 167,168 | 41,792 | 41,792 | 0 |

The cases `P=2,8` have no qualifying rows in this graph; `P=1` has only
the small core case. These are experimental results, not a uniform
injectivity theorem. The ancestor restriction cannot be inferred from
`k`'s period without a separate argument: a general no-period-drop theorem
has not been proved.

The simple proposal `q(t)=S(t) AND S(t-1)` fails already at `P=16` on the
actual parent word `100000000`, with a white head appended. The report
contains its exact profiles and a literal full-cycle audit. Guesses that
all modes avoid `101`, or satisfy the corresponding simple mask-image
condition, also fail. There are 81 independent literal audits, including
each displayed first failure.

The noncore modes were absent from the same-clock prefix-profile graph.
That does **not** prove nonrealizability with higher-clock ancestors and
later period drops. It supplies no license to treat a mode as `Actual`.

## What the learned readers did

Three bounded templates were tested independently of the positive Lean
results:

| Template | Observed outcome |
|---|---|
| Sequential binary DFA, at most four states | All 66,282 transition tables fail on 44 valid profiles at clocks 2,4,8. A separate pure-Python audit replays every conflicting terminal-state pair. |
| Finite algebra combining dyadic halves | Small sizes through six states were rejected by the solver; searches at 8,10,12 states ended inconclusively. No validated candidate. |
| DFA reading aligned halves, with the least OR clock supplied | Small sizes through six states were rejected; larger searches at 8,10,12,16 states ended inconclusively. No validated candidate. |

These solver rejections are not Lean impossibility theorems. Timeouts are
recorded as `unknown`, not as refutations of the larger templates.

To inspect what was learned, representative tables were reconstructed
for recorded training corpora. On clock-32 validation the six-state tree
table makes 794 wrong predictions, and the ten-state paired-stream table
makes 990. Every terminal state of each table contains valid examples
with opposite true targets. The saved tables and literal counterexample
pairs show that relabeling their outputs cannot repair them. The recovered
tables are not claimed to be bit-identical to the earlier solver models.

## Generic cubic transfer, still awaiting complete instantiation

`Rule30CubicAlgebraResearch` proves a uniform algebraic fact for arbitrary
finite sample lists and arbitrary observation times. If all triple driver
moments have XOR zero, then all triple moments of a zero-start XOR
integral have XOR zero. With even sample count, every Boolean polynomial
of degree at most three is annihilated. An odd-XOR target cannot agree
with such a polynomial on all samples.

The proof uses three time inductions and multilinearity. All initial,
recurrence and moment hypotheses are explicit. It has not yet been fully
connected to the preceding 290-orbit certificate: rotation/parity and
cyclic-normalization bridges remain. The direct head-moment audit from
the preceding checkpoint remains computational evidence, not a completed
generic cubic-impossibility Lean theorem.

## Current reference environment and exact validation

The official environment moved from `00900564...` to
[`5473ffd075f63c9d626e63b8455805d4831b39ca`](https://github.com/WolframInstitute/Rule30PrizeKit/tree/5473ffd075f63c9d626e63b8455805d4831b39ca).
Lean 4.35.0 and the Mathlib pin are unchanged. `Check.lean` is unchanged,
SHA-256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
The new references add period-4 single-cell/high-support absorption and
Problem 2 scale equivalences; none supplies the missing observer theorem.

An isolated project contains 267 byte-verified official source files.
Its 24,246 copied cache files, totaling 3,197,503,982 bytes, were separately
verified byte-for-byte, without hardlinks. Changed imports were rebuilt.
All 41 research modules passed build and full replay: 1,068 declarations,
no new axioms. The slowest took 44.16 seconds including build and replay;
the highest owned RSS was 2,799,050,752 bytes. The new official `P2Scales`
module was separately replayed, 117 declarations, as reference validation.
This is not a fresh build of every unrelated catalog module.

An initial misordered bootstrap/build attempt failed while the cache copy
was still running. The completed copy was then independently verified,
and builds were rerun sequentially. The failed guard/log and the successful
completion audit are retained. The previous project was not modified.

New module source hashes:

```
Rule30CubicAlgebraResearch
b1e608df3c1bec943cef704482d54f4885364be6240564354637b169a402b7b7
Rule30ClockSearchResearch
666bbafa2f2e92bf822e26ebd212d16b9a3306cccc9a0656c4aa959c670e30e7
Rule30ClockModeResearch
0d7f9dc8ff048cbb50d45e68e85d63d31f69d512556c87c50459f95b895250e1
```

The guard remains 300 seconds, 8 GiB owned RSS and 2 GiB free memory.
No guard, checker, official statement or authentication setting changed.
The public Z3 dependency was copied into the owned experiment directory;
there was no system installation. Its binaries are not included here.

The 12:01 UTC refresh found 40 submissions and no new completed agent
responses. All 2,635 hashes in 34 preceding owned archives remain
unchanged. [BRIEF.md](BRIEF.md) gives the exact next targets and response
instructions.
