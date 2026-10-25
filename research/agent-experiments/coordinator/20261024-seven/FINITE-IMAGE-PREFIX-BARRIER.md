# A signed prefix-rank obstruction on actual finite images

The earlier prefix-reader obstruction used a starting row with no finite
predecessor. The new theorem removes that limitation for **scale one**:
the same period-five-only prefix reader cannot provide the specified
bounded-below signed rank even on the refined domain with an actual finite
predecessor. Three new modules passed full kernel replay of **200 owned
declarations**. This is an obstruction to a proof method; **CQ01, Q01 and
Rule 30 Prize Problem 1 remain open**.

The source and raw evidence are in `finite-image-prefix`. The 26 completed
search records released with it cover stronger past restrictions, upcoming
bit phases and a different inverse-column flux model. None produced a
positive certificate. Numerical errors and time limits remain unknown.

## The exact theorem

The reader is the explicitly specified, correctly aligned 784-state binary
prefix reader in the previous release. It recognizes prefixes of the five
temporal phases of the period-five spatial background, and has an absorbing
reject state `1`. Its first input is the first left cell.

For arbitrary integer letter costs and phase offsets, consider

```
E_r(w) = H_r + sum_i C_r(reader state before w[i], w[i]).
```

There are two phases, indexed `0` and `1`, and the weights have geometric
scale one. Costs may have either sign.

`HasPastOne w` means that there is an actual finitely supported predecessor
`P` with black head, preceding free bit `1`, and `row w = zrow P 2`.
`Safe13 w 0` means the head is black at even times through time 26 and its
first thirteen odd-time bits are `010101...`. The shifted condition
`Safe13 w 1` uses `101010...`.

`no_unit_scale_finite_past_prefix_rank` proves that the following three
requirements cannot all hold:

1. `E_1` has one uniform additive lower bound on every canonical word with
   `HasPastOne` and `Safe13 ... 0`.
2. `E_0(M) < E_1(A)` on the specified first physical double step.
3. `E_1(Z) <= E_0(M)` on the specified second physical double step.

Here `G` is the official white-wall two-step evolution. If `w0` is the
earlier 30-cell ether prefix, then `A=G(G(w0))`, `M=G(A)`, `Z=G(M)`.
Their lengths are 34, 36 and 38. The kernel checks both complete updates,
canonicality, `Safe13 A 0`, `Safe13 M 1`, and finite predecessors with the
correct preceding free bits. The earlier nonimage row `w0` is not the
starting state of this new obstruction.

The first step has free bit zero after one preceding one, so it is a
positive-defect step in the proposed Golden rank. The second has free bit
one. The theorem even allows the second inequality to be non-strict.

## Why signed costs cannot rescue this instance

The important new argument derives nonnegative reject-state costs from
the lower-bound premise. It does not assume them.

`Rule30FiniteImagePumpResearch` constructs two infinite families of finite
predecessors, with an actual image for every natural number `n`. One family
produces an arbitrarily long all-white output block; the other produces an
arbitrarily long all-black output block. Their exact full output words are

```
U_false ++ false^n     ++ V_false
U_true  ++ true^(3*n)  ++ V_true.
```

The prefixes have length 34 and suffixes have length 5. Both families are
canonical, satisfy the same thirteen forward steps and have the required
finite past. Both fixed prefixes have already reached reject state `1`.

The all-black construction uses the exact fact that a periodic input block
`110` becomes `111` after two updates. The all-white construction uses a
zero block. Uniform local evolution and tail-translation identities prove
the complete word equations, including every newly created front cell.
This is not a bounded enumeration over `n` or a truncation of the output.

Their scores have the form `constant + n*C_1(1,false)` and
`constant + 3*n*C_1(1,true)`. A negative reject-state cost would violate
the uniform lower bound. `sink_cost_nonnegative` therefore proves both
costs are nonnegative, although every other cost may still be signed.

Finally, the actual rows `A` and `Z` share the first six symbols, after
which the reader is absorbing. Beyond that prefix, `Z` contains exactly
one more white cell and three more black cells. The exact score identity is

```
score_1(Z) = score_1(A) + C_1(1,false) + 3*C_1(1,true).
```

Thus `E_1(Z) >= E_1(A)`, contradicting the two required rank inequalities.
The complete argument, including the quantified finite-image families and
the signed-cost consequence, was replayed locally through Lean's kernel
with the unchanged official checker.

## Scope and remaining openings

This theorem concerns integer costs, geometric scale **one**, this fixed
single-background prefix reader, and the exact domain in its statement.
It does not rule out a reader recognizing several backgrounds, geometric
scale greater than one, costs using the full right half, or ranks restricted
by a longer actual past. It also does not prove that a displayed numerical
zero optimum is an impossibility theorem for an entire method.

In particular, the known coefficient-one critical-charge counterexample
and the present scale-one reader obstruction are different statements.
Neither refutes the remaining variable-coefficient charging target.

## Checked modules and reproduction

| New module | Owned declarations replayed | Headline checks |
|---|---:|---:|
| `Rule30FiniteWordAppendResearch` | 18 | 3 |
| `Rule30FiniteImagePumpResearch` | 123 | 7 |
| `Rule30FinitePastPrefixRankObstructionResearch` | 59 | 8 |

All three local reports have verdict `pass`, successful full replay, imported
official statements, and no new axioms. Per-declaration standard axioms
are in the raw check logs. Counts include generated owned declarations.
They exclude imported declarations and are not counts of independent
mathematical theorems.

Use the previous release's dependencies and pinned reference project at
`3eca23c0a9fa6b153313655e6d51835406c2d06e`, Lean 4.35.0. Compile the new
files in table order. The unchanged checker has SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
For example, after compiling the dependencies:

```powershell
lake env lean -o .lake/build/lib/lean/Rule30FinitePastPrefixRankObstructionResearch.olean Rule30FinitePastPrefixRankObstructionResearch.lean
lake env lean --run Check.lean Rule30FinitePastPrefixRankObstructionResearch --claim partial --headline Rule30FinitePastPrefixRankObstructionResearch.no_unit_scale_finite_past_prefix_rank
```

The manifest records the exact sources, complete build/check logs and
reports. No checker change, new axiom, `sorry`, native decision shortcut or
skipped declaration replay was used.

## Experiments beyond the theorem's domain

The accompanying sources and results are mathematical experiments, with
independent physical and exact arithmetic controls. They are not claimed
as Lean proofs.

| Family | Cases | Actual solver outcomes |
|---|---:|---|
| Actual finite history, depths 2 through 4 | 6 | Five zero optima; one solver error |
| Energy phases selected by upcoming free bits | 6 | Four zero optima; two solver errors |
| Universal column flux, fixed charging coefficient | 8 | Two infeasible instances; six time limits |
| Universal column flux, optimized positive charging rate | 6 | Five zero optima; one time limit |

The first two families retain complete moving fronts and allow signed
geometric costs with a uniform additive lower bound. Their independent
controls include 49,152 exhaustive history-language checks, 1,398 exact
history-energy identities, 55,296 upcoming-phase language checks and 156
exact phase-energy identities. The history archive uses the corrected v2
harness, with fixed case-ID log names and all six case outcomes retained.

The column-flux model is a different candidate route. It asks for
`Phi(column) <= M*Phi(next inverse column) + F*firstBlack`, while a separate
boundary-language graph lower-bounds a zero count or zero-run count by
`Phi`. Finite graph potentials encode every column length, rather than
only training lengths. With `M>1`, telescoping would give a position-
weighted spatial bound, still finite on any finitely supported row.
The optimized variant permits any positive charging rate at fixed `M`.

Two- and three-column encodings, optional temporal clocks, and the no00,
Golden and conditional coupled forbidden-word languages were tested.
The unrestricted domain pays starts of zero runs. It is distinguished
from the known false unrestricted unit-coefficient bound. The conditional
coupled language uses the previously independently replayed external
finite-Psi reduction; no new external proof is being assumed from a label.

Column controls passed 14,344 antidiagonal/full-column cell comparisons,
5,022 exhaustive column-language checks, 4,088 boundary-language checks
and 4,280 exact energy identities, plus nontrivial positive and zero-payment
negative calibrations. Any positive numerical candidate would have been
checked against every original rational inequality. None was found.

All 26 process guards completed normally on G913. Peak process-tree RSS
was below 0.85 GiB and minimum system free memory exceeded 42 GiB. Native
solver time limits are distinct from process guards: the seven time-limit
cases and three solver errors remain unknown. Numerical infeasibility and
zero optima have their stated finite model scope, and are not kernel
theorems or disproofs of the charging conjectures.

The released experiment packages require NumPy and SciPy. Run their control
scripts first and use the case drivers to reproduce individual settings in
a separate output directory. The G913 wrappers additionally use the
existing process-tree resource guard. Source manifests, complete numerical
metadata and every authoritative case result are preserved.

This is a public research record, not a new prize submission.
