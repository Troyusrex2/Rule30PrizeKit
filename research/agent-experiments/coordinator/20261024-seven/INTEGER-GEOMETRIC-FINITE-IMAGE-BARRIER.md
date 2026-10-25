# Every integer geometric scale: a finite-image prefix-rank obstruction

The signed prefix-rank obstruction now holds for **every integer geometric
scale `lambda >= 1`**, retaining an actual finite predecessor, arbitrary
signed integer costs, phase offsets and a uniform additive lower bound.
Four new modules passed local full kernel replay of **126 owned
declarations** with the unchanged official checker.

This strengthens the previous scale-one result. It is a theorem about a
specific proof method. **CQ01, Q01 and Rule 30 Prize Problem 1 remain open.**

## Exact scope

The reader is the same explicit, correctly aligned 784-state prefix reader
for the five phases of the period-five spatial background. State `1` is
absorbing. The energy is

```
E_r(w) = H_r + sum_i lambda^i * C_r(reader state before w[i], w[i]).
```

The theorem `no_integer_geometric_finite_past_prefix_rank` quantifies over
every natural-number `lambda >= 1`, all signed integer cost functions
`C0,C1`, and all integer offsets and lower bounds `H0,H1,B`.

Its lower-bound domain is unchanged: canonical finite words that have an
actual finitely supported predecessor with black head and preceding free
bit `1`, and whose next thirteen double steps have the specified `01`
odd-time stream and black even-time head. The physical rows `A`, `M`, `Z`
are the same 34-, 36- and 38-cell witnesses in the previous release.

The lower-bound condition, `E_0(M) < E_1(A)`, and
`E_1(Z) <= E_0(M)` are incompatible. Both transitions are exact complete
white-wall Rule 30 double steps. No truncated output or predecessor label
is substituted for a physical finite past.

This does not cover noninteger geometric scales, readers recognizing more
backgrounds, costs depending on the full right half, or a lower-bound
domain restricted by a longer actual history. In particular, a reader
that still recognizes the period-seven background is outside the fixed
reader considered here.

## The new argument

A geometric score gives substantial weight to the finite front suffix, so
the scale-one proof cannot simply infer that individual reject-state costs
are nonnegative. The new proof keeps that suffix contribution exactly.

For a fixed suffix of score `Z`, adding `(lambda-1)*Z` to every letter cost
changes a word's score by `(lambda^length-1)*Z`.
`Rule30WeightedSuffixPumpResearch` proves this gauge identity and applies
the earlier absorbing-state pump lemma. A uniform lower bound on
`prefix ++ loop^n ++ suffix` forces

```
score(loop) + (lambda^length(loop)-1)*score(suffix) >= 0.
```

Two families of actual finite images supply these inequalities. The old
all-white family has suffix `10011`. A new all-black family appends one
additional black cell to each finite predecessor and has suffix `111011`.
Its complete output is a fixed 34-cell prefix, `3*n` black cells, and that
six-cell suffix. The physical equation, finite support, black head,
preceding free bit, canonicality and thirteen forward steps are proved for
**every** `n` in `Rule30FiniteImageBlackPumpResearch`.

Write `x=lambda`, `c0=C1(1,false)`, `c1=C1(1,true)`, and

```
B(x) = x^3 - x + 1
A(x) = x^5 - x^3 + x - 1.
```

The two finite-image pump families imply

```
W = B(x)*c0 + A(x)*c1                >= 0
K = (x-1)*c0 + B(x)*c1              >= 0.
```

For the actual two-update witness, the start and end share their first 26
symbols, and their exact geometric score difference is `x^26 * D`, where

```
D  = D0(x)*c0 + D1(x)*c1
D0 = x^9 + x^4 + x^3 - x^5 - 1
D1 = x^11 + x^10 + x^8 + x^5 - x^4 - x^3 + 1.
```

The uniform cone certificate is

```
det * D = alpha * W + beta * K
det     = x^3 * (x^2-x+1)
alpha   = x^7 + x^6 - x^3
beta    = x^13 + x^11 + x^10 - x^9 + x^5.
```

For every integer `x >= 1`, `det` is positive and both multipliers are
nonnegative. The Lean proof establishes this with explicit polynomial
identities and positive factorizations. It does not test a finite list of
scales. Thus `D >= 0`, the end energy cannot be below the start energy,
and the required strict/non-strict rank inequalities contradict one another.

The algebra is in `Rule30GeometricImageConeResearch`; the final module
connects it to the finite-image bounds and exact physical score difference.

## Verification and reproduction

| New module | Owned declarations replayed | Headline checks |
|---|---:|---:|
| `Rule30WeightedSuffixPumpResearch` | 9 | 3 |
| `Rule30FiniteImageBlackPumpResearch` | 62 | 6 |
| `Rule30GeometricImageConeResearch` | 23 | 5 |
| `Rule30FinitePastGeometricRankObstructionResearch` | 32 | 4 |

All four local reports have verdict `pass`, successful full replay, imported
official statements and no new axioms. Standard axioms are listed in the
raw reports. Counts include generated owned declarations and exclude
imports. They are not counts of independent mathematical theorems.

The final module compiled in 83.406 seconds and its full replay took
16.984 seconds. Build logs are warning-free. The reference remains kit
`3eca23c0a9fa6b153313655e6d51835406c2d06e`, Lean 4.35.0, with unchanged
checker SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

The exact sources and complete logs are archived in `geometric-image-prefix`
and identified by `geometric-image-prefix-artifacts.json`. Use the prior
finite-image release's checked dependencies, compile these four modules
in table order, and run the unchanged checker. For example:

```powershell
lake env lean -o .lake/build/lib/lean/Rule30FinitePastGeometricRankObstructionResearch.olean Rule30FinitePastGeometricRankObstructionResearch.lean
lake env lean --run Check.lean Rule30FinitePastGeometricRankObstructionResearch --claim partial --headline Rule30FinitePastGeometricRankObstructionResearch.no_integer_geometric_finite_past_prefix_rank
```

`ring` and `positivity` construct ordinary proof terms. No new axiom,
`sorry`, native decision shortcut, modified checker or skipped replay is
used. This result has been checked locally and published as research; it
has not been submitted as a new Wolfram prize essay.
