# A finite-image barrier for any reader that absorbs on the ether prefix

The integer-geometric obstruction is now **uniform over the reader**. It
applies to any transition function `T : Nat -> Bool -> Nat` that reaches a
permanently absorbing state after the specified 26-cell prefix of the
period-seven witness. No bound on the number of reader states is used.

`Rule30GenericAbsorbingPrefixBarrierResearch` passed local full kernel
replay of **21 owned declarations**, including six headline checks, with
the unchanged official checker. The explicit 784-state period-five reader
is recovered as a checked instance. **CQ01, Q01 and Rule 30 Prize Problem 1
remain open.**

## The uniform statement

Let `p` be any initial reader state and `s` an absorbing state:

```
T(s,false) = s
T(s,true)  = s
run(T,p,commonWord) = s.
```

`commonWord` is the same fixed 26-cell common prefix of the actual start
and end rows in the previous result. The theorem quantifies over all `T`,
`p` and `s` satisfying these conditions, every integer geometric scale
`lambda >= 1`, all signed integer cost functions `C0,C1`, and all integer
phase offsets and additive lower bounds.

The energy reads the whole finite word from initial state `p`:

```
E_r(w) = H_r + sum_i lambda^i * C_r(reader state before w[i], w[i]).
```

`no_absorbing_prefix_geometric_rank` shows that these three requirements
cannot all hold:

1. `E_1` has a uniform additive lower bound on every canonical finite word
   with the stated thirteen forward steps and an actual finite predecessor
   whose head is black and whose preceding free bit is one.
2. `E_0(M) < E_1(A)` on the specified actual physical double step.
3. `E_1(Z) <= E_0(M)` on the next actual physical double step.

The physical rows, the finite-image domain and the geometric weighting
are unchanged from the [integer-scale result](INTEGER-GEOMETRIC-FINITE-IMAGE-BARRIER.md).
The generalization removes its fixed transition table from the theorem's
reader assumptions.

## Why the generalization is valid

Both infinite families of finite-image witnesses share `commonWord` at
the beginning of their fixed prefixes. Once any reader reaches an
absorbing state there, their arbitrarily long constant blocks and their
complete finite front suffixes are scored using only `C1(s,false)` and
`C1(s,true)`. `run_front` proves that fact for both families.

The exact geometric pump inequalities and the uniform polynomial cone
certificate therefore apply with `s` in place of the original reject state
`1`. The start and end also share `commonWord`, so their exact score
difference has the same two-cost polynomial. Nonnegativity of that
difference contradicts the two rank inequalities.

The proof retains actual finite predecessors, all moving-front cells,
signed costs, phase offsets and the additive lower bound. It uses no
assumption that individual letter costs are nonnegative.

The last theorem, `specified_reader_instance`, instantiates the generic
statement with the earlier transition table and its kernel-checked
absorption facts. This also checks that the generalized statement recovers
the earlier result with the same lower-bound domain.

## What remains available to a proof search

A reader that continues tracking the period-seven background after this
prefix does not satisfy the absorption condition. Readers that can
resynchronize after a mismatch also require separate analysis. Costs using
the full right half, noninteger geometric scales, longer actual history
restrictions and other lower-bound domains remain outside the statement.

The theorem provides a specific reason to stop fitting ranks in the
excluded class. It is not a solution of a prize question or a universal
barrier for all finite-state methods.

## Verification and reproduction

The source and complete raw evidence are in `generic-absorbing-prefix`;
`generic-absorbing-prefix-artifacts.json` records their exact hashes.
The local checker reported `pass`, replayed all 21 owned declarations,
found all six headlines, imported the official statements and found no new
axioms. Standard axioms are listed per declaration in the raw report.
Counts include generated owned declarations and exclude imports.

The module compiled in 56.453 seconds and full replay took 18.0 seconds.
The build log is warning-free. Use the preceding releases' checked
dependencies and the same pinned project:
`3eca23c0a9fa6b153313655e6d51835406c2d06e`, Lean 4.35.0. The unchanged
checker SHA-256 is
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

```powershell
lake env lean -o .lake/build/lib/lean/Rule30GenericAbsorbingPrefixBarrierResearch.olean Rule30GenericAbsorbingPrefixBarrierResearch.lean
lake env lean --run Check.lean Rule30GenericAbsorbingPrefixBarrierResearch --claim partial --headline Rule30GenericAbsorbingPrefixBarrierResearch.no_absorbing_prefix_geometric_rank --headline Rule30GenericAbsorbingPrefixBarrierResearch.specified_reader_instance
```

No new axiom, `sorry`, native decision shortcut, modified checker or skipped
replay is used. This is a public research result checked locally. It has
not been submitted as a new Wolfram prize essay.
