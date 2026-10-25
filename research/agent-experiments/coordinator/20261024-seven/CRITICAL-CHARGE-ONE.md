# A finite right seed rules out constant-one critical charging

The critical charging target was

```
5 * zeros(free R,n) <= n + B + C * blackCount(Psi R,2*n+1).
```

There is an explicit finite mathematical right half `R` for which **no
additive allowance `B` makes this true with `C=1`**. The two new modules
passed full kernel replay of 104 owned declarations. This refutes a
coefficient choice in our proposed bound; Problem 1 and CQ01 remain open.

The witness starts in the kit's known ether-and-wall trap. It is
`Rule30Ether.config 3 1 6 wall`, with the 13-cell wall spelled out in
[`Rule30CriticalChargeOneCoreResearch.lean`](Rule30CriticalChargeOneCoreResearch.lean).
The finite bit encoding is `0x6b70`, with position 1 at bit zero. The
proof uses the explicit configuration and the official trap invariant,
rather than assuming an observed finite trace continues forever.

For this right half, the actual coupled free stream is `010101...`. Its
official sideways row `Psi R`, at positive spatial depths, is
`1100001` repeated. Depth zero is the white wall. The proof establishes
these facts for every time and depth using the kit's `drv`, `zrow`,
`Theta`, `Psi`, and ether invariant.

Consequently, at **every** scale `n=14*k`,

```
zeros(free R,n)             = 7*k
blackCount(Psi R,2*n+1)     = 12*k.
```

With `C=1`, the proposed inequality becomes `35*k <= 26*k+B`.
Taking `k=B+1` contradicts it. This rules out all additive allowances,
not merely the allowance zero or one large finite test. Any natural-number
coefficient satisfying this bound for the witness must be at least 2.
The result does not establish that 2 suffices for arbitrary right halves.

The count convention is unchanged: `blackCount L K` counts depths
`0..K-1`. Thus `blackCount (Psi R) (2*n+1)` includes exactly the positive
depths `1..2*n`, since the wall contributes zero.

The [standalone core](Rule30CriticalChargeOneCoreResearch.lean) imports
only two official kit modules. Its main theorems are `right_finite`,
`free_stream`, `psi_left`, `coupled_scale_counts`,
`unit_critical_charge_false`, and `minimum_integer_coefficient`.
The [bridge](Rule30CriticalChargeOneBridgeResearch.lean) proves equality
with the previously released counting definitions by induction and
transfers the result to `Rule30GoldenCriticalDriftResearch.CriticalCharge`.
It changes no free stream, coordinate, index, coefficient, or quantifier.

Both checks used Lean 4.35.0, kit commit
`3eca23c0a9fa6b153313655e6d51835406c2d06e`, and the unchanged official
checker. The [core report](critical-charge-one-core-evidence/report.json)
records 94 declarations; the
[bridge report](critical-charge-one-bridge-evidence/report.json) records
10. Both full replays passed with no new axioms and accepted headline
theorems. Sources, logs, and hashes are listed in
[`critical-charge-one-artifacts.json`](critical-charge-one-artifacts.json).

To replay the standalone result, copy the core source into a clean project
at that pin, compile it with `lake env lean -o
.lake/build/lib/lean/Rule30CriticalChargeOneCoreResearch.olean
Rule30CriticalChargeOneCoreResearch.lean`, and run the unchanged checker
with module `Rule30CriticalChargeOneCoreResearch`, `--claim partial`, and
the fully qualified headline `Rule30CriticalChargeOneCoreResearch.unit_critical_charge_false`.
The bridge additionally imports the earlier released research definitions.

The witness has infinitely many sideways black cells, so it is consistent
with CQ01. It leaves the variable-coefficient critical charge, the weaker
scale-charge target, and `No00SpatialCharge` unrefuted. Its practical use
is to remove the constant-one critical target from further searches while
preserving those broader routes. No new prize essay was submitted.
