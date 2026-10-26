# A ten-letter actual-image obstruction

**P1, Q01, CQ01 and the all-time center observer remain open.** This follow-up
combines the round-three realizability question with our earlier delayed-defect
family. It proves a uniform image exclusion, not the center's nonperiodicity.
No new prize essay or API submission was made.

## Exact result

For every right half R, including infinite ones, and every onset s, the actual
coupled free bits `!u R (s+i)` cannot spell

    1010111010

The official `Psi_free` identity identifies these bits with the odd-time free
column of `Psi R`. The theorem uses the official driven-right recurrence and
alternating boundary. It does not assume finite support or a canonical seed.

Consequently, start with the alternating free stream `s mod 2` and change only
its white bit at an even index L to black. **For every even L>=6, this stream
cannot be an actual coupled free response.** It contains the forbidden word
beginning at L-5. The proof covers all indices and onsets, not just a census.

In particular, the delayed family at L=4*j+2 used in
[our earlier period-growth result](../20261025-delayed-periods/REPORT.md) is
outside the actual image whenever j>=1. The positive synthetic period theorem
remains valid; it was explicitly about synthetic starts. The earlier theorem
that those streams avoid 00, 11111, 010110 and 1011010 remains valid too. The
new ten-letter word itself contains none of those four forbidden factors.

The module states the three main results as `no_free_1010111010`,
`no_actual_isolated_flip`, and `delayed_family_not_actual`.

## Evidence and proof method

An exact finite-cone solver first rejected delayed flips at L=6,10,18. Its SAT
controls used three physically evolved finite right halves; every returned
witness was independently replayed as a literal Rule30 cell set. L=2 remained
SAT through 48 free bits. Those witnesses do not prove infinite realizability.

Testing factors isolated the ten-letter word. We then discarded reliance on
the solver: a separate procedure enumerated only the sixteen local Boolean
assignments to `next = left XOR (center OR right)`. Propagation and four case
splits give a nine-node contradiction tree. The tree works with an arbitrary
right row at an odd starting time, which is a stronger relaxation than requiring
a preceding physical row.

[The 770-line Lean source](work/Rule30IsolatedDefectResearch.lean) directly
checks those local implications and both branches of every split. Its generic
`no_profile` theorem derives a contradiction from the recurrence, the
alternating boundary and the ten prescribed free bits. A separate proof
connects that profile to the official `drv` and `u` at any onset. Arithmetic
then supplies the isolated-flip and delayed-family corollaries. No SMT result,
external proof certificate checker or skipped kernel computation is trusted.

An independent Python audit checks every local deduction and branch, and
rejects two deliberate corruptions: a wrong forced value and a missing Boolean
branch. These controls supplement the Lean proof; the Python calculations
themselves are not Lean verified. The producer, tree, generator, audits and
finite solver results are included for reproducibility. This is not a claim
of historical priority for this forbidden word.

## Validation

At kit `0090056412733accaa27643d3cbbf982104f2251`, Lean 4.35.0,
the unchanged official checker fully replayed **all 52 module declarations**,
including generated declarations, and accepted all three headlines with no
new axioms. Local facts inside the proof are not counted as separate theorems.
Source SHA-256:
`bb98722222ef8576c7c76994f7713da45bf5dfe99623fe6d294aa55ad090eff9`.
Checker SHA-256:
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

Build plus full replay on the Windows offload machine took 2.294 seconds,
peaked at 786,874,368 bytes of owned RSS, and left at least 46,420,856,832 bytes
free. The existing 300-second / 8-GiB owned-tree / 2-GiB minimum-free guard
was unchanged. A first source attempt failed on Boolean-negation parentheses
and simplification; those errors were repaired before the reported pass.
No resource limit was relaxed.

Run `python verify_artifacts.py` for archive hashes and evidence scope.
To reproduce the formal result, check out the pinned kit, build dependencies,
copy work/Rule30IsolatedDefectResearch.lean into lean/, and run there:

```text
lake env lean -o .lake/build/lib/lean/Rule30IsolatedDefectResearch.olean Rule30IsolatedDefectResearch.lean
lake env lean --run Check.lean Rule30IsolatedDefectResearch --claim partial --headline Rule30IsolatedDefectResearch.no_free_1010111010 --headline Rule30IsolatedDefectResearch.no_actual_isolated_flip --headline Rule30IsolatedDefectResearch.delayed_family_not_actual
```

The included generation and independent-audit scripts use Python's standard
library. The exploratory finite-cone script additionally uses Z3 5.3.1;
its dependency path is specific to the original research workspace. Z3 is not
needed to compile or check the Lean theorem.

## Remaining gap

This eliminates another tempting synthetic family. It does not characterize
all achievable streams, establish a charging inequality on them, or connect
all-width escape to the canonical moving center observer. The next useful
step is a structural invariant retaining image constraints and finite ancestry,
or a counterexample that survives those constraints. A longer list of forbidden
words, without such a mechanism, would still not resolve the prize problem.
