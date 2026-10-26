# The supplied fixed-prefix cycle and its precise boundary limitation

Root subsequently requested one exact four-cycle audit, without search.
The literal updates and wrap passed. With oldest bit least significant:

| Phase | A | B | H | D | Subset |
|---|---:|---:|---:|---:|---|
| 0 | 1 | 2 | 8 | 3 | false |
| 1 | 7 | 14 | 8 | 9 | true |
| 2 | 9 | 2 | 8 | 11 | true |
| 3 | 15 | 14 | 8 | 1 | false |

Every row satisfies Common on all three internal adjacent pairs. The
fourth update returns to phase0, so deterministic iteration proves Common
at those pairs for every time. A has four distinct values; the joint least
period is exactly4. Shifting the starting phase to1 gives initial Subset,
Subset after one update, and loss at j=3 after two updates.

This refutes even the fixed-prefix version with all-time internal Common,
genuine missing older white cells, and finite-prefix recurrence. It blocks
the proposed recurrence argument through the stated prefix lemma.

It is not a whole-half-line all-time Common example. Zero-padding the
original phase0 input A=1,B=2,H=8 beyond j=3 gives, after one true half-line
update, A'=7,B'=14,H'=56. The extra H bits are at4 and5. Output Subset
fails there, and Common fails at the adjacent pair(3,4). All outputs above
index5 are zero by radius2, and the audit includes the last possible
nonzero-to-zero adjacency. The finite4 truncation discards precisely the
newer coordinates needed by the global condition.

No conclusion about global Actual/Common/Mode initial-Subset preservation
or the safety conjecture follows. No BFS, SAT, or horizon sweep was run.
Reproduce the requested cycle and mismatch with `python -B audit_cycle.py`.
