# One-step backward Subset candidate fails at width four

The exact finite-word implication is false. Root supplied the candidate;
the structural worker independently checked its literal update against the
frozen CommonPast definitions. No BFS or additional horizon was run.

Bits below are older first; the integers use the oldest bit as the least
significant bit. Missing older inputs in all three rows are white.

| Quantity | Input | Output after one update |
|---|---|---|
| A | 1000 (1) | 1110 (7) |
| B | 0100 (2) | 0111 (14) |
| H | 0001 (8) | 0001 (8) |
| D = A xor B | 1100 (3) | 1001 (9) |

Common holds at all three adjacent pairs of both rows. Input Subset fails
exactly at the newest coordinate j=3. Output Subset holds at every position.
The input boundary formulas are the actual white formulas, and there is
no spatial wrap at the newest edge.

Thus Common at the two rows plus output Subset does not imply input
Subset for every finite white-ended prefix. The proposed one-step lemma
cannot be combined with recurrence in the suggested way.

The subsequent requested four-cycle audit, recorded in `CYCLE_SCOPE.md`
and `cycle-audit.json`, strengthens this to all-time Common on the three
internal pairs of the fixed width4 prefix. Starting at phase1 then gives
initial Subset and loss after two steps. It also records the exact failure
of the zero-padded half-line extension. Neither audit supplies whole-half-line
all-time Common or a counterexample to the global initial-Subset question.
Neither addresses the finite-white safety-completeness conjecture.

Reproduce with `python -B audit_candidate.py`. The data file records the
frozen source hash and all local predicate checks. The two implementations
of Actual and the two implementations of Mode agree on this exact input.
