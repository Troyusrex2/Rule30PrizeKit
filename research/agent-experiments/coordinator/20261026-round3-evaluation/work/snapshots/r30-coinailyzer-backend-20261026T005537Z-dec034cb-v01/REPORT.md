# Agent response

Response ID: r30-coinailyzer-backend-20261026T005537Z-dec034cb-v01
Agent: CoinAIlyzer Backend Bot (claude-opus-5-5, Claude Code)
Supersedes: none

## Batch overview

One off-the-wall idea, borrowed from die-state research on coins. A die crack, once started, always spreads into the field; no die strikes forever without its flaws showing. Here the "die" is a finite row and the "flaw" is its edge. The bet is that a finite row cannot hide its edge from the center column forever, so any periodic stretch in its trace must break, within a bound that depends only on the row's width.

## F001 — Die-crack lemma

- **Track and status:** A, EXPERIMENT (bounded measurement, not proved).
- **Exact question:** is there an explicit f such that every periodic stretch (period p) in the center trace of any nonzero finite row of width W has length at most f(W), or f(W, p)?
- **Why it suffices:** if the seed column were periodic from time T on, the row Phi^T(1), of width 2T+1, would have an infinite periodic stretch. Any finite f rules that out.
- **Conventions:** the handoff's moving frame, Phi(a) = a XOR ((a<<1)|(a<<2)), observation Phi^u(a)[u]. The seed trace reproduces 1101110011000101100100... as a check.
- **Result:**
  - No row of length up to 14 has a trace that is periodic (p up to 16) from t=48 to t=160.
  - The longest periodic stretch R(L), over all rows of length L, for L = 2..15: 12, 12, 10, 13, 14, 14, 14, 15, 18, 18, 24, 18, 23, 23. That is roughly L+8, slightly below a random-sequence baseline.
  - So far the data fit a finite f that grows slowly.
- **Evidence:** `src/runs.py`, `src/probe.py`, `evidence/runs.json`, `evidence/periodic-census-L14.json`; hashes are in `logs/sha256.txt`.
- **Limitations:**
  - Small bounds, and counting alone could produce the same curve.
  - The general lemma may be harder than Problem 1, which only needs seed rows.
  - Only c=0 was run, and traces were capped at 8L+64.
- **Next action:**
  1. Extend to L up to 24 with traces to 64L, written in C.
  2. Study how each record-holding stretch breaks. The candidate mechanism is the row's left-edge information crossing the column after about W steps, under the left-permutive update.
  3. Try p=1 in Lean first.
