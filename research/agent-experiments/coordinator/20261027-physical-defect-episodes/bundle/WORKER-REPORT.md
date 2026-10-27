# Physical defect-budget interfaces — worker full-checker PASS

This phase formalizes the quantitative interfaces proposed in Cedar's `r30-codex-cedar-prize-bridge-20261027-v01/REPORT.txt`. It proves the doubling-window lower count, a conditional implication to the official `Problem1`, the exact physical mismatch recurrence, and the finite-horizon weighted charging inequality. **The required subcritical upper budget is still open.** These interfaces are not a prize solution or an estimate of the actual defect count from above.

The two frozen core-Lean sources are:

| Source | SHA256 | Full replay | Headline checks |
|---|---|---:|---:|
| `Rule30PhysicalDefectBudgetResearch.lean` | `0ce4c056a39b761d297e4a51468e32d8deb7baf662507c6297cf477e1e2f506f` | 35 constants | 7 |
| `Rule30PhysicalDefectChargeResearch.lean` | `f55ad8100296ce6db1a143fbdb5785c3efc757e4435c1f14e62227820c980149` | 59 constants | 5 |

Both final builds have zero source warnings and no new axioms. These are worker results, not yet an independent root replay or Wolfram/backend verdict. No worktree, public repository, deployment, or submission was changed.

## Exact physical lower bound and conditional Problem 1 statement

All physical cells are the official `Rule30Jen.cell`, the single black seed at position zero. Let `D_Q(t)` mean that column zero is white and the values of column one at `t` and `t-Q` differ. `intervalCount` is literally `List.countP` over `List.range' lo (hi-lo)`, hence uses the half-open interval `[lo,hi)` and is zero when `hi≤lo`. `defectCount Q n0 X` is that count of `D_Q` on `[n0,X)`.

`doubling_lower` assumes `Q>0`, the center's period `Q` from `T`, and `n0≥T+Q`. For every `k`, it proves

    k ≤ defectCount Q n0 (2^k*n0).

Its induction splits at `2^k*n0`, applies the official `Rule30MaskedJen.periodic_window` to `[2^k*n0,2^(k+1)*n0)`, and uses exact additivity of the disjoint half-open counts. The hypotheses imply `n0>0`; there is no zero-start loophole. At `k=0` the interval is empty. `base_four_lower` specializes to

    2*m ≤ defectCount Q n0 (4^m*n0)

for every `m`, including `m=0`.

`periodic_multiple` explicitly converts `P | Q` and an eventual center period `P` to period `Q` with the same onset. `problem1_of_fixed_budget` concludes the official `Rule30Prize.Problem1` only from the following quantified premise:

    for every hypothetical period P>0 from T,
    there exist Q,n0,C,M with Q>0, P|Q, n0≥T+Q,
    such that for every m≥M,
        defectCount Q n0 (4^m*n0) ≤ C+m.

The four parameters are chosen before `∀m`. The contradiction uses `m=M+C+1`. This theorem does not supply the premise. A horizon-dependent Q, n0, C, or onset M would not satisfy its type.

## Exact physical recurrence

The definitions are literal physical column values:

    mismatch Q t = r(t) XOR r(t-Q),
    persists t = NOT z(t),
    forcing Q t = NOT r(t-Q) AND (z(t) XOR z(t-Q)),

where `r(t)=cell t 1` and `z(t)=cell t 2`.

`mismatch_step` proves

    mismatch Q (t+1)
      = (persists t AND mismatch Q t) XOR forcing Q t

from `Q≤t` and agreement of the center at `t` and `t-Q`. It uses the literal `cell` recurrence at column one, not a moving-diagonal model. `periodic_mismatch_step` obtains the center agreement from eventual period Q and `t≥T+Q`, preserving the natural-subtraction domain. `maskedDefect_eq_or_difference` proves that on this domain D_Q is exactly the time-shift defect of the official effective `orCol 0` boundary.

The Boolean OR-difference identity is proved symbolically on its four input bits. This is a uniform local identity, not a spatial/clock enumeration. A common black z reset has both persistence and forcing zero. A unilateral black z only kills persistence and may reinject a mismatch through forcing.

## Finite-horizon CHARGE with exact weights

The second source proves a generic result for arbitrary Bool streams satisfying `x(t+1)=a(t)*x(t) XOR b(t)` from a start s, with arbitrary observation mask. Its definitions use ordinary natural-number counts:

- `survival a s n` is the product of a on `[s,s+n)`, with empty product one.
- `weight a mask s n` is the number of masked readings reached by an initial contribution at s. `weight_expanded` proves its exact finite sum/product expansion.
- `injected a b mask s n` is the accumulated weighted injection charge. `injected_expanded` proves the exact sum over **n−1** possible update times, not n readings.
- `count_as_sum` connects the natural mask/product sum back to the literal half-open `List.countP` count.

`charge` follows by horizon induction from the elementary bound that the indicator of an XOR is at most the sum of its two indicators. It retains multiplicity and does not claim equality after XOR cancellations.

`physical_charge` substitutes the actual physical mismatch, persistence, forcing, and white-center mask. Assuming center period Q from T, `n0≥T+Q`, and `X≥n0`, it proves precisely

    N_Q(X) ≤ delta(n0) * Σ[n0≤t<X] M(t) Π[n0≤s<t] a(s)
             + Σ[n0≤u<X−1] b(u) * Σ[u<t<X] M(t) Π[u<s<t] a(s).

The formal outer injection sum has length `X-n0-1`; thus its last possible index is `X-2`, and it is empty for horizons zero and one. The initial reading at `n0` has an empty survival product and is retained. An injection at u starts affecting time `u+1`, not time u. A reset at s kills a contribution at `s+1`; the reading at s remains included. In particular, the last possible injection at `X-2` has weight exactly the mask at `X-1`.

No bound on these weights is proved or assumed in CHARGE itself. A generic recurrence may allow one contribution to survive many readings. The physical recurrence places additional structure on a and b, but this phase establishes no subcritical estimate from it. The original strategic question—controlling physical reinjection and survival together, with one fixed Q over unbounded horizons—remains unchanged.

## Dependencies, validation, and preserved attempts

The exact dependency graph is `Charge → Budget → official MaskedJen → Prize → Jen`. No Mathlib or private observer/clock machinery is imported. `sources.json` gives the topological order and hashes; `dependencies.json` gives the three official source/object hashes. Their source bytes were checked against both the original compiled pin `5473ffd075f63c9d626e63b8455805d4831b39ca` and the audited compatible official pin `7d665044b904117af9e82328aeb90a30692b2b85`.

Both fresh source builds used Lean 4.35 and a private library containing the exact official dependency objects. Full replay used unchanged `Check.lean`, SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. Its own existing deprecation warning was not suppressed or edited. The checker tests every module-owned constant and all listed headline types, with only standard axioms allowed.

Final core receipt: `formal/attempt02/report.json`, guard `evidence/replay-attempt02.guard.json`: PASS35/7, 2.404 seconds, 778,579,968 bytes peak owned RSS. Final charge receipt: `formal/attempt04/report.json`, guard `evidence/replay-attempt04.guard.json`: PASS59/5, 2.313 seconds, 778,833,920 bytes peak owned RSS. Both retained over 44 GB available system memory and used unchanged 300-second/8-GiB/minimum-2-GiB guards. All jobs are terminal.

Attempt01 failed only because the OR-bridge Boolean cases had not normalized the integer index `0+1` to `1`; adding `Int.zero_add` fixed it without changing a statement. Attempt03 needed one additive-commutativity rewrite in the count/sum bridge and removal of two unused simp arguments. The exact attempted sources, error logs, and guards are preserved. No mathematical claim was weakened to obtain either final proof.

For independent replay, build the two source modules in the order in `sources.json` against the three official dependencies, then run the unchanged checker with the headline names in that file. The recorded `replay.py` shows the complete compile/check/type-print commands and hash assertions. `core-inputs.json` records the first module's inputs; `inputs.json` records the second module and its exact core source/object dependency. Use a new owned phase/attempt and preserve the guards; the delivered phase is sealed.

The original Cedar report and both paper audits were read completely and credited as the source of the mathematical proposal. `CEDAR-INPUTS.json` records their verified manifest hashes. Their suggested upper-budget theorem is not imported as an axiom, hypothesis-free theorem, or informal conclusion.
