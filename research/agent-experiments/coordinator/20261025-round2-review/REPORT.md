# All seven round-two responses: review, falsification and new checked results

Troy Lowry and Codex, 25 October 2026. **Problem 1, Q01 and CQ01 remain open.**
All seven responses arrived and their listed artifact hashes matched. Every
response received a mathematical review and independent computations or proof
checks. Several manifests have schema notes, recorded without changing or
discarding the original work. The reviewed originals are in `work/snapshots`.

The strongest new result is an **all-time coefficient-two counterexample** to
our proposed critical-charge inequality. The wiki agent supplied the finite
seed and empirical pattern; the coordinator found its finite entry to an
official invariant trap and completed the missing proof. See
[COEFFICIENT-TWO.md](COEFFICIENT-TWO.md). Coefficient three remains open on
actual finite right halves. This refutes a proposed bound, not a prize question.

Two other responses produced checked proof interfaces: exact least-source
ancestry recurrences and a conditional bridge to the official Problem 1, and
cross-column defect transfer with a quantitative interval witness under a
hypothetically periodic center. Their decisive escape/capacity premises remain
unproved. Numerical rank growth is another open lead, not a theorem.

## Findings and dispositions

Each original finding keeps its own submitted status. These are the
coordinator's separate dispositions; one checked result does not verify a
whole response. Full response IDs and finding references are in
[DISPOSITIONS.md](DISPOSITIONS.md) and `intake.json`.

| Session | Independent work completed | Disposition and remaining gap |
|---|---|---|
| codex-sanity, R2-03 | Reproduced exact nonlinear source identities, all 32,780 trace bits and minor checks, the bounded-descent witnesses and failed rank-growth shortcuts. | The pigeonhole obstruction is valid as a written argument. Unbounded source-minor rank would imply all of Problem 1, but no rank-growth lemma is supplied. Finite ranks remain experiments. |
| codex-cedar, R2-04 | Fresh isolated rebuild and unchanged checker replay of all 44 declarations; reproduced 4,096 frontier cases and 32 held-out cases, including retreats. | Conditional ancestry and the nonlinear Rule-210 countercontrol are verified. The least source reaching the center remains open. The new coordinator module formalizes its exact recurrence, persistent left-edge descendant, crossing lemma and conditional official bridge. |
| photograde, R2-02 | Reproduced F001/F002 classifications and all 126-by-600 reconstruction checks. | No seed-specific learned signal emerged. The two-column periodicity obstruction is already the stronger official Jen theorem; inheritance is still missing. |
| backend, R2-01 | Reproduced the barrier escape examples; all 27 Rule-30 modular-rank cases through window nine and all 15 Rule-184 controls through five; pump, Farkas and Fibonacci-reader computations. | Useful exact finite ingredients. The unbounded physical reductions are paper arguments with formalization gaps. Reported windows ten/eleven were not independently rerun. These do not prove an obstruction to the richer history/upcoming-phase model. |
| swarm run 123207Z, R2-06 | Reproduced the reported measurements and extended samples to time 131,072. Checked a full autonomous 87,868-cell prefix cycle of period 32. | The proposed positive asymptotic fraction at lag 16 fails: the agreement depth eventually stays 87,867. The finite cycle and semantic derivation are not Lean-checked. The multiset proposal has no block ordinal, and merges are not automatically decreasing. |
| wiki, R2-07 | Reproduced both actual finite-right coefficient-two candidates at n=20,000. Proved W1 for every scale and allowance in Lean. Tested 96-bit transients and an exact temporal-state cycle. | W1 is now a theorem. W2 remains a finite observation/entry candidate. The proposed broader density floor 2/7 fails for an explicitly specified eventually alternating Golden stream with exact cycle density 6/28; its achievability by a finite right half is unknown. |
| swarm run 124556Z, R2-05 | Reproduced defect identities, rule-family scan, corrected frame comparison and rate calibrations. Formalized the zero gate and interval witness. | The mask identities and conditional interval theorem are verified. A positive-density/capacity result is still open. The original moving-frame claim is retracted. The seven-minute 65,532-orbit sweep was source-reviewed, not independently rerun. |

## New formal results and evidence

All checks used Lean 4.35.0 and the reference kit at
`3eca23c0a9fa6b153313655e6d51835406c2d06e`. `Check.lean` is unchanged, SHA-256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
Each listed module passed full local kernel replay of all its owned
declarations, headline checks, official-statement imports and no-new-axiom
checks. Counts include generated declarations and are not counts of independent
mathematical discoveries. Sources are in `work/`; raw reports and logs are in
`work/evidence/`. Cedar's independent replay is in `work/evidence/cedar`.

| Module | Replayed declarations | Scope |
|---|---:|---|
| `CedarAncestry` (incoming) | 44 | Local normalization, conditional ordered ancestry, canonical seed bridge, Rule-210 countercontrol. |
| `Rule30RoundTwoAncestryFrontResearch` | 27 | Exact least-root masked-neighbor recurrence; persistent outward left edge; crossing; Problem 1 from the explicit unproved escape premise. |
| `Rule30RoundTwoDrivenPrefixResearch` | 10 | Sound finite light-cone trace certificates for official `drv`. |
| `Rule30RoundTwoChargeTwoEntryResearch` | 41 | Actual finite W1; kernel-checked 59-step trace; entry and invariant; exact entire free stream. |
| `Rule30RoundTwoChargeTwoThetaResearch` | 68 | Exact all-depth/time reconstruction by a small table; official `Psi` equality. |
| `Rule30RoundTwoChargeTwoResearch` | 33 | All-scale exact counts; failure of coefficient two for every allowance; natural coefficient at least three. |
| `Rule30RoundTwoChargeTwoBridgeResearch` | 5 | Transfer to the unchanged earlier Golden critical-charge target. |
| `Rule30RoundTwoDefectTransferResearch` | 26 | Local defect transfer, zero gate, triangular propagation and white-terminal interval. |

The coordinator's seven new modules total **210 replayed declarations**, plus
the 44 independently replayed incoming declarations. No axiom, `sorry`, native
decision shortcut, changed official target or skipped replay was used. The
unchanged checker emits its existing deprecation warning; our final module
build logs have no warnings. The final per-module guards completed normally.

The ancestry headline `problem1_of_least_root_escape` is a **conditional**
theorem. `LeastRootEscape` is unproved. It does not inhabit Problem1 without
that hypothesis, and the checker was deliberately invoked with `--claim partial`.

## Corrections exposed by the new tests

The lag-16 depth measurement looked linear up to time 8,000. An autonomous
left-edge prefix, with update

```
q_next = ((q << 2) XOR ((q << 1) OR q)) mod 2^87868,
```

reaches a closed period-32 cycle by time 131,072. Each of its 32 phases differs
from its lag-16 partner only at bit 87,867. Prefix autonomy and this full-state
cycle imply exactly that agreement depth for every later lag-16 comparison
(t >= 131,088), so its proportion of row width tends to zero. A coordinate
truth-table check and 97 independent physical rows passed. This is an exact
finite certificate with a written semantic bridge, **not a Lean theorem**.
It does not identify the moving seed-edge prefix with the distinct white-wall
prefix in the earlier reader barrier.

For the wiki's proposed floor, the explicit prefix in `wiki-exact-cycle.json`
is followed by an alternating tail forever by definition. The full pair of
temporal functions is represented exactly by 196 bits per column: a 192-time
prefix and period-four tail. Its spatial reconstruction state repeats after
1,079 states, entering a 28-cycle at depth 1,052 with **six** black outputs.
That gives density 3/14, below 2/7. This cycle includes the full represented
functions, not just a repeated finite output prefix. Its semantics are checked
independently on 32 scalar columns and justified on paper; no Lean replay or
finite-right achievability is claimed. Consequently it does not refute C=3
on actual finite right halves.

Two logical gaps also matter. Maximum limiting zero density 1/2 does not force
eventual alternation: insert one extra `1` in block `01` at powers-of-two block
indices. The Golden stream still has limiting zero density 1/2 and infinitely
many `11` slips. Bounds only for eventually alternating streams therefore do
not cover every Golden or every finite-right driver. Also, in a multiset order,
a merge creates a new block: it is not merely deletion. A relation between the
new block and removed blocks must be proved.

In the R2-05 paper count, intervals for m_k=2^k*C touch at endpoints and are
not disjoint as written. Choosing m_(k+1)=2*m_k+1 repairs the disjoint-interval
argument while keeping logarithmic order. The formal theorem here states the
underlying interval witness directly, with no informal logarithm convention.

## What to investigate next

The source-minor odd-residual construction, least-source escape, and a
Rule-30-specific capacity/progress argument are still open. None follows from
finite rank tables, surviving-path existence, ordered ancestry, or a larger
learning model. Rule 210 remains a mandatory countercontrol for ancestry-only
arguments. For charge bounds, C=2 is now excluded, and a universal Golden
density floor cannot replace actual coupling. Variable coefficients and
ScaleCharges remain open.

Full sources, exact received manifests, review metadata and byte hashes are
preserved in [artifacts.json](artifacts.json). See
[REPRODUCE.md](REPRODUCE.md) before running anything. The original inbox and
other sessions' work were not edited. This archive is public research checked
locally; no new Wolfram prize essay or pull request was submitted.
