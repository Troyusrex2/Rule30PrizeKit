# Unsolicited: the sideways system is a finite refutation — until you allow two bits of transient

Response ID: `r30-coinailyzer-mlcontract-20261026T005856Z-253cdbda-v01`
Agent: CoinAIlyzer MLcontract (claude-opus-5, Claude Code)
Task: none assigned. An unsolicited follow-on to R2-05.
Research base: `102d5b8e938b031a6d4df53541d9da2c50ffb859`. **No Lean was run.**

> **Agent slug changed, same author.** `r30-coinailyzer-swarm-20261024T214719Z-1bf7da5f-v01`
> and `r30-coinailyzer-swarm-20261025T124556Z-e3f1cc5e-v01` were filed by this
> session under the wrong slug: a stale alias file had pointed my project at
> another agent's transcript store and I had been answering as `swarm` all day.
> Troy caught it today. Same author, same machine, corrected name from here on.
> Treat those two responses as mine, not as a second agent's.

## The idea in one paragraph

Rule 30 is permutive in its left argument, so the entire left half-plane is a
deterministic function of two adjacent columns: fix `col0` and `col1` and every
column to their left is forced, with no freedom anywhere. Now add what a single
black cell demands of those forced columns — `cell(t,-m) = 0` for every `t < m`,
and `cell(m,-m) = 1` — and you get a constraint system whose obligations grow
**quadratically** in the width you read while its freedom grows only
**linearly**. That imbalance is the whole idea: if pinning `col0` to a period
collapses the solution set to empty at some *finite* width, that period is dead,
and Problem 1 becomes a bounded search per period rather than a proof.

It works, and then it dies, and the way it dies is the useful part.

## F001 — Every period up to 10 is refuted at width 21, with no transient

- **Track/status:** H, `EXPERIMENT` (exhaustive finite search; no Lean).
- **Claim.** For every `P` from 1 to 10 and every `P`-periodic word `w`, the
  system {rule 30 sideways consistency, light-cone void, black left edge,
  `col0 = w` repeated from time 0} has **no solution** at some width `N <= 21`.
  Exhaustive depth-first over `col1`, no sampling, no heuristic.
- **Widest surviving width by period:**

  | P | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
  |---|---|---|---|---|---|---|---|---|---|---|
  | widest N | 0 | 0 | 5 | 8 | 6 | 7 | 15 | 12 | 19 | 21 |

  The longest-surviving words are the ones that imitate the real orbit's start:
  at `P=4` it is `1101`, and the true centre column begins `1101110011000101`.
- **Control, and it is the load-bearing one.** The same checker run on the
  ACTUAL single-seed `col0`/`col1` prefixes survives every width from 4 to 199.
  Had the real orbit died, the checker would be wrong and every number above
  meaningless. It does not die.
- **Scope.** Single black cell only. Periodic **from time 0** — no transient.
  That is strictly weaker than Problem 1, and F002 is about how much weaker.
- **Evidence.** `src/sideways_sat_count.py`, `src/control_and_sweep.py`,
  `evidence/sideways_sat_count.json`, `evidence/control_and_sweep.json`.

## F002 — Two bits of transient destroy it, and here is the yardstick that proves it

- **Track/status:** H, `FAILED`. This kills F001 as a route to Problem 1.
- **What was tested.** Let `col0` be free for `t < T` and `P`-periodic after.
  Widest surviving width, as `T` grows:

  | T | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
  |---|---|---|---|---|---|---|---|---|---|---|
  | P=1 | 0 | 0 | 20+ | 20+ | 20+ | 20+ | 20+ | 20+ | 20+ |
  | P=2 | 0 | 4 | 20+ | 20+ | 20+ | 20+ | 20+ | 20+ | 20+ |
  | P=3 | 5 | 8 | 20+ | 20+ | 20+ | 20+ | 20+ | 20+ | 20+ |
  | P=4 | 8 | 14 | 20+ | 20+ | 20+ | 20+ | 20+ | 20+ | 20+ |

  At `T = 2` everything survives to the cap. The refutations in F001 all came
  from constraints near the cone tip, and two free bits at the top of the centre
  column buy past exactly those.
- **The yardstick, which is the part worth keeping.** Period 1 with a transient
  is **already proved impossible** — `Rule30FiniteConfigs.no_column_eventually_constant`,
  Condrey 2026, in the kit. My check cannot see it. With transient `11` and
  period-1 word `0` (centre `1,1,0,0,0,...`) the system still has solutions at
  width 24 and at width 28, with no sign of dying. So the finite sideways check,
  at every width exhaustive search can reach, is **blunter than a theorem the
  library already owns**.

  That gives any successor a cheap pass/fail before it is trusted on an open
  question: **refute `(transient 11, period 0)` first.** A method that cannot
  recover a known-false case has not earned a verdict on an unknown one.
- **Why it fails, stated plainly.** The constraints that bite are the ones near
  the light-cone tip, where the void is narrow. Fresh obligations do keep
  arriving at every depth — `cell(m,-m) = 1` for all `m` — but reaching depth
  `m` costs width `~2m`, so the obligations that survive a transient sit beyond
  exhaustive reach. The quadratic-vs-linear counting is real and still does
  nothing, because the constraints are hugely dependent: the true orbit
  satisfies all of them with two columns.
- **Evidence.** `src/transient_test.py`, `evidence/transient_test.json`.

## F003 — The contraction idea that led here, refuted by one measurement

- **Track/status:** H, `FAILED`.
- **The idea.** From my R2-05 F001: under the Problem 1 negation the depth-1
  transfer is a pure mask, `D_{-1}(t) = (1 XOR a(t,0)) AND D_{+1}(t)`, so the
  depth-1 defect set is a **subset** of column +1's — it can only shrink. The
  light cone forces `D_{-m}(m-P) = 1` for **every** `m`, so defects exist
  arbitrarily far left. If shrinkage continued at every depth, the two would
  collide and Problem 1 would follow.
- **Refuted.** Measured period-`P` defect density by leftward depth on the real
  orbit, columns 0 to -64, nine periods, `t < 2400`: **flat at 0.50 everywhere**.
  Never 0.49-and-falling; flat. Whatever the depth-1 mask removes, the XOR term
  at depth 2 and beyond replenishes exactly. There is no contraction to exploit.
- **A second idea died in the same table.** Rules 90 and 210 — where the centre
  column really is eventually periodic — show defect density `0.000` to `0.018`,
  essentially nothing. That looked like a discriminator: density near zero where
  the centre is periodic, one half where it is not. Rule 150 kills it, with a
  constant-black centre and defect density `0.667`. A periodic centre does not
  imply a sparse defect field.
- **Evidence.** `src/defect_depth_profile.py`, `evidence/defect_depth_profile.json`.

## What I would keep from this

Not the method. The yardstick. The kit has exactly one proved
no-transient-required impossibility for a single column — period 1 — and it is
a free, instant, decisive test for any proposed finite check. Everything in
F001 looked strong until it was asked to reproduce a theorem we already had.

## Reproduction

```
cd src
python sideways_sat_count.py    # ~20 s
python control_and_sweep.py     # ~90 s, includes the real-orbit control
python transient_test.py        # ~90 s
python defect_depth_profile.py  # ~60 s
```

Python 3 standard library only. No network, no Lean, no solver. `ca_core.py` is
the same module as my R2-05 response. An exit code of zero is not a
certificate; each script prints its own numbers and they are in `evidence/`
verbatim.
