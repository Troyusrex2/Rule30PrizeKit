# The critical charge is paid by a transient, not by the periodic part

Response ID: `r30-coinailyzer-wiki-20261025T124335Z-f16dc412-v01`
Task: **R2-07** (a seed-specific information or scale-charge estimate).
Original response: `r30-coinailyzer-wiki-20261024T214827Z-f1e1a394-v01`. Supersedes: nothing.
Research base: `102d5b8e938b031a6d4df53541d9da2c50ffb859`.
Verifier pin: `3eca23c0a9fa6b153313655e6d51835406c2d06e`, Lean 4.35.0.

Nothing here is kernel-checked. No Lean was built, no checker was run, and no
theorem is claimed. Everything below is exact integer computation plus the
statements it suggests, labelled accordingly.

---

## Batch overview

My round-one entropy idea is dead and the update says why: the deficit I measured
is a generic local-rule constraint, and the spectral threshold I proposed accepts
every candidate period word. I dropped it rather than widening it.

Reading `CRITICAL-CHARGE-ONE.md` against the official definitions turned up a
structural fact that reframes the whole charge question, and it is the spine of
this response:

> `Psi R = Theta (free R)` and `free R k = zrow (Psi R) (2*k+1) 1`, so **both sides
> of the critical charge are functionals of the single free stream `f = free R`.**
> The right half `R` enters the inequality only by deciding which streams `f` are
> achievable.

That is a real narrowing. Any proposed mechanism that reads `R` in a way that does
not factor through `free R` is using information the inequality cannot see. It also
makes the extremal question finite-dimensional in a useful way, because
`Rule30GoldenCoupledResearch.golden_free` says every `free R` is Golden, so the
excess `5*zeros(f,n) - n` grows at a rate of at most `3/2`, with equality exactly on
the eventually-alternating streams. The whole constant-coefficient question becomes:

> among eventually-alternating Golden streams, how **sparse** can `Theta f` be?

Three independent findings follow.

- **F001 (COUNTEREXAMPLE_CANDIDATE).** Two finite right halves give ratio `> 2`, so
  **`C = 2` fails for every additive allowance `B`**, exactly as `C = 1` does. The
  smallest natural coefficient not refuted by anything I tested is **3**.
- **F002 (EXPERIMENT).** The extremal search. A *purely periodic* free stream never
  beats `7/4`; every ratio above 2 comes from a **transient** — a single phase slip
  in an otherwise alternating stream. The sparsest reconstructed row found has
  density `2/7`, capping the ratio at `21/8 = 2.625` over everything searched.
- **F003 (FAILED).** My first construction. I predicted that the phase-3 members of
  the same proved ether-and-wall trap would give the sparse row. They give the
  *dense* one: density `6/7`, ratio `7/8`. Reported because it closes off the one
  route that would have made F001 kernel-checkable by copying an existing proof.

**Route to Problem 1 and its gap.** None of this proves CQ01 or Problem 1, and
F001 does **not** touch `ScaleCharges`: my witnesses have `blackCount(Psi R, 2n+1)`
growing linearly, which dwarfs the `floor(k/2)` slack at `n = cutoff(m,k)`. What
F001 does is price the pointwise route that implies `ScaleCharges`: it is still
available, but not below `C = 3`. The gap that remains is stated as the missing
lemma in F002.

---

## F001: two finite right halves refute the `C = 2` critical charge

- **Track/status:** H / `COUNTEREXAMPLE_CANDIDATE`.
- **Exact claim.** With the official definitions,
  `CriticalCharge C B R := forall n, 5*zeros (free R) n <= n + B + C*blackCount (Psi R) (2*n+1)`,
  there exist finite right halves `R` with
  `limsup_n (5*zeros(free R,n) - n) / blackCount(Psi R, 2*n+1) > 2`,
  hence `CriticalCharge 2 B R` is false for **every** `B`. Two of them:
  - **W1**, black exactly at positions 3, 7, 11 (`0x888` with position `p` at bit `p`).
    Ratio `-> 21/10`.
  - **W2**, black exactly at positions 4, 5, 6, 9, 13, 16, 17, 18 (`0x72270`).
    Ratio `-> ~2.3288`.
- **Mechanism.** `free W1` is the alternating stream carrying one **phase slip** at
  index 2 (`0 1 1 0 1 0 1 0 ...`). Golden permits this: a slip repeats a bit, and the
  repeat is `11`, which is legal, while `00` is not. The slip costs nothing in zero
  density — still exactly `1/2`, so the excess still grows at `3/2` per step — but it
  changes `Theta f` from the period-7 ether row `1100001` (density `3/7`) to a
  period-14 row with 5 black per period (density `5/14`). Less sideways black for the
  same excess is precisely a higher charge ratio: `(3/2)/(2 * 5/14) = 21/10`.
- **Barrier check.** The generic absorbing-prefix barrier and the integer-geometric
  finite-image barrier are about *readers and prefix energies*; this finding proposes
  no reader and no rank, so neither hypothesis applies. It is the same kind of object
  as `CRITICAL-CHARGE-ONE.md`: an explicit right half whose two counts are computed.
- **Fast falsification, and the control I ran.** The whole thing dies if my
  implementation of the official objects is wrong, so the first artifact reproduces
  the published kernel-checked witness exactly before anything new is claimed:
  `Rule30Ether.config 3 1 6 wall` gives free stream `0101...`, sideways row `1100001`
  repeated, `zeros = 7k` and `blackCount = 12k` at `n = 14k`, ratio `7/4` — all four
  published facts, and the packed word `0xd6e0` is the brief's `0x6b70` with position
  1 at bit 0. A second, separately written implementation (plain dictionaries, the
  Lean recursions transcribed literally, no bit packing) agrees cell for cell.
- **Result — proved, observed, conjectured, unknown.**
  - *Observed, exactly, by integer arithmetic to `n = 20000` (depths `0..40000`):*
    for W1 the free stream is the slip stream at every one of 20,000 steps, `Psi W1`
    is exactly period 14 with 5 black from depth 100 to depth 40,000, and
    `5*zeros - n - 2*blackCount` is `28, 138, 350, 708, 1422` at
    `n = 500, 2000, 5000, 10000, 20000` — linear growth, so no `B` absorbs it. For W2
    the same quantity is `55, 375, 1019, 2091, 4233`.
  - *Observed:* `5*zeros - n - 3*blackCount` is negative and decreasing on every
    witness, at every sampled `n`.
  - *Unknown:* whether the free streams continue past `n = 20000`. See limitations.
  - *Not claimed:* that `C = 3` suffices for anything.
- **Evidence.** `A001` `src/coupled_core.py` (objects + the reproduction selftest),
  `A002` `src/controls.py` (independent implementation + cycle analysis),
  `A003` `src/witnesses.py` (the headline), logs `A010`, `A011`, `A012`.
  Command: `python -I src/witnesses.py 20000`, about one second, standard library
  only, no solver, no Lean, well inside 8 GiB and 300 s.
- **Verification.** `finite_computation`. Exact integers throughout; the simulated
  width always exceeds the true support, which spreads rightwards at speed one, so
  the truncation is not an approximation. **This is not a kernel replay.**
- **Missing lemma — the smallest decisive obligation.**
  > For the finite right half `W1` with black cells exactly at positions 3, 7, 11:
  > `forall s >= 2, drv altCol W1 (2*s+1) 1 = decide (s % 2 = 1)`, and `drv altCol W1 1 1 = false`.
  Everything else in F001 follows from that by the same bridge arithmetic as the
  published `C = 1` module: the free stream determines `Psi` through `Theta`, and the
  period-14 row is a finite check plus induction. The published witness proves its
  analogue (`right_col1`) from `Rule30Ether.trap_invariant`; F003 explains why that
  particular route is not available here, so this lemma needs a different invariant.
- **Limitations.**
  - Not kernel-checked, not replayed, no Lean built. The status is
    `COUNTEREXAMPLE_CANDIDATE` and should not be cited as a theorem.
  - A 20,000-step agreement is not an infinite assertion. This is the same gap the
    brief warns about and I am not claiming otherwise.
  - It refutes `C = 2` only; it says nothing about variable coefficients,
    `ScaleCharges`, or `No00SpatialCharge`, and nothing about CQ01 or Problem 1.
  - Both witnesses have **infinite** sideways support, so both are consistent with
    CQ01, exactly as the published `C = 1` witness is.

---

## F002: the extremal search — a transient buys the excess, and the cap is `21/8`

- **Track/status:** H / `EXPERIMENT`.
- **Exact question.** Over Golden streams `f`, maximise
  `rho(f) = limsup_n (5*zeros(f,n) - n) / blackCount(Theta f, 2*n+1)`.
  By the reduction in the overview, `sup_R rho(free R)` is the smallest uniform
  constant the critical charge could possibly use, and `rho` is the only quantity a
  constant-coefficient search is really fighting.
- **Mechanism, and the one sentence I would keep.** Golden caps the zero density at
  `1/2`, so the numerator's rate is at most `3/2` and is attained only by eventually
  alternating streams. The denominator is then the density of `Theta f`. Scanning
  **purely periodic** Golden streams with cycle length up to 12 — 474 of them with
  positive excess rate — the maximum ratio is `1.748`, attained by `01` itself, i.e.
  the published witness. Nothing purely periodic beats `7/4`.
  > Every ratio above 2 in this response comes from an eventually-periodic stream
  > with a **transient**. The periodic part of the free stream does not buy the
  > excess; a finite defect in front of it does.
  That is worth saying plainly to the solver effort: a model that reads only the
  asymptotic grammar of the free stream cannot see these witnesses at all.
- **Fast falsification.** Exhaustive, not sampled, on the parts that matter:
  - all 262,144 right halves supported in positions 1..18, screened at `n = 120` and
    re-measured at `n = 2000..4000`;
  - all Golden streams of the form `<prefix> + alternating tail` for prefix length up
    to 18 (13,664 of them), plus one- and two-slip streams with slip positions up to
    41 and single slips pushed out to index 79;
  - all cyclically Golden periodic streams of cycle length up to 12.
- **Result.**
  - *Observed:* `Theta` of the pure alternating streams has density `3/7` (ratio
    `7/4`) and `6/7` (ratio `7/8`) for the two phases. One slip at index 2 gives
    `5/14` (ratio `21/10`); at index 13 or 14, `9/28` (ratio `7/3`); at index 26,
    `8/28 = 2/7` (ratio `21/8 = 2.625`). Pushing single slips to index 79 and adding a
    second slip never went below `2/7`; over the range where an exact cycle was
    detected (slip index up to 26) the eventual period saturated at 28.
  - *Observed:* the best **achievable** ratio, i.e. realised by an actual finite right
    half rather than by a hand-built stream, is `~2.3288` (W2, F001). The gap between
    `2.3288` and `2.625` is a gap in my search over `R`, not a proved bound.
  - *Conjectured:* `sup_R rho(free R) = 21/8`, so `C = 3` suffices and is optimal.
  - *Unknown:* whether the density of `Theta f` is bounded below at all. My searches
    found a floor at `2/7` but I have no argument for one.
- **Evidence.** `A004` `src/prefix_density.py`, `A005` `src/slip_trend.py`,
  `A006` `src/charge_ratio_search.py`, `A009` `src/periodic_scan.py`;
  logs `A013`, `A014`, `A015`, `A016`.
- **Verification.** `finite_computation`, deep-window densities on depths up to 6,000
  and exact eventual periods where one was detected within 200. Densities quoted as
  rationals (`5/14`, `9/28`, `2/7`) are the exact per-period counts of a detected
  cycle; densities quoted as decimals are finite-window measurements.
- **Missing lemma — what would turn the conjecture into the bound.**
  > For every Golden `f` that is eventually alternating, `Theta f` is eventually
  > periodic with period dividing 28 and at least 8 black cells per 28 depths.
  With the Golden cap on the zero density this gives
  `5*zeros(f,n) <= n + B + 3*blackCount(Theta f, 2*n+1)` for every achievable stream,
  i.e. the uniform critical charge at `C = 3`, which the published
  `Rule30GoldenScaleChargeResearch` then turns into `ScaleCharges` and `CQ01`. The
  statement is finite-looking and is the smallest thing I would try to formalise.
  The quantitative version for streams of zero density **below** `1/2` is not covered
  by my search and is the obvious hole in it.
- **Mechanism answer to the question R2-07 actually asks.** "What converts the finite
  right half into a uniform-in-`k` bound?" My answer is that nothing about `R` does,
  beyond achievability — and that the inequality is not really asking for a constant.
  The constraints `forall n: excess(n) <= B + C*blackCount(2*n+1)` are nested in `n`,
  and `2*n+1` is exactly the light cone of time `n`, so the family **is** Hall's
  deficiency condition for a cone-respecting assignment of excess-zero tokens to
  sideways black cells with multiplicity at most `C`, modulo the slack `B`. The
  missing object is therefore a **constructible assignment** read off the dynamics,
  not a constant to be found by a solver; and an assignment is uniform in `k` for
  free, which is the property the scale-charge formulation has to assume.
- **Limitations.**
  - All exhaustive claims are exhaustive only inside the stated ranges.
  - `2/7` is a measured floor, not a proved one. If it is not a floor, no uniform `C`
    exists and the pointwise route dies entirely rather than moving to `C = 3`.
  - I did not search streams of zero density strictly between `1/5` and `1/2` in any
    systematic way beyond the periodic scan.
  - The Hall reformulation is an equivalence, not a new resource. It does not escape
    any barrier by itself and I make no claim that it does.

---

## F003: the phase-3 ether trap does **not** give the sparse row (failed prediction)

- **Track/status:** H / `FAILED`.
- **Exact claim that failed.** `Rule30CriticalChargeOneCoreResearch` proves
  `altCol t = ether 3 (t+1)` and builds its witness as `config 3 1 6 wall`. Ether
  column 3 is `[false,true,false,true]`, which has period **two** in the phase, so
  `ether 3 (t+3) = altCol t` as well — phase 3 is the same alternating driver, and the
  published witness uses phase 1 only. I predicted that the 27 phase-3 members of the
  same proved trap family would realise the sparse sideways row, which would have made
  F001 provable by copying an existing kernel-checked proof with different parameters.
- **Result — reproducible rejection.** They realise the *opposite* extreme. Phase 3
  gives free stream `1010...` and sideways row `1011111` repeated: density `6/7`, the
  densest row in the family, ratio `7/8`. All 27 phase-3 wall states give the identical
  ratio `0.875`, and so do `k = 6, 13, 20, 27`. The reason is now clear and is the
  content of F002: within the pure-ether trap, column 1 is forced to be ether column 4,
  so the free stream is forced to be exactly alternating — and an exactly alternating
  stream is precisely the case that carries no transient.
- **Evidence.** `A007` `src/phase_three_witness.py`, log `A017`.
- **Verification.** `finite_computation` at `n = 2800`.
- **What the failure does not rule out.** It does not refute F001; the witnesses there
  stand on their own computation. It rules out one *proof route* for F001: the
  ether-and-wall trap cannot produce a free stream with a phase slip, because the
  alternating driver pins the ether column. A different invariant is needed, which is
  why F001's missing lemma is stated as a free-standing obligation.
- **Next action.** Stop looking for the F001 witnesses inside the pure-ether trap
  family. Look instead for an invariant for a configuration that enters the ether
  *after* a bounded transient, since a bounded transient is exactly what the slip is.

---

## Reproduction and delivery

Environment: Windows, CPython 3, **standard library only** — no numpy, no solver, no
Lean, no network. Every script runs in seconds and well inside 8 GiB and 300 s.

```
cd src
python -I coupled_core.py                 # reproduces the published C=1 witness
python -I controls.py                     # independent implementation + cycles
python -I witnesses.py 20000              # F001 headline
python -I phase_three_witness.py 2800     # F003 (the failed prediction)
python -I prefix_density.py 14 1600       # F002
python -I slip_trend.py 26 3000           # F002
python -I charge_ratio_search.py 14 120 2000 10   # F002
python -I periodic_scan.py 12 1600        # F002, the purely periodic contrast
```

`src/wallstates.json` is the 109-entry `Rule30Ether.wallStates` table parsed out of
the kit source; the parse is self-checked by the presence of the published `C = 1`
wall at phase 1, and by the phase histogram 26/29/27/27.

Raw outcomes are in `logs/`, byte-for-byte as produced, including the failed
prediction. Exit code zero is not a certificate and nothing here was replayed through
the kernel; where I write "observed" I mean a finite computation and nothing more.
No credentials, configuration or unrelated files are included. No prize essay is
submitted and none is proposed.
