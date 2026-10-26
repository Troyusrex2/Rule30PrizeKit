# Slips are particles: the doubling clock is forbidden, and one defect reaches 7/2

**response_id** `r30-coinailyzer-wiki-20261026T005537Z-e656e7b7-v01`
**prompt** aside to R2-07 (seed-specific information / scale-charge estimate), round two
**kit commit** `102d5b8e938b031a6d4df53541d9da2c50ffb859`
**builds on** `r30-coinailyzer-wiki-20261025T124335Z-f16dc412-v01` (same author, round two)
**arithmetic** exact integers and `fractions.Fraction` throughout; no floating-point quantity
is relied on

---

## What round two left on the table

Round two established three things this aside depends on, and they are not re-argued here:

1. **Both sides of the critical charge are functionals of one stream.** `Psi R = Theta (free R)`
   and `free R k = !u R k`, so for
   `CriticalCharge C B R := forall n, 5*zeros (free R) n <= n + B + C*blackCount (Psi R) (2*n+1)`
   the right half `R` enters *only* by deciding which free streams `f` are achievable.
2. **`free R` is always Golden** (`Rule30GoldenCoupledResearch.golden_free`): no `00`, no
   `11111`. Hence the zero density is at most 1/2, with equality exactly on
   eventually-alternating streams, and the excess `5*zeros(f,n) - n` grows at rate at most 3/2.
3. **A single phase slip is the transient that buys ratio.** A parity flip in the alternating
   stream is Golden because it creates `11` and not `00`; `0x888` reaches 21/10 and `0x72270`
   about 2.3288, which is how round two refuted `C = 2`.

For an eventually-alternating Golden `f` the zero density is exactly 1/2, so the whole question
collapses to the eventual black density `d` of the reconstructed row:

> **ratio(n) = (5\*zeros(f,n) - n) / blackCount(Theta f, 2n+1) -> (3/2)/(2d) = 3/(4d).**

"Is there a uniform `C`" is therefore, on this family, "is there a positive floor on `d`".

## The off-the-wall idea

`ScaleCharges` measures at `cutoff(m,k) = (m+16)*(2^k - 1)` and allows slack `floor(k/2)`.
The statement has a **doubling clock built into it**. A slip is a localised defect in the
alternating ether of the free stream. So: treat slips as **particles** and let the adversary
slip **once per doubling** --- defects at `m, 2m, 4m, 8m, ...` --- so that he presents a fresh
transient at every scale at which he is measured. A gas of defects on the statement's own clock.

It does not work, and the reason it does not work is exact rather than empirical. That is F001.
What came out of chasing it is F002, F003 and F004.

---

## F001 --- A doubling slip schedule is not merely unachieved, it is forbidden

**status: FAILED**

Golden splits into two conditions on a slip set, and the first one is a parity law:

- **no `00`** iff the first slip sits at an even index (phase 0) **and every consecutive gap is
  ODD**. Checked exhaustively over all 65,535 non-empty slip sets inside positions 0..15:
  **0 mismatches** (`logs/04-geometric-clock.txt`).
- **no `11111`** is a separate restriction and is *not* characterised here. It is not a run-length
  condition on the slip set: slips at 2, 3, 4, 5 have all-odd gaps and so pass the `00` law, yet
  the stream carries `11111`. Three candidate run-length laws were tested and all three fail
  (13,008 / 11,090 / 11,998 mismatches for runs >= 4 / 5 / 6). Only the `00` law is claimed, and
  only it is needed below.

A doubling schedule has gaps `m, 2m, 4m, ...`, so **every gap after the first is even**. At most
two slips can sit on a doubling clock, and for even `m` not even two. Enumerated for `m = 1..40`,
`k = 2..5`: **no doubling schedule of three or more slips is Golden, for any m.** Since `free R`
is always Golden, the schedule is unavailable, not merely unobserved.

The surviving half of the idea is worth one sentence, because it redirects the attack: the
`floor(k/2)` slack grows with `k` while one slip contributes one bounded transient, so the slack
is not what the adversary is fighting. The fight is over `d`.

## F002 --- Slips do not cooperate: a gas is worse than one well-placed defect

**status: EXPERIMENT**

Exact eventual densities of `Theta f` (period detected, black cells counted in one period), over
legal slip sets with positions <= 60 (`logs/02-density-floor.txt`):

| slip count | best density | ratio_inf = 3/(4d) | configuration |
|---|---|---|---|
| one   | **3/14** | **7/2**  | slip at 94 (sweep to L <= 1200) |
| one   | 2/7      | 21/8     | slip at 26 (positions <= 60) |
| two   | 9/28     | 7/3      | slips at 0, 13 |
| three | 2/7      | 21/8     | slips at 0, 1, 26 |

Adding a defect never produced a sparser row than the best single defect. At the single-slip
optimum `L = 26`, every legal second slip at gap 1..23 *lowered* the finite-`n` ratio, from
2.4896 to at best 2.0078 (`logs/01-slip-gas.txt`, section B). Defects do not superpose into
sparsity; the second one re-seeds the dense ether.

This is a measurement over the tested configurations, not a proof of a general anti-cooperation
law, and it is stated that way deliberately.

## F003 --- One slip at index 94 reaches 7/2, which would refute C = 3

**status: COUNTEREXAMPLE_CANDIDATE** (conditional on achievability --- see the missing lemma)

The alternating free stream with its single slip at index 94 is Golden, and `Theta f` is **exactly
period 28 with 6 black cells per period**, i.e. density **3/14**, so

> **ratio -> 3/(4 \* 3/14) = 7/2 = 3.5.**

`5*zeros - n - 3*blackCount` on that stream (`logs/06-verify-94.txt`), exact integers:

| n | zeros | blackCount(2n+1) | ratio | 5z - n - 3b |
|---|---|---|---|---|
| 1000  | 500  | 682  | 2.199413 | -546 |
| 2000  | 1000 | 1112 | 2.697842 | -336 |
| 4000  | 2000 | 1969 | 3.047232 | **+93** |
| 8000  | 4000 | 3682 | 3.259098 | **+954** |
| 14000 | 7000 | 6255 | 3.357314 | **+2235** |

It is **negative through the transient**, crosses zero between `n = 2000` and `n = 4000`, and then
grows --- the crossing is late because the row's pre-slip prefix is dense. Unbounded growth is
what refuting `C = 3` requires, and this is the shape of it. The quantity is recomputed on a
**second, independently written implementation** (`controls.py`, dicts and the literal Lean `recon`
recursion, no machine words): **0 disagreements over depths 0..1600**.

**This is not a counterexample yet, and the gap is the whole of it.** Over all 65,535 right halves
supported in positions 1..16, the free streams realise 10,988 distinct slip schedules, but **only
slip indices 1 and 2 occur as single-slip streams** (`logs/05-achievable-slips.txt`). Slips at 14,
26, 94 and 190 were not realised in that search. Round two's best *exhibited* right half, `0x72270`,
reaches about 2.3288. So the distance between 2.3288 and 7/2 is not a distance in the dynamics ---
it is entirely achievability.

### The missing lemma, stated exactly

> **Lemma (needed).** For even `L >= 3`, decide whether the Golden stream
> `f_L(s) = (s + [s >= L]) mod 2` lies in the image of `R |-> free R` over finite right halves
> `R`. Equivalently: exhibit a finite `R` with `free R = f_94`, or prove the image contains no
> single-slip stream with `L >= 3`.

Either answer is worth having. A construction gives `C >= 4` outright. A proof of the negative
caps the achievable single-slip ratio at 21/10 and makes the right half --- not the Golden
condition --- the binding constraint, which would be the first structural statement about the
image of `free`.

## F004 --- The sparsity ladder is quantised in units of 1/56

**status: EXPERIMENT**

Over all 230 legal single slips with `L <= 1200`, every eventual density of `Theta f` has
**denominator dividing 56** (observed periods 7, 14, 28, 56), so

> **ratio_inf = 42/k**, where `k` is the number of black cells per 56 depths.

Observed `k`: 12, 14, 16, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36,
38, 39, 48. The minimum is **k = 12**, attained **once**, at `L = 94`
(`logs/03-single-slip-sweep.txt`).

So on this family the entire problem is a floor on one integer. `k >= 12` would make 7/2 the exact
supremum of the single-slip family; `k = 1` would give 42. Nothing in this aside bounds `k` below
--- that is the second open question, and it is cheaper to attack than the lemma above because it
is a statement about one periodic orbit of `Theta`, not about the image of `free`.

---

## Reproduction

```
python -I src/coupled_core.py            # selftest: reproduces the published C=1 witness
python -I src/geometric_clock.py         # F001
python -I src/density_floor.py 120       # F002
python -I src/verify_94.py               # F003, on both implementations
python -I src/sweep.py 1200              # F004
python -I src/achievable_slips.py 16 70  # the achievability gap
python -I src/slip_gas.py 1200           # the first pass, including the failed geometric section
```

Every number quoted above is in `logs/`, produced by exactly those commands. `src/coupled_core.py`
and `src/controls.py` are carried over unchanged from the round-two response, so their hashes match
that manifest.

## What I would NOT claim from this

- Nothing here is a theorem. F003 is conditional on an unproved achievability statement and is
  classified as a candidate for that reason alone.
- F002's anti-cooperation is a measurement over configurations with positions <= 60, not a law.
- F004's quantisation is observed over `L <= 1200`; a period not dividing 56 at larger `L` would
  not contradict any other finding here, it would just widen the ladder.
- The published `C = 1` refutation and round two's `C = 2` refutation stand on exhibited finite
  right halves. This aside exhibits none; it exhibits a *stream*.
