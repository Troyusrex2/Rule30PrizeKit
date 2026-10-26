# Photograde aside: restrike forensics, where a time-shifted copy can hide its defects

- Response ID: r30-photograde-20261026T005626Z-1de68195-v01
- Task: unassigned aside (Troy asked for one more off-the-wall idea)
- Builds on: r30-photograde-20261025T122841Z-abce3ea0-v01 F003 (no adjacent pair of columns is jointly eventually periodic)
- Research base: 102d5b8e938b031a6d4df53541d9da2c50ffb859. **No Lean was run.**

## The idea

When a coin is restruck, the new design is stamped over an old one. Graders spot restrikes by the *undertype*: traces of the old design that show through where the new strike didn't fully cover.

Apply the same idea to Rule 30:
- Let `A(t,x)` be the single-seed diagram.
- Let `B(t,x) = A(t+P,x)` be the "restrike", the same diagram shifted P steps in time.
- Column 0 being eventually P-periodic means the restrike matches the host exactly on column 0 from some time T onward.
- The defect field `D = A XOR B` is the undertype.

The question is where the undertype is allowed to show through when the center matches perfectly. The forensic tool is left-permutivity, the same one used in F003 last round.

## F001: the undertype shows only on white cells of column 0 (EXPERIMENT)

- **Identity (exact algebra):** suppose `c0(t) = c0(t+P)` and `c0(t+1) = c0(t+1+P)`. Then

  `D(t,-1) = D(t,1) AND NOT c0(t)`.

  **Proof:** `c0(t+1) = c_{-1}(t) XOR (c0(t) OR c1(t))`, and the same holds for B. Subtract the two copies. When `c0(t)=1`, both OR terms are 1. When `c0(t)=0`, the OR terms differ exactly when `D(t,1)=1`. ∎
- **Consequence, combined with last round's F003:** suppose column 0 is eventually P-periodic from T.
  - If every column-1 defect at t ≥ T sat under a black cell of column 0, then `D(·,-1)` would vanish from T on. Columns -1 and 0 would then be jointly P-periodic, which F003 rules out for any adjacent pair.
  - **So a periodic center forces infinitely many t ≥ T with `c0(t) = 0` and `c1(t) ≠ c1(t+P)`.** Column 1's period defects cannot all hide under black cells.

  This is a necessary condition that a counterexample to Problem 1 must satisfy. It concerns the column-0 pattern itself, which F003 alone did not give.
- **Check:** the identity was verified exactly on the seed for all P ≤ 512 and t < 4707. There were 570,026 instances where the premise held, and 0 mismatches (A002).
- **Limitations:**
  - The identity is elementary algebra, and the consequence is modest. It narrows what a counterexample must look like but does not exclude one.
  - Not kernel checked.
- **Next action:** iterate the identity leftward. Express `D(·,-k)` as a masked function of `D(·,1)` and the periodic column 0. Then ask whether the defect cascade can avoid the always-black left edge, which F003 shows it cannot do forever. A Lean statement of F001 plus F003 should be short.

## F002: at finite scale, the rim never exposes a restrike, and the seed looks generic (FAILED)

- **Question:** F003's proof catches a perfect restrike at the left edge, the "rim". Does that mechanism show up at finite scale? Do near-restrikes of the seed behave differently from generic orbits?
- **Method:**
  1. For every P ≤ 512 and every start time T < 4096, measure the joint agreement run L, meaning how long columns 0 and 1 of A and B match together.
  2. For the 2,000 longest runs, find the first left-side mismatch that left-permutivity says must end the run. That gives a certificate `L* = t − T + j + 1`, where the mismatch is at time t in column −j.
  3. Classify the mismatch as "rim" if t ≤ j (at or beyond A's light-cone edge) and "interior" otherwise.
  4. Control: run the same pipeline on 5 generic orbits from fully random rows.
- **Result:**

| source | joint runs | max L | mean L | rim-witnessed (of 2000 longest) | certificate violations |
|---|---|---|---|---|---|
| seed | 325,255 | 17 | 1.612 | 0 | 0 |
| 5 random orbits | 325,952–328,885 | 15–18 | 1.594–1.608 | 0 | 0 |

  - The certificate holds in every case (`L ≤ L* − 1`). It was tight in 22 of the top 25 runs, and every top run was ended by column −1 one step before column 0 broke.
  - The rim never does the work. The seed's restrike statistics fall inside the random-orbit range, including the tail counts for L ≥ 10.
- **Conclusion:** any rim-based argument is purely asymptotic. There is no finite-scale signal to mine, and the seed is not special at this resolution.
- **Limitations:**
  - P ≤ 512 and T < 4096 only.
  - The 5 control orbits use a periodic ring, which has no light cone, so "rim" is not meaningful for them; only the run statistics are compared.
- **Next action:** stop the statistics. If this line is pursued, the useful part is F001 as a proof step.

## Reproduction

- **Commands:**
  - `python -I src/restrike.py F001`
  - `python -I src/restrike.py F002`
  - `python -I src/restrike.py F002C` (control)
- **Environment:** Python 3.11, numpy 1.24.3.
- **Runtime:** a few seconds each.
- **Determinism:** control seeds 20261025–20261029.
- **Dependencies:** no credentials and no Lean.
