# Round-two response: the mask is the only thing rule 30 has that its siblings do not

Response ID: `r30-coinailyzer-swarm-20261025T124556Z-e3f1cc5e-v01`
Agent: CoinAIlyzer Swarm (claude-opus-5, Claude Code)
Task: **R2-05** (cross-column inheritance with actual seed ancestry).
Original response: `r30-coinailyzer-swarm-20261024T214719Z-1bf7da5f-v01` (its F001 is retracted here, see F004).
Supersedes: none. Research base: `102d5b8e938b031a6d4df53541d9da2c50ffb859`.
Verifier pin: `3eca23c0a9fa6b153313655e6d51835406c2d06e`, Lean 4.35.0. **No Lean was run.**

## Conventions

`a(t,x)` for `t >= 0`, `a(0,0)=1` and `a(0,x)=0` otherwise;
`a(t+1,x) = a(t,x-1) XOR (a(t,x) OR a(t,x+1))`. Column `x` is the sequence
`t |-> a(t,x)`; the centre column is `x=0`. For `P >= 1` the **period-P defect
field** is `D_x(t) := a(t+P,x) XOR a(t,x)`. Every claim below is labelled
PROVED (by hand, in this report), CHECKED (finite computation, stated bounds),
or OPEN.

## Batch overview

In round one I proposed solving rule 30 for the right neighbour and widening a
periodic strip rightward. The coordinator's objection was exact: knowing the
centre and the next centre does not determine the right neighbour without the
left neighbour, and my supporting measurement tracked a **moving** window, not
a fixed column. Both halves of that objection are correct, and F004 retracts
the finding.

Running the same idea in the only direction where it is deterministic --
leftwards, where rule 30 is permutive in its left argument -- gives a valid
relation. That relation is already the kit's: it is how
`Rule30FiniteConfigs.not_adjacent` and Jen's theorem are proved. The mechanism
is prior art and I claim none of it.

What is new here is quantitative, and it came out opposite to what I expected.
Writing the leftward relation in terms of the period-P defect field gives an
exact **zero-gated transfer identity**

```
D_{-1}(t) = (1 XOR a(t,0)) AND D_{+1}(t)     whenever the centre is P-periodic at t and t+1
```

(F001). The mask `(1 XOR a(t,0))` is the OR's entire contribution, and it is the
one piece of structure rule 30 does not share with any other rule for which
Jen's argument runs. Tracing defects along the leftward relation turns the
light cone into a defect rate for column +1, and that rate stops at `log2(t)`
(F001, Theorem B). I expected that ceiling to be slack. It is not: rules 90 and
210 realize orbits satisfying every hypothesis of the argument whose column +1
carries **exactly** about `2*log2(t)` defects, black precisely at `t = 2^k - 1`
(F002). No better rate is provable from the shared facts alone.

The escape is equally sharp. Both log-rate witnesses have an eventually
**white** centre, a case the kit already excludes for rule 30
(`no_column_eventually_constant`). The only remaining witness, rule 150, has a
constant **black** centre and defect density `2/3`. A 65,532-orbit sweep finds
no non-constant eventually periodic column anywhere in the family (F003). So
once the hypothetical centre is known to be non-constant, the sibling rules cap
nothing, and a positive-density defect rate is not excluded by any of them.
That is the gap I would attack next; the missing lemma is stated in F001.

**Route to Problem 1, honestly.** None of this reaches it. The chain would be: a
rate argument that consumes the ones of the hypothetical centre as well as its
zeros; pushed from `log t` to positive density in column +1; then closed against
the finite right half. Steps two and three are missing. What I can offer is that
step one is not barred, and the exact reason it is not.

---

## F001 -- Zero-gated defect transfer, and the rate it yields

- **Track/status:** H, `EXPERIMENT` (hand proofs plus finite verification; no Lean).
- **Claim.** Fix `P >= 1` and write `D_x(t) = a(t+P,x) XOR a(t,x)`.
  1. (PROVED, Lemma 3) For all `t, x`:
     `D_{x-1}(t) = D_x(t+1) XOR [ (a(t+P,x) OR a(t+P,x+1)) XOR (a(t,x) OR a(t,x+1)) ]`.
  2. (PROVED, Prop 1) If `D_0(t) = D_0(t+1) = 0` then
     `D_{-1}(t) = (1 XOR a(t,0)) AND D_{+1}(t)`.
  3. (PROVED, Prop 2) If also `D_0(t+2) = 0` then
     `D_{-2}(t) = ((1 XOR a(t+1,0)) AND D_{+1}(t+1)) XOR ((1 XOR a(t,0)) AND D_{+1}(t))`.
  4. (PROVED, Theorem B) If the centre column is `P`-periodic for all `t >= T`,
     then for every `m >= T+P` there is `s` with `m-P <= s <= 2m-P` such that
     `D_{+1}(s) = 1`, and `s` can be taken with `a(s,0) = 0`. Hence
     `#{s <= t : a(s+P,1) != a(s,1)} >= log2(t) - O_{T,P}(1)`.

- **Proofs.**
  *Lemma 0 (light cone).* `a(t,x) = 0` for `|x| > t`; induction on `t`.
  *Lemma 1 (black left edge).* `a(t,-t) = 1`; induction, since
  `a(t+1,-t-1) = a(t,-t-2) XOR (a(t,-t-1) OR a(t,-t)) = 0 XOR (0 OR 1) = 1`.
  *Lemma 2 (left reconstruction).* XOR is invertible in the left argument, so
  `a(t,x-1) = a(t+1,x) XOR (a(t,x) OR a(t,x+1))`. This is the kit's
  reconstruction and the reason Jen's theorem holds; no novelty claimed.
  *Lemma 3.* Apply Lemma 2 at `t` and at `t+P` and XOR the two.
  *Prop 1.* Lemma 3 at `x = 0`. `D_0(t+1) = 0` kills the first term, and
  `a(t+P,0) = a(t,0)`. If `a(t,0) = 1` both ORs are `1` and the bracket is `0`;
  if `a(t,0) = 0` the ORs are `a(t+P,1)` and `a(t,1)`, so the bracket is `D_1(t)`.
  *Prop 2.* Lemma 3 at `x = -1`: the OR's second argument is again `a(t,0)`, so
  the same split gives `D_{-2}(t) = D_{-1}(t+1) XOR ((1 XOR a(t,0)) AND D_{-1}(t))`;
  now substitute Prop 1 at `t` and at `t+1`.
  *Lemma 4 (locality).* Contrapositive of Lemma 3: if
  `D_x(t) = D_x(t+1) = D_{x+1}(t) = 0` then the bracket vanishes and `D_{x-1}(t) = 0`.
  *Lemma 5 (light-cone defect).* For `m >= P`,
  `D_{-m}(m-P) = a(m,-m) XOR a(m-P,-m) = 1 XOR 0 = 1`, by Lemmas 0 and 1.
  *Theorem B.* Fix `m >= T+P` and start at the site `(-m, m-P)`, live by Lemma 5.
  Given a live site `(x,t)` with `x <= -1`, Lemma 4 applied at `x+1` makes one of
  `(x+1,t+1)`, `(x+1,t)`, `(x+2,t)` live; take it. Columns strictly increase,
  times never decrease and start at `m-P >= T`, so no site in column `0` can
  occur, since `D_0` vanishes from `T` on. From a live site in column `-1` the
  only surviving option is `(+1,t)`, and by Prop 1 that step also forces
  `a(t,0) = 0`. The walk reaches column `+1` within `m` steps, each costing at
  most one unit of time, so `s` lies in `[m-P, 2m-P]`. For the count take
  `m_k = 2^k (T+P+1)`: consecutive intervals `[m_k-P, 2m_k-P]` are disjoint once
  `2m_k < m_{k+1}`, giving one fresh defect time per doubling.

- **Mechanism, and why it is rule-30 specific.** For rules 90 and 150 the same
  derivation gives `D_{x-1}(t) = D_x(t+1) XOR D_{x+1}(t)`: linear, unmasked,
  nothing deleted. Rule 30's OR deletes every column +1 defect that arrives at a
  time when the centre is black. The mask is the whole difference, and it is the
  only place where a hypothetically periodic centre's actual bit pattern -- not
  merely the fact of its periodicity -- enters a cross-column relation.

- **Barrier check.** The generic absorbing-prefix barrier and its integer-
  geometric extension concern prefix energies
  `E_r(w) = H_r + sum_i lambda^i C_r(state,w[i])` for readers that absorb after
  the 26-cell common ether prefix. Nothing here is a prefix score: the defect
  field is a function of the orbit and its own time shift, defined at every cell,
  and the state carried leftwards is the pair of adjacent columns, which never
  absorbs. The C=1 critical-charge counterexample concerns
  `5*zeros(free R,n) <= n + B + C*blackCount(Psi R,2n+1)`; no charge of that form
  appears here. The barrier that does apply is the new one in F002.

- **Verification.** `src/defect_identities.py` (stdlib, about 90 s) on the actual
  single-seed orbit to `t = 1200`:
  A1 left edge black for every `t <= 1200`; A2 light cone;
  B the reconstruction identity, 2,876,400 instances;
  C Lemma 3, 317,682 instances over ten periods `P in {1,2,3,5,7,11,14,29,64,97}`;
  D Lemma 4, 157,784 live defects of 317,682 cells;
  E Prop 1 at the 2,998 pairs `(P,t)` where the centre happens to agree with its
  own `P`-shift at `t` and `t+1`, 1,546 of them with a live column +1 defect;
  F1 and F2 Prop 2 at 5,935 and 1,500 such pairs; G Lemma 5, 11,534 instances;
  H the unmasked rule 90 transfer. All pass; see
  `evidence/defect_identities_output.txt`.
  Prop 1, Prop 2 and Theorem B have hypotheses that are **false** for rule 30, so
  on the real orbit they can only be checked where the hypothesis holds by
  coincidence; that is what checks E, F1 and F2 do. The hypotheses hold genuinely
  for rules 90, 150 and 210, where F002 checks the conclusions outright.

- **Limitations.** Nothing is in Lean. Theorem B is a rate for **column +1** under
  the Problem 1 negation; it says nothing about column 0 and is not by itself a
  step towards a contradiction. Jen's theorem already gives infinitely many such
  defects without a rate, so the only new content is the rate and the mask. The
  `O(log t)` rate is far below the positive density any charging route needs.

- **Missing lemma (smallest decisive obligation).** A **capacity** statement for
  the walk in Theorem B: that one column +1 defect at time `s` can be the
  terminus for only `O(1)` of the light-cone sources `(-m, m-P)`, rather than for
  every `m` in a whole dyadic block. With capacity `C` the count becomes at least
  `t/(2C)`, a positive density. The walk is currently a disjunction
  (reachability), not a flow, which is precisely why only disjointness of dyadic
  intervals can be exploited. F002 shows this is not barred once the centre is
  known to be non-constant.

- **Next action.** Make the walk deterministic using the mask: at a column `-1`
  site the step is forced and lands on a zero of the centre, which is a periodic
  set. If that forcing can be propagated to depth `k` through Prop 2 and its
  deeper analogues, distinct sources separate and capacity follows.

---

## F002 -- The sibling rules cap the rate at log t, and the cap dies with the white centre

- **Track/status:** H, `EXPERIMENT` (finite computation plus a classical closed form).
- **Claim.** Exactly four elementary rules satisfy every structural fact used by
  F001 and by the kit's Jen theorem -- `f(0,0,0)=0` (quiescent), `f(0,0,1)=1`
  (black left edge), and left-permutivity `f(0,q,r) != f(1,q,r)`. They are
  **30, 90, 150, 210** (CHECKED, exhaustive over all 256 rules).
  For rules 90 and 210 from the single black cell the centre column is white for
  every `t >= 1`, and column +1 is black **exactly** at `t = 2^k - 1` (CHECKED to
  `t = 16384`; classical by Kummer, since `binom(2u+1,u+1)` is odd iff `u` and
  `u+1` share no binary digit, i.e. `u = 2^k - 1`). Their period-1 defect count
  for column +1 is therefore `2*floor(log2(t+1)) + O(1)`, measured at `1.81` to
  `1.96` times `log2 t` across four decades.
- **Consequence.** Any lower bound on the defect rate of a column adjacent to an
  eventually periodic column, proved from quiescence, black left edge and
  left-permutivity alone, is `O(log t)`. Theorem B attains that order, so its
  logarithm is a ceiling for the whole class of argument, not a slack step. This
  is an independent reason for a ceiling that the coordinator's Golden defect
  clock also stops at (`D(s,cutoff(m,k)) >= k`) -- but only to the extent that
  clock's hypotheses are shared with the siblings. Its ether, No00 and Golden
  restrictions are rule-30 specific, so this mirrors that ceiling rather than
  explaining it.
- **The escape, which is the useful half.** Both log-rate witnesses have an
  eventually **white** centre. The kit already proves that no column of rule 30
  is eventually constant (`Rule30FiniteConfigs.no_column_eventually_constant`),
  so an argument about rule 30 is entitled to assume the hypothetical periodic
  centre is non-constant. The only sibling then left is rule 150, whose centre is
  constant **black** and whose column +1 has defect density `0.6667` (CHECKED).
  Under the non-constant hypothesis the family caps **nothing**: a
  positive-density defect rate for column +1 is not excluded by any rule sharing
  rule 30's structure, and the capacity lemma of F001 is not barred.
- **Fast falsification.** Exhibit any rule, or any finite seed of 30/90/150/210,
  with a **non-constant** eventually periodic column. That would cap
  shared-structure rates immediately and kill the escape. F003 looked; there is
  none in the box searched.
- **Evidence.** `src/permutive_barrier_scan.py`, `src/rate_calibration.py`,
  `evidence/permutive_family_scan_output.txt`, `evidence/permutive_family_scan.json`,
  `evidence/rate_calibration_output.txt`, `evidence/rate_calibration.json`.
- **Limitations.** The closed form `t = 2^k - 1` is verified to `t = 16384` and
  argued from Kummer; it is not proved in Lean here. The cap concerns what the
  shared hypotheses can prove; it does not say an argument using them must fail,
  only that it cannot beat `log t` while it stays inside them. Rule 210, which
  the coordinator lists beside 90 and 150, behaves exactly like 90 throughout.

---

## F003 -- 65,532 orbits of the shared-structure family: every periodic column is constant

- **Track/status:** H, `EXPERIMENT` (finite search; a negative result inside a stated box).
- **Question.** Which periods does the shared-structure family actually realize?
  A realized period is one the shared facts provably cannot exclude; a period
  realized by no member leaves a shared-structure argument unrefuted.
- **Search.** Rules `{30,90,150,210}`; every seed of width `1..14` whose leftmost
  cell is black (65,532 orbits); columns `-4..23` relative to that cell
  (1,834,896 columns); `t < 900`; periods `<= 32`; transient `<= 200`; a period
  accepted only on a full suffix match.
- **Result (CHECKED).**

  | rule | eventually periodic columns | of those, non-constant | minimal periods seen |
  |---|---|---|---|
  | 30 | 0 | 0 | -- |
  | 90 | 494 | 0 | 1 |
  | 150 | 494 | 0 | 1 |
  | 210 | 15,639 | 0 | 1 |

  **Zero non-constant eventually periodic columns in the entire family.** Rule 30
  contributes none at all, the expected control: a hit there at period 2 would
  have contradicted `CQ01`.
- **Reading.** The caution that "rules 90/150/210 expose shared-structure
  arguments that cannot prove Problem 1" is, on this evidence, precisely a
  **period-1** caution. Rule 30's period-1 case is already closed in the kit by a
  rule-30-specific monotonicity argument, and the necessity of that specificity
  is exactly what the three witnesses demonstrate. For periods `>= 2` the
  siblings supply no counterexample, so a shared-structure route to periods
  `>= 2` is not refuted by them. This narrows the warning rather than
  contradicting it.
- **Limitations.** A finite box: widths `<= 14`, 28 columns near the seed,
  `t < 900`, periods `<= 32`, transients `<= 200`. A long transient, a wider seed,
  a distant column or a period above 32 would be missed. By Jen at most one
  column per orbit can be periodic, which is why a narrow column window is
  defensible, but that is not a proof. Nothing here shows that a
  shared-structure argument for period `>= 2` exists; only that the obvious
  refutation is absent.
- **Next action.** Extend the box in the one direction that could change the
  conclusion: periods to 128 with transients to 2,000, on widths `<= 10`.

---

## F004 -- Retraction of my round-one F001 (wrong frame, missing neighbour)

- **Track/status:** H, `FAILED`. Retracts
  `r30-coinailyzer-swarm-20261024T214719Z-1bf7da5f-v01#F001`.
- **What was claimed.** That solving rule 30 for the right neighbour
  (`right = new XOR left` when the centre is 0) would widen a periodic strip
  rightwards, supported by a table showing the left side temporally periodic to
  depth 160 while the right side had no period `<= 400`.
- **Failure 1, the relation was incomplete.** `right = new XOR left` needs the
  **left** neighbour, column `-1`, whose periodicity is not supplied by the
  hypothesis and is in fact excluded by Jen's theorem once column 0 is assumed
  periodic. The usable direction is the opposite one, and it is already the
  kit's (Lemma 2 above). The coordinator's objection was exactly right.
- **Failure 2, the measurement was in the wrong frame.** The round-one probe
  tracked a 12-cell window at fixed **depth** inside the light-cone edge; that
  window moves one cell left per step. Problem 1 is about a **fixed** column.
  Recomputed in `src/frame_retraction.py` at `t < 4000`:
  - moving frame, `t in [300,700)`: left periods 4, 4, 4, 8, 8, 8, 8 at depths
    1, 5, 10, 20, 40, 80, 160 -- the round-one table reproduces;
  - fixed columns `-160, -80, -20, -5, -1, 0, 1, 5, 20, 80, 160` over
    `t in [1000,4000)`, periods `<= 400`, transient `<= 500`: **no period at any
    of them**, on the left exactly as on the right. The left is not a wall in the
    frame that matters;
  - the boundary of the regular left region sits at depth `0.756`-`0.768` of `t`
    (binary search on depth, `t = 1000..3700`), that is at `x` about `-0.24 t`,
    consistent with the known rule 30 left-boundary speed near `0.25`. A fixed
    column `x = -k` is inside the regular wedge only while `t <= k/0.24`, and is
    in the chaotic region forever after. That is the entire explanation of the
    asymmetry I reported: the window outruns every fixed column.
- **Failure 3, a vacuous period in the round-one probe.** It searched periods up
  to 400 on a 400-sample window, so `P = 400` passed on zero comparisons. The
  recomputation requires at least `P` real comparisons; with that fix the right
  side reads `64` at depth 1 and no period at depths `5..160`, instead of round
  one's `64, 256, 256, none, ...`. The qualitative claim survives the fix; two
  entries of the published table do not.
- **What survives.** Only the observation that rule 30 is invertible in its left
  argument, which is prior art, and which F001 reuses in the direction that works.
- **Limitations.** Fixed-column aperiodicity here is a bounded search (periods
  `<= 400`, transient `<= 500`, `t < 4000`) and counts as falsification only, not
  as a theorem. The wedge boundary is an empirical slope from six samples.

---

## Dependencies, conflicts, prior art

- **Prior art I rely on and do not claim.** `Rule30FiniteConfigs.not_adjacent`,
  `.jen`, `.periodic_column_unique`, `.no_column_eventually_constant` (Jen 1986;
  Kopra 2023; Condrey 2026) and the reconstruction identity named in that file's
  header. I rederived the two-column theorem before reading the kit and checked
  the kit before writing it up; it was already there, in a stronger form -- any
  two distinct columns, not merely adjacent ones.
- **Conflicts:** none known. F004 retracts my own round-one F001; no other
  agent's finding is contradicted.
- **Relation to other round-one responses.** `codex-cedar`'s disagreement
  identity compares two orbits forwards, where paths can cancel. The defect field
  here compares one orbit with its own time shift and propagates **leftwards**,
  where left-permutivity makes the relation an exact identity, so no cancellation
  arises. They are different objects; I make no claim about that finding.

## Reproduction

```
cd src
python defect_identities.py        # about 90 s, stdlib only
python permutive_barrier_scan.py   # about 30 s
python seed_sweep.py               # about 7 min, 65,532 orbits
python frame_retraction.py         # about 60 s
python rate_calibration.py         # about 90 s
```

Python 3 standard library only: no third-party package, no network, no Lean, no
solver. `src/ca_core.py` (bytearray evolution) and `src/seed_sweep.py` (bitwise
evolution) are two independent implementations and agree on all 28 columns to
`t = 300`; check B is an independent test of the first. An exit code of zero is
not a certificate -- each script prints its own PASS/FAIL lines and those are
included verbatim under `evidence/`.
