# Mixed derivative modes: exact obstruction to the local parent alternative

`HeightTwoMixedControl.lean` passed unchanged full declaration replay, 39 declarations. It supplies an all-time free-boundary countercontrol to the proposed local lemma: a height-two child need not have a Safe, coSafe, or height-two immediate parent, even with five shared predecessor equations, every adjacent transition-cover relation, and the four established forbidden cylinders in every supplied column.

This is NOT a genuine finite-white counterexample. The oldest two temporal profiles remain free. No white-anchor embedding, arbitrary-depth older ancestry, or actual finite initial word is supplied or asserted.

## Exact witness and what Lean proves

The clock is fixed at32; bit t of each mask is its value at time t modulo32. The seven columns are ordered oldest to newest:

| Column | Mask | Signed white drift over32 | Observed one-period height span |
|---|---:|---:|---:|
| r | 2572815714 | 0 | 3 |
| q | 3920235100 | 5 | 7 |
| w | 2930510420 | 4 | 7 |
| v | 3040087144 | -1 | 4 |
| u | 3576171432 | 3 | 7 |
| A | 2787642032 | 7 | 7 |
| b | 1513098543 | 0 | 2 |

Lean proves all five actual update equations `D c_j = c_(j-1) OR c_(j-2)` for j=2..6, at every natural time, including cyclic wrap. For each adjacent pair L,R, it proves `L <= D R <= L OR L_next`. Every supplied column avoids11011,00100,000111,111000 for all time. The finite certificate is lifted using exact modulo32 identities.

Lean also proves b has all-time signed WHITE-height in `[0,2]`, using positive-even periodicity, zero drift, and the closed-period adapter. It proves b is not eight-periodic. It proves both parents A and u have temporal00 and11 occurrences, so neither is Safe nor coSafe. Finally `H_A(32)=7` and `H_u(32)=3`, together with H(0)=0, refute every possible all-time height band of width2 for both parents.

The Python literal replay additionally computes least period32 for each of the seven displayed profiles and the entire height table. The Lean headlines claim period32 and b not-eight, not an independently formalized least-period theorem. No assertion about an actual whole-prefix return clock is attached to this free strip.

## The exact role-switching obstruction

The newest derivative has this cyclic block sequence, with each gap a run of zeros in D b:

| Start time | Active length | Gap | Mode | A active part | u active part | Delta H_b | Delta H_A | Delta H_u |
|---:|---:|---:|---|---|---|---:|---:|---:|
| 3 | 3 | 1 | 3a | 011 | 101 | 2 | 0 | 2 |
| 7 | 3 | 1 | 3b | 101 | 111 | -2 | 2 | 1 |
| 11 | 1 | 7 | 1 | 1 | 1 | 1 | 1 | 1 |
| 19 | 1 | 1 | 1 | 1 | 1 | -1 | 1 | 1 |
| 21 | 1 | 2 | 1 | 1 | 1 | 0 | 0 | 0 |
| 24 | 3 | 1 | 3a | 011 | 101 | 2 | 0 | -2 |
| 28 | 4 | 3 | 4a | 0101 | 1011 | -2 | 3 | 0 |

Each increment includes the complete active block and following gap. The final row wraps through time34; the next block begins at35, congruent to3. The child increments cancel to0, while the parent increments accumulate to7 and3. Modes3a and3b put temporal11 in different parents; mode4a adds another u11. Thus excluding only the pure both-parent11 block4d leaves this obstruction intact.

`mixed-modes.json` records the exact segments and arithmetic. It is a diagnostic of this one fixed witness, not an exhaustive grammar classification. It introduces no new solver query.

## Validation

Source SHA-256: `975f1d613efc0e5763dfbcdda326b22ba0fe0626ab0497b3fb1edc08f53689a8`.

Dependency manifest SHA-256: `0eb28c0f069ddc67929534d1aacf76fd798ff0cdda3156cd12fc51a18f70074e`. Eleven dependencies,572 existing declarations, were freshly compiled and fully replayed in this owned phase. Official pin5473ffd075f63c9d626e63b8455805d4831b39ca, Lean4.35.0, unchanged Check.lean SHA-256 b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905. No peer binaries, new axioms, sorry, native decisions, checker modifications, or reference modifications.

Successful leaf replay: `formal/HeightTwoMixedControl/attempt02/`,5.67seconds,1.28GiB peak owned RSS, more than40GiB system memory available. Dependencies took39.91seconds. All jobs used300seconds/8GiB owned process tree/2GiB minimum system-free guards; none fired. All jobs are terminal.

One fixed SMT query at clock32 and seven columns found the assignment in0.19seconds; its entire guarded job took1.20seconds and54MiB. Existing local Z3 was used read-only. No clocks, widths, or strip depths were swept. An initial script error passed two nested constraint lists to Z3 before the solver ran; exact failed source and logs are retained. A one-line flattening fix produced the single actual solver query. The complete SMT-LIB and result are preserved. Lean does not trust SMT output: it checks every exact fixed claim from the masks.

Lean attempt01 failed to synthesize a decidability instance for the three named constraint predicates. Unfolding those predicates before `decide +kernel` resolved it; attempt02 passed. Both exact sources and logs remain preserved.

For independent replay, copy exact `.lean` files, dependencies.json, guard.py, and replay.py to a fresh owned G913 folder without previous lib/formal outputs, then run:

```powershell
C:/Users/troyu/Miniconda3/python.exe <fresh>/guard.py replay.py dependencies
C:/Users/troyu/Miniconda3/python.exe <fresh>/guard.py replay.py HeightTwoMixedControl fresh
```

## What remains necessary

The genuine finite-white one-step reduction remains open. The candidate may still hold with the white anchor, but cannot follow from the displayed bounded-depth recurrences, cover relations, cylinders, and child height condition alone. A spatial induction needs an invariant established at the white boundary and preserved through arbitrary preceding columns; bounded local admissibility is insufficient. The fixed witness supplies no evidence that such an invariant cannot exist.

No enlargement of this control, new publication, or prize submission was performed by this worker. Further symbolic boundary-invariant notes are separate from these frozen kernel claims.
