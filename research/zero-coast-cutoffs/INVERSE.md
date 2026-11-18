# How far can a change of reset rhythm reach?

The period-two reduction in the prize kit asks about finite starting rows in the Rule 30 left half with a fixed white boundary. A proposed proof would complete a finite legal near-wall history by repeating the six-tick rhythm forever. If the difference from the six-tick reference stayed shallow enough while reconstructing earlier rows, the known oscillating tail of the reference might force set bits inside the part of the initial row determined by the history. The following example rules out that proposed bound on the **outermost** disagreement.

## A legal switch with an exact inverse speed

Index the first evolving cell by 0 and increase the index into the left half. Kit depth equals index plus one. The six-tick reference has near-wall word `011111` in forward time. Start the reference at time 0 and reconstruct an earlier history whose near-wall zeros occur at times −16, −10, and 0, with ones in between. The two gaps are 6 and 10. From time 0 onward the two rows evolve identically.

At time −16 the last disagreement with the in-phase reference is at index 37. At time −16−n it is **exactly 37+14n**, for every n ≥ 0 and every choice of the n earlier near-wall bits. The rows agree at every greater index. In particular the formula survives every legal choice of earlier resets.

The preceding gap can also be ten. Its five near-wall bits from −15 to −11 are the same. Choosing a one instead of a zero at −16 changes only the first two cells of that predecessor. The theorem `alternate_entry` verifies this second entry and the identical tail at index 37; the same induction applies. Thus a final ten-tick return before a purely six-tick future already suffices when its past continues with legal returns.

In the six-tick reference the spatial tail repeats after 84 cells. At the last disagreement the inverse rule reads the known tail using two predecessor bits. For all four choices of those bits it gives a disagreement 14 cells deeper, followed by two matching bits. These two matches and the deterministic recurrence reproduce the entire remaining periodic tail. The phase returns to its starting value, so induction applies. The 16-step entry, nonvacuity for arbitrary earlier prescriptions, phase calculation, induction, and correspondence with the kit's `zrow` are in [ReverseFront.lean](ReverseFront.lean).

This compares two infinite completions. A finite initial row's first H evolving cells determine the first H near-wall bits. A discrepancy outside those cells supplies no lower bound on the mass inside them. The existence of a finite seed that survives infinitely many legal switches remains open.

## Exactly one other six-tick pattern shares the deep tail

For a six-periodic near-wall word, encode forward phase t as bit t of a six-bit integer. The white wall and the word specify two full temporal columns. Rule 30 uniquely determines the next deeper column from those two. In packed form the next pair is (b, rotate(b) XOR (a OR b)), where bit t of rotate(b) reads bit t+1 modulo six.

For every one of the 64 words the pair after 93 spatial steps equals the pair after 9. Thus any eventual merger with the reference can be detected at depth 9: once two ordered pairs coincide, every later pair coincides; repeated 84-step returns bring both back to their depth-9 values. Exactly the masks 62 and 26 coincide there. In forward time order these are `011111` and `010110`, respectively. The latter is an actual time-periodic Rule 30 solution which agrees with the reference at every index ≥8 and differs at index 7 at time 0. Its consecutive zeros across the period boundary exclude it from the legal reset language. The theorems `advance_local`, `six_merge_iff`, `compact_steps`, and `compact_tail` check the column encoding, classification and physical control.

## Sharp bounds for individual clocks

[periodic_cut.py](periodic_cut.py) constructs the complete spatial orbit for each specified periodic wall word and checks every transition, including the wrap, against the literal Rule 30 truth table. For a width bound W, truncate the reference initial row just before index W. Its first mismatch with the reference is the first black bit at or beyond W. By left permutivity, a first spatial mismatch at j gives the first near-wall mismatch at tick j. No other seed of width at most W does better. The following entries give the maximum number of matching ticks **in excess of W**, over every W. Within a row the entries follow the reset phases in chronological order.

| Repeated gaps | Spatial pair preperiod | Spatial pair period | Sharp excess by starting reset |
|---|---:|---:|---|
| 6 | 1 | 84 | 5 |
| 10 | 1 | 155 | 6 |
| 6, 10 | 39 | 325 | 8, 7 |
| 6, 6, 10 | 73 | 13123 | 11, 11, 11 |
| 6, 10, 10 | 2407 | 2444 | 9, 10, 10 |

For example the +8 occurs at W=281. These are complete finite-orbit computations for the listed clocks. They give no uniform bound over all legal gap sequences.

## Reproduction

Use Python 3 and the Lean version in the kit's `lean-toolchain`. From this folder run `python periodic_cut.py` and `python replay_front.py --lean PATH_TO_LEAN`. The second command builds the required kit modules from this checkout into a fresh temporary directory, invokes the kit's unmodified partial-claim checker, and prints its JSON receipt. The [recorded receipt](verification.json) is a local run. The kit base for this note is [ac3d144](https://github.com/WolframInstitute/Rule30PrizeKit/tree/ac3d1440c6dbce52a45aa404e4d614ce85d4b8d1).
