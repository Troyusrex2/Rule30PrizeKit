# Position-dependent parity scores and finite physical XOR rectangles

**Problem 1 remains open.** These are checked obstructions to proposed proof
strategies. They do not prove that the canonical center is non-periodic.
No new prize essay or API submission was made in this phase.

## A uniform one-cell obstruction

[Rule30WeightedCellResearch.lean](work/Rule30WeightedCellResearch.lean) proves
`all_sites_iff`. Let old and new be arbitrary functions from integer positions
and two Boolean cell values to Fin 2. Subtract each position's white/white
baseline when forming its charge. At every integer translation, test the
four possible subsets of two pulses in each of two independent physical
Rule30 histories: sixteen pairs of inputs, followed by four updates.

All those charge equalities hold if and only if BOTH old and new scores are
independent of the cell values at every position. The weights need not repeat
in space, and old and new need not agree. This is a **one-cell** theorem,
not an all-width classification with space/time-dependent scores. It is
distinct from [PR27's translation-invariant all-width theorem](../20261025-product-parity/REPORT.md).

The two pulses are seven positions apart. Their four-update mixed derivative
isolates one output position; varying the other history isolates each
Boolean argument of that position's score. Translation gives every position.
Once the new score is trivial, single-pulse tests give triviality of the old
score. The actual finite evolutions are checked inside Lean.

The unchanged official checker replayed all **97 declarations**, including
generated declarations, and accepted all seven headlines, with no new axioms.
Build plus full replay took 16.828 seconds, peak owned-tree RSS 1,250,971,648
bytes. The module uses core Lean and the catalog, without Mathlib.

## A four-history rigidity shortcut is false, even for finite starts

[Rule30FiniteRectangleResearch.lean](work/Rule30FiniteRectangleResearch.lean)
proves a permanent XOR rectangle consisting of four distinct, finitely
supported, actual Rule30 histories. At time zero their black sets are

    {-1}, {0,-1}, {-1,-3}, {0,-1,-3}.

At every subsequent time and every integer position, XOR of the first two
histories equals XOR of the last two. `physical_step` proves the ordinary
whole-line Rule30 recurrence, `initial_support` proves support in [-3,0],
`initial_distinct` distinguishes all four starts, and `finite_rectangle`
proves the all-time identity. No auxiliary evolution is substituted for a
physical history.

More generally, a paired right-boundary prefix with bits b,1,0 and an
arbitrary shared left tail returns after two steps to the same kind of prefix
with a transformed shared tail. Thus the paired difference is independent
of that tail. The difference occupies a two-cell strip moving right. This
does not contradict the catalog's three-history XOR rigidity theorem, and
does not refute the canonical left-edge observer conjecture.

The unchanged official checker replayed all **72 declarations** and accepted
all five headlines. Build plus full replay took 16.250 seconds, peak RSS
1,236,439,040 bytes. There are no new axioms or kernel shortcuts. This is a
counterexample to a candidate considered during this phase, not a prize
counterexample. No claim of historical mathematical novelty is made.

## Independent controls and finite experiments

- `audit_weighted.py` independently evolves whole-line pulse sets, verifies
  1,024 local mixed-derivative cases, and checks periodic weight spaces for
  periods 1 through 64. Rule150 controls retain nontrivial weights.
- `audit_rectangle.py` independently evolves physical cell sets for 2,080
  tail/time cases. Removing the shielding black cell breaks the proposed
  rectangle at time 2. These finite controls supplement the all-time proof.
- `clock_charge.py` solves the complete local phase-current equations at
  spatial periods 2,3, time periods 1,2, and density widths 1,2,3. Each of
  those twelve spaces contains only phase gradients and constants with a
  time-independent total. `audit_clock.py` independently checks 26,676
  cyclic states including a linear Rule150 control. This finite search is
  **not** a theorem for all clocks or widths.
- `four_step_anf.py` finds 122 Boolean polynomial terms and checks all 512
  inputs. The unique translate of the quadratic shape {0,7} suggested the
  pulse proof. The standalone polynomial computation is not Lean verified;
  the Lean proof checks its needed physical tables independently.
- `affine_history.py` and `probe_affine_quad.py` preserve the earlier finite
  search. Their flags record what was known before the later all-time Lean
  counterexample; finite survival through 128 alone was not a proof.

All final jobs stayed within the original 300-second / 8-GiB owned-tree /
2-GiB available-system-memory guards. Three failed weighted proof attempts
are retained: unreduced row lookups, then two AC simplifier timeouts. The
successful proof groups the four charges pointwise before normalization.

Both modules were checked at kit commit
`0090056412733accaa27643d3cbbf982104f2251`, unchanged checker SHA256
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
These are local official-checker results, not claims of Wolfram server or
human review. The older notebook memory waiter is separate from these
proofs; no freshly verified notebook is claimed here.

The next useful argument must retain the actual canonical histories and
control their unbounded cancellation. Neither of these obstruction results
supplies that missing step.
