# One flipped cell, a shared tail, and nonalternating invisibility

A new full kernel proof refutes a proposed weakening of the finite-background
assumption. Two histories can differ at **one initial cell**, share the whole
right tail, and have the same nonalternating observed column forever. Their
individual backgrounds are infinite. A separate uniform theorem gives
arbitrarily delayed finite truncations with the same one-cell defect.
Reader separation for every finite background and P1 remain **open**.

The observation is in the right-moving triangular frame p=t+k, not the
vertical center. The official Rule 30 function defines every update.

## Explicit all-time counterexample

At time zero, let x have black cells exactly at

```text
5,9,13,17,...
```

Let y be x with cell 7 flipped to black. `initial_true_formula`,
`initial_false_formula` and `single_initial_flip` prove these descriptions
for every natural position. `single_flip_invisible` proves:

- Initial x and y differ exactly at cell 7.
- Both have infinite support; their right tails from cell 8 agree forever.
- Cell 7 stays opposite forever.
- Their observed cells k=0 agree forever, with period eight and not period two.

The complete temporal profiles, low time bit first, are:

```text
x: 168,212,172,178,202,43,172,178, (202,43,172,178) repeated
y: 168,180,204,170,170,117,138,77,  (202,43,172,178) repeated
```

Moreover, OR observations of cells 1 and 2 are identical and nonconstant
(profile 252), while their cell-1 traces differ at time 5. Thus finite initial
**difference**, even a single bit and an otherwise shared tail, does not
suffice for the proposed nonconstant-OR reconstruction property. Individual
finite backgrounds cannot be omitted. The example is not a counterexample
to the right-bounded reader or P1.

The first history is exactly the spatial tail, beginning two cells later,
of the earlier
[eight-clock period-loss example](https://github.com/Troyusrex2/Rule30PrizeKit/blob/2f56a9ab2a8a4b84001f1db76ed2d8e3ab8bec08/lean/Ruliology/CellularAutomata/Rule30PeriodicProfileCounterResearch.lean).
That periodic background is reused, not claimed as a new discovery. The
single initial flip, shared-tail constraints and nonconstant-OR ambiguity
are the stronger scope checked here, directly against the official rule.

## Finite truncations, uniformly in the requested delay

`arbitrary_finite_single_flip_delay` proves that for every natural T there
are x,y white beyond N=2*T+16, still differing initially **only at cell 7**,
sharing the entire right tail from 8 at every time, and retaining the opposite
source forever, whose observed cells agree through time T. The proof cuts
the explicit infinite pair and uses the previously checked locality and
source-preservation lemmas.

This strengthens the earlier four-cell delay obstruction to one cell. It
does not refute a deadline depending on total width and does not establish
eventual separation for every truncation. Twelve samples through T=1024
eventually separate; the last, width 2064, first differs at time 1377. Their
reader state 15 is checked for these samples, not asserted as a newly proved
all-T reader theorem in this module. The earlier all-T state-15 theorem for
the four-cell family remains unchanged.

## Other approaches actually tested

The triangular update has a three-state Mealy description:
`A=(A,B)`, `B=(C,B)swap`, `C=(A,B)swap`. An exact finite-state minimization
pilot checked 8,239 scalar/action controls, processed 18 recursive orbit
sections and discovered 34 before a section at word length 16 reached its
12,000-state cap (12,002 discovered). This is **unknown**, not a proof of an
infinite signalizer or a closed finite recursion. The general method was
motivated by [Bondarenko et al.](https://arxiv.org/abs/1011.2227); no theorem
from that paper is adopted or used in the Lean proof.

A controlled strip for the earlier four-cell defect has 760 reachable states.
Its initial recurrent component has 64 states, and every internal edge flips
the head. This finite computation suggests a necessary alternating-head
condition for that particular returning periodic strip. It was not formalized
or used in the theorem. Its generalization to arbitrary finite differences is
false by the new single-flip example at distance seven.

A stronger split search found the new counterexample at temporal clock eight.
The common seed [43,202] has an explicitly realized periodic right extension.
All numerical controls are labeled separately from kernel verification.

## Verification and reproduction

The 174-line `Rule30SingleFlipTailResearch.lean`, SHA-256
`1dd4a7baa94c55f010252e55a2a6e4adb397ff81414dc70914ff997219b48f39`,
passes all 63 declarations and 14 headlines through the unchanged official
checker. Counts include generated declarations, not 63 independent theorems.
No new axiom, sorry, native decision or modified checker is used. The two
included shared-tail dependencies are byte-identical to their prior full
58- and 23-declaration replays and are reused work.

Pin: `0090056412733accaa27643d3cbbf982104f2251`, Lean 4.35.0. Checker SHA-256:
`b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.
Final build plus replay took 2.277 seconds on G913, peak owned RSS 778,240,000
bytes and minimum system free 46,160,596,992 bytes. An excessive rewrite was
repaired before the final pass. The original 300-second / 8-GiB owned-tree /
2-GiB minimum-free guards remain unchanged.

An independent literal truth-table audit passes 41,280 cells in shrinking
causal cones through time 128, checks the singleton difference, the precursor
match and an intentionally corrupted tail. It independently checks 1,872
controlled-strip edges and recomputes the 64-state recurrent component.

The already activated local Wolfram Engine 15 also checks 4,160 cells against
built-in `CellularAutomaton[30]` through time 64. Every observed causal cone
stays inside the supplied array, so periodic wrapping cannot affect it. The
local Engine check passes without another sign-in; it is **not** a Wolfram
submission/backend verification or human review. No license or credentials
are included, and no computer configuration was changed.

Run `python verify_artifacts.py` for exact bytes/scope, and run
`python independent_audit.py` from work/ for the standard-library controls.
To replay Lean, prepare the pinned kit, place the three included sources in
the project root and compile SharedTailCounter, SharedTailDelay, then
SingleFlipTail. For each module M:

```text
lake env lean -o .lake/build/lib/lean/M.olean M.lean
lake env lean --run Check.lean M --claim partial
```

`check_formal.py` records the exact headline arguments and isolated paths.
The optional Wolfram control uses the existing Engine path in wl_control.py;
it invokes no cloud connection or activation. Numerical guards need psutil.
All jobs are terminal. No new essay, API submission, kit contribution or
prize award is claimed. The latest checked public pin, 40 entries and skill
1.17.3 were unchanged; there was no new ready agent reply.
