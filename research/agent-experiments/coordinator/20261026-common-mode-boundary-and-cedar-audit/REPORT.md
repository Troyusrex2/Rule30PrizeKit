# Boundary-sensitive common modes and independently checked Cedar results

**The prize problem and both global observer/safety gaps remain open.** This
packet records an all-time counterexample when the white boundary is removed,
two independently replayed Cedar partial results, and Cedar's independent
review of the preceding clock theorem. No new prize submission or Wolfram
backend verification is claimed.

## A real obstruction to dropping the boundary

The common-mode approach compares two actual histories A,B and an auxiliary
linear mode H. Common is the pointwise adjacent determinant constraint
`(A XOR B)[j] * H[j+1] = H[j] * (A XOR B)[j+1]`.
Initial subset means every initial black H cell lies in A XOR B.
The desired preservation statement for the one-sided white-boundary system
is still open. The following counterexample concerns a spatial SIX-CYCLE.

Read each integer least significant bit first, around that cycle:

| Time | A | B | H |
|---|---:|---:|---:|
|0|58|23|12|
|1|5|40|12|
|2|27|27|36|
|3|36|36|36|
|4|63|63|63|
|5 and later|0|0|63|

Both backgrounds satisfy the literal triangular Rule30 update with cyclic
older indices. H satisfies exactly the divided-difference mode equation.
Common holds for EVERY natural time. Initial subset holds, but subset fails
at time2. The backgrounds merge at time2, so the later Common constraint
becomes automatic; H persists. The final row is explicitly stationary under
the coupled equations, making this an unbounded-time example, not a horizon
extrapolation.

`Rule30CyclicSubsetObstructionResearch.cyclic_subset_preservation_fails`
proves this in Lean. The separate `white_boundary_fails` headline proves
`A(1,0) != A(0,0)`, directly contradicting the depth-zero equation of the
white-boundary Actual definition. Thus this does NOT refute FrontStable,
CollisionClock, white-boundary subset preservation, or Prize Problem1.
It rules out removing the boundary and replacing it by interior equations
plus all-time Common. The cyclic backgrounds coalesce; genuine finite-white
prefix evolution is injective and cannot coalesce that way.

The full unchanged checker replayed 48 constants and three headlines in
1.62s, with742MiB peak owned RSS. The first elaboration lacked two decidable
instances and an explicit finite case split; its source and logs are retained.

Cedar separately rebuilt the official dependencies and fully replayed this
exact module: all 48 constants and all three headlines passed, in 11.39s
with 743MiB peak process-tree RSS. Its independent scalar audit also checked
all seven supplied finite-cone witnesses without invoking SAT. A separate
white-boundary finite-cone control shows why that distinction matters:
the protected interior matches the cyclic example, but Common already fails
near the actual white boundary. The complete selected review is retained in
`work/independent-cyclic-review/`. The review's label "Wolfram" refers to the
producer agent, not an official Wolfram review or verifier verdict.

## Cedar's new results, independently replayed by root

Credit: the Codex Cedar team for Troy Lowry. The immutable v02 handoff
`r30-codex-cedar-followup-20261026T154236Z-b768c9a6-v02` contains664 artifacts;
all hashes were checked. Its formal sources match the earlier sealed
177-artifact stage2 snapshot used for our replay. Experimental/paper findings
were not promoted to Lean results.

`CedarZeroFront.not_safe_zero_front` proves that for every older prefix and
every natural k, the finite-white word `older ++ P ++ 0^k ++ [1]` eventually
has two consecutive newest zeros. P is the explicit24-bit word in the source.
Four updates reduce the gap by8 and shift the distinguished suffix by8 cells;
the proof retains the actual evolved older prefix. Eight terminal gaps have
kernel-checked escape certificates, and strong induction handles every k.
This is one regular suffix family. Its coverage of all remaining words is
false, so it is not a completeness proof.

`CedarFiniteInjectivity` proves injectivity of the finite triangular update
and every iterate. If a word ever reaches a whole-word eight-step return,
it already had that return initially. The exact previously checked language
bridge gives the corresponding conditional eventual-acceptance reduction.
It does not prove that a rejected safe word ever reaches acceptance.

We rebuilt the four byte-matched dependencies in a fresh private library,
then independently fully replayed all41 and7 constants of these two modules.
The batch took17.75s at757MiB peak. Their earlier238 constants remain earlier
results; they are not counted again as new mathematics.

## Independent review of the preceding clock proof

Cedar froze published commit64197054b1e4f5b768a624c16bd3c1db0555f3cb, rebuilt
the official dependencies from exact sources without a reference compiled
cache, and fully replayed all nine custom modules:388 constants, including
191 dependency constants and197 in the three new modules. It independently
reconstructed the640->192->112->90 graph,20 projections and438 even-reach
pairs. Source, hypotheses, arbitrary path induction and transient scope
passed review. Runtime70.70s, peak909MiB. This is independent confirmation of
the earlier result, not an additional theorem or official verification verdict.

The reviewer correctly notes that the odd-R seed20 control refutes dropping
parity from the OR theorem. That example's next column alternates, so it does
not establish parity necessity for the next-column corollary. The published
producer made only the former claim. An initially overstrong reviewer control
was corrected; both audit versions are retained in the independent packet.

## What the new experiments establish

The balance shortcut fails even in a genuine canonical white history:
width10, seed33 has a32-step orbit with18 newest ones and three cyclic00
pairs. Every update and wrap was independently checked with the literal rule
table. Thus uniform balance or a universal upper bound of one-half on the
black density cannot supply the proposed global argument.

Common-mode local tests are deliberately separated. Seven cyclic-time ring
searches (widths3..10, clocks2..16) were UNSAT for subset creation. They were
not a proof; allowing a finite transient immediately found the six-cycle
example above. In separate interior cones of horizons1,2,3,4,6,8,12, SAT
witnesses satisfy initial subset and Common and every retained literal
equation, yet lose subset at time1. At time t only indices j>=2t are evolved;
there are no white depth-zero/one equations after time0. These are finite
interior witnesses, not complete half-line histories or all-time extensions.
They rule out the tested finite local certificates only. No larger sweep
was used as evidence for the global claim.

All root jobs retained the300-second/8GiB-owned/2GiB-free guards. A first
solver launch could not import the already installed research Z3 package;
the runner was corrected to use its existing path, with no installation.
The independent Cedar review retained its separate stricter guard. No
configuration or authentication settings were changed.

The next argument still needs genuine white ancestry and the ordered,
unbounded temporal information. Neither the cyclic obstruction nor the
zero-front family supplies the fixed physical-center observation bridge.
