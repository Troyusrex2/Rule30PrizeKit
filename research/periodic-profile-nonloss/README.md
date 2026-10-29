# Low-clock nonloss at arbitrary spatial depth

Partial core-Lean results by Troy Lowry. Generic period nonloss and all Rule 30 Prize claims remain open.

## What is proved

For every initial configuration white to the right of a boundary R, consider its ordinary Rule30 right diagonals. Let the **whole prefix** through diagonal n have least dyadic period `2^E`. If `E <= 5`, then:

1. The last diagonal in that prefix has no period `2^e` with `e < E`: it realizes the whole-prefix exponent.
2. The following diagonal cannot have period `2^e` with `e < E`, either.

These statements hold at **every spatial depth**, with arbitrary initial cells to the left. There is no finite-width bound or finite-left-support assumption. Thus a first individual dyadic-period drop, if one exists, must follow a whole-prefix clock of at least64. This does not rule out a first drop at clock64 or above, or later behavior once a larger prefix clock has occurred.

The actual statements are `Rule30ProfileGraphCases.actual_small_clock_minimal` and `actual_no_drop_below_sixty_four`. They explicitly use the prefix clock, rather than silently assuming individual-period nonloss. Existing dyadic periodicity of actual profiles is supplied by the prefix framework.

## Why a finite certificate gives an all-depth theorem

Fix q=32. Each state is a pair of q-periodic Boolean profiles `(a,b)`. A next profile c satisfies

    c(t+1) = c(t) xor (a(t) or b(t)).

Its initial bit determines it uniquely. If the full-period forcing has odd XOR parity, no q-periodic successor exists; otherwise there are exactly two complementary successors. Starting at the white pair `(0,0)`, the complete forward graph has2116 states.

`Rule30ProfileGraph` proves a generic certificate theorem. It translates finite cyclic word equations into literal infinite-profile equations, rules out odd-parity nodes using the running-XOR shift law, reconstructs every actual bounded-period prefix from the white boundary, and propagates a smaller period backwards through a checked graph. The concrete certificate checks closure and period inheritance on every node. The boundary and reconstruction premises are discharged in the actual-seed theorems; they are not left as assumptions about encodings.

The finite period range is essential. This is an invariant at arbitrary spatial depth for a fixed bounded clock, not a finite-width calculation promoted to an unbounded-period theorem.

## Verification and reproduction

Official kit pin `932cf8dde039b89b1dcbe9636867bb1b2057fef0`. The exact attributed `Rule30RightProfiles` dependency comes from ghywel's [PR51](https://github.com/WolframInstitute/Rule30PrizeKit/pull/51), head `5d4cc975534cb09cd424646696de2488838afb52`. PrefixClock and PrefixBound retain the exact previously checked source bytes from the [prefix-clock archive](https://github.com/Troyusrex2/Rule30PrizeKit/tree/e1ff89b9cd0059082ea0126e35414dc8a4a11d9c/research/right-prefix-clock). No authorship of PR51's module is claimed here.

A fresh ten-source dependency-closure build and the **unchanged official checker** replayed all428 owned declarations across the two new modules, including15 explicit headlines. There were no reused objects, source warnings, or new axioms. The combined type/axiom smoke check passed. Most of the350 declarations in Cases are generated certificate helpers, not separate mathematical insights. The whole catalog was not built.

The initial single large certificate reached its8GiB cap and was stopped. The same fixed data was split into32-node batches. The successful fresh build and replay took84.91seconds and peaked at approximately1.12GiB owned RSS, within the unchanged300-second/8GiB cap. No computational axioms, `sorry`, `native_decide`, or weakened checks are used.

Reproduce on Windows with Python and the exact recorded Lean4.35.0 toolchain:

    python -B replay/verify.py --lean C:/path/to/toolchain/bin/lean.exe --out D:/new-empty-output

All dependencies, toolchain/checker hashes, build logs, all declaration replays, type output, resource receipt, and exact source hashes are included. The data auditor in `discovery` independently checks every cyclic equation and every node's period inheritance, and realizes each of the2115 nonroot q32 nodes as an actual finite-seed orbit. Those numerical checks supplement the kernel certificate.

## Numerical evidence and failed approaches

The complete graphs for q=2,4,8,16,32 have8,12,36,68,2116 states. Their raw data and generator are included. Only the final q32 graph and generic reconstruction are adopted through the Lean proof.

Two independent-purpose numerical censuses exhaust all16,777,216 exact finite T-map states at width24 (23,144 cycles, maximum period8192). One finds no adjacent individual period drop. The other checks predecessor uniqueness after aligning cyclic profiles: outside period1/2, each newer profile has the same older profile wherever it occurs, across8244 canonical profile classes. These are **bounded Python evidence**, not Lean theorems or proofs of generic nonloss/uniqueness.

The small graphs have an intriguing stronger pattern: all nonalternating newer profiles determine their predecessors uniquely; only the two alternating words admit three predecessors each. Attempts to explain this with a cyclic Mealy decoder were unsuccessful. A proposed00/11 reset model was contradicted by explicit actual low-period examples. A follow-up without those reset assumptions was UNSAT for2,3,4,6,8 states in the stated fixed-white-loop family. This does not exclude every finite-state decoder. Training, exact closure, and exact period-preservation are separate obligations; no model passed all of them. The finite-word closure validator is a sufficient stronger requirement, not equivalent to the main conjecture.

The experiment scripts, controls, caps, failures, and receipts are retained under `discovery`. Their SAT answers and bounded observations are not substituted for the kernel proof.

## Remaining gap

The next missing mathematical step is unbounded in the clock size. The q32 certificate does not supply an induction to q64 or arbitrary powers of two. The observed predecessor-uniqueness pattern is stronger than nonloss and may require a nonlocal explanation; it has not been proved at arbitrary clocks. These results do not establish homoclinic past closing, the absence of finite legal Gate rows, Q01, or a Prize conclusion. A catalog integration must coordinate the still-unmerged PR51 dependency rather than silently duplicate its module.
