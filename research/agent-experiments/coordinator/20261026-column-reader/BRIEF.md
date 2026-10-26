# Next target: complete the sound temporal-column reader

Read [REPORT.md](REPORT.md) and the exact sources and certificates in work/.
P1 remains open. The 17-state reader has full kernel-checked **soundness**
at all widths and times; its rejection predictions remain unproved.

The paired alphabet is 00,01,10,11, scanned from the white right boundary
toward increasing depth. The single-history update is
`x[j] XOR (x[j-1] OR x[j-2])`. A fixed depth follows a moving physical ray,
not the vertical center. `reader_sound` proves accepted paired prefixes have
equal last temporal columns. The 47-state product establishes acceptance
invariance under one update and equal current last bits. Do not turn this
into a converse without a proof.

Try to prove or falsify completeness: every rejected pair should eventually
have unequal last bits. The reject sink (state 15) is the main gap. A finite
clock enumeration or another accuracy/depth increase will not establish the
unbounded claim. Additive state/edge weights, macro-step additive weights
(2,3,4 updates), and lexicographic state/input digits in both directions
(1,2,3 updates) have failed in the included templates. Six macro updates hit
a graph cap, not a logical refutation. A local separation invariant also
fails without global boundary reachability.

Possible directions include a nonlocal recursive separation witness, a
stronger inductive invariant for OR-profile collisions, or an exact analysis
of the triangular map's Mealy automorphism. No claim that these will work.
Inspect failed templates before repeating them. Reachable profiles need not
be balanced: the period-eight counterexamples are included.

Completeness would be useful for the prior [CollisionClock target](../20261026-front-clock-reduction/BRIEF.md),
but that implication itself needs proof. Unconditional subset preservation
and a fixed-center past extension also remain open. Keep those gaps separate.

For multiple independent replies, use the repository's existing
[response protocol](../../README.md#start-and-return-a-response): a fresh
unique response ID/directory, manifest, exact sources, commands, results,
limits and READY marker. Never edit another agent's response or old archives.
State whether each result is a conjecture, a finite test, a solver result or
a full kernel replay. Use unchanged official statements/checker at the
recorded pin; no axioms, sorry, native_decide, bv_decide or native reduction.
Keep replies independent so several agents can return without clobbering.
