# Keep the white boundary: one-bit differences and common tails are insufficient

The [new full kernel proof](REPORT.md) gives a sharper counterexample to
boundary-free reconstruction. Start with black cells 5,9,13,... and compare
it with the same state plus one black cell at 7. Their right tails are
identical, the source stays opposite forever, and their observed heads agree
forever with period eight, not two. Nonconstant OR at cells 1/2 agrees while
cell 1 differs. Both backgrounds are infinite.

Thus do not try to prove either of these without individual finite/right-white
backgrounds: a common tail plus finite initial difference prevents nonalternating
resynchronization; or nonconstant OR determines its adjacent column. Even one
initial flip does not rescue those assertions. The periodic background has an
older period-loss precursor; do not claim that phenomenon as new.

Finite cuts give a kernel-checked arbitrary delay with the same single flip,
permanent source and width 2*T+16. No defect-only deadline can work. This
does not disprove width-dependent bounds or prove eventual separation. All
12 tested cuts separate, but that is finite evidence only.

The actual target remains all-time separation of every right-bounded word
in reader state 15, retaining the whole shared background and white boundary.
Outside state 15 the reader is already complete. Even full separation would
leave CollisionClock and the fixed-center bridge to P1. A fixed depth here
is a moving physical ray, not the vertical center.

The orbit-section experiment hit a logical state cap and is unknown; no finite
or infinite signalizer theorem is available. The controlled-strip recurrent
calculation concerns one four-cell pattern, not all defects. Avoid silently
promoting these diagnostics into premises. A global clock/tree invariant or
a boundary-aware recursive witness remains a possible direction, not a claim.

Return independent findings using the [response format](../../RESPONSE_FORMAT.md).
Use a unique local `D:\MWB\Rule30\agent-inbox\<response_id>\` directory and
write READY last, or an intake PR to Troy's fork/research branch as described
in the [handoff](../../README.md#start-and-return-a-response). Include exact
sources, commands, limits and full unchanged-checker replay for Lean claims.
Do not edit another response or prior archive, or submit a prize essay under
Troy's identity.
