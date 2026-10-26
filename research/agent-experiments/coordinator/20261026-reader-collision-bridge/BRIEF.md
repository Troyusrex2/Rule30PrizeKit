# Sink separation now also supplies the collision clock

[The new full kernel proof](REPORT.md) closes a gap in the plan. Every
accepted reader prefix either shields the next difference permanently
(states 0, 3, 12), or supplies the exact alternating/two-step clock (state
16). This holds for all widths and all times in the actual one-sided
white-boundary dynamics.

Hence **full separation in the reader's state-15 sink implies CollisionClock,
first-source stability and, with finite initial difference, initial-subset
preservation.** The older brief saying CollisionClock would remain separate
after completing the reader is superseded. The source proves the accepted
case unconditionally; SinkSeparates remains an explicit unproved premise
for the global conclusions. The fixed-center past bridge remains open too.

Please target sink separation while retaining the whole white-boundary
background, or the fixed-center bridge. A recursive witness may grow with
the background. Finite-difference/common-tail replacements remain false,
even for one initial flip. Local defect size cannot bound the waiting time.

Six regular/tree invariant searches did not find a certificate. Exact
backward preimages grow to 7, 129 and 12,306 minimized states at depths 1, 2
and 3, then hit the next composition's 100,000-state cap. These are audited
Python experiments, not an impossibility theorem for finite invariants.
Do not infer unbounded closure from finitely many tested heights or from a
candidate whose verifier stopped at a resource cap.

Return findings using the [response format](../../RESPONSE_FORMAT.md).
Use a fresh unique `D:\MWB\Rule30\agent-inbox\<response_id>\` directory;
write READY last. Multiple findings and independent responses have separate
IDs. Include exact sources, caps, counterexamples and full unchanged-checker
replay for Lean claims. Do not edit another response, the coordinator's
checkout, prior archives, shared reference builds, or submit a prize essay
under Troy's identity.
