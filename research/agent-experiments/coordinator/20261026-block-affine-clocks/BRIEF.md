# Try the block-affine formulation; the white-boundary inverse tree is still open

[The checked module and controls](REPORT.md) now provide:

- A generic three-cell block driven with even period P has period 4*P.
  Two updates are affine triangular maps, each with fourth power identity.
- A formal proof of the known sharper clock
  `a(t+2^((2*j+1)/3),j)=a(t,j)` for every Actual white-boundary history.
- The exact two-step update: cell j flips iff the earlier pair j-3/j-4
  has a one and the nearer pair j-1/j-2 is equal (j>=4).

This is a clock tool, not sink separation. The mode corollary retains
ALL-TIME Subset; do not replace that premise by initial subset. The known
period estimate is credited to placego G249; no novelty claim is made.

The new single-profile graph at clock 64 closes at 171,780 states. Beyond
its small period-two core it has no merging; nonconstant OR uniquely
determines the current column in this finite census. A uniform inverse-tree
argument at all dyadic clocks remains a possible route. Do not infer one
from more bounded enumeration. The block-affine return could help a
recursive proof, but no terminating witness recursion is known here.

NFA searches and recent-context/prefix-parity lexicographic ranks did not
find a certificate. Preserve UNSAT versus timeout distinctions. External
RootedReturn and odd-clock ParityMask lemmas have different hypotheses;
they were not adopted as premises or counted as newly verified progress.

The [previous bridge](../20261026-reader-collision-bridge/REPORT.md) still
shows that full state-15 separation would give CollisionClock and
initial-subset preservation. The fixed-center bridge remains open too.

Use the [response format](../../RESPONSE_FORMAT.md) and a fresh unique
`D:\MWB\Rule30\agent-inbox\<response_id>\` folder; write READY last.
Include exact sources, full unchanged-checker replay for Lean claims,
caps and falsification controls. Multiple responses use separate IDs.
Do not modify other responses, prior archives or shared reference builds,
or submit a prize essay under Troy's identity.
