# Agent update: a proved exterior phase and a new bounded-band conjecture

Keep the exact all-time canonical observer target from the
[original precise brief](../20261025-trace-followup/BRIEF.md). P1 is open.

New [PR28](https://github.com/WolframInstitute/Rule30PrizeKit/pull/28) is fully
kernel checked but not merged. For all U>V, an initially subset common D/W
field obeys h(t,p)=h(0,U)*cell(U+t,p) for p>V+t. A distance-dependent finite
version and zero-background common-mode classification are proved. The
auxiliary field is not assumed physical. The center/left-edge overlap is open.

The current research target is stronger than simply checking more widths:
prove or refute the following ALL-WIDTH statement. In the moving right frame,
a and b evolve by Phi(x)=x XOR((2x) OR(4x)). Suppose a is initially odd,
bits 1 and 2 of a are equal, and b is initially even. Can any nonzero h
satisfy the exact D/W recurrences for all time while remaining in a fixed
finite band of right-edge depths? The candidate answer is NO. No initial
subset condition appears in the strongest tested version. It is UNPROVED.

The ordinary-coordinate definitions are in PR28. In right-depth coordinates
j=olderFront-p, the update is

    h'_j = h_j + (1+b_(j-2))*h_(j-1) + (1+a_(j-1))*h_(j-2),
    delta_j*h_(j-1) = delta_(j-1)*h_j.

All arithmetic is F2; negative-depth cells are white. Require actual evolution
of a,b and global D/W, including outflow at the band's left edge. In a band
0..L-1, the two D outflow rows at L and L+1 and the W row at L matter.
Ignoring them manufactures spurious modes.

Why try this: exact canonical prefixes have no band mode in 4,610 cases
through L=13. A stronger arbitrary-prefix test has none at L=2..8 in
43,688 parameterized older-class-zero/younger-even cases, even without
initial subset. These are finite evidence only. A=3,B=2 does have the known
two-cell escaping mode and violates the older three-bit condition; retain
it as a control. Do not count overlapping subset versions as disjoint data.

Do not replace this by the already known Mealy/group2369 model or by a finite
rank census. A useful response extracts an unbounded mechanism, a genuine
counterexample or a theorem linking such band growth to the moving center.
The band conjecture by itself would still not prove P1.

Backward lifting remains another route, but neither the new exterior phase
nor merely adding the left edge has established it. A tested left-edge family
passes arbitrarily requested sampled finite horizons and has no subset lift,
but the family's all-H theorem is not yet Lean checked and its center values
are generally NONZERO. It is not an observer counterexample.

Use the parent response schema, a NEW response_id per agent/version, and a
findings array. Shared-machine responses go in
D:\MWB\Rule30\agent-inbox\<response_id>\ with READY written last. GitHub
responses go in research/agent-experiments/responses/<response_id>/ on your
own branch or fork. Never edit another response or coordinator worktree.
Separate checked proof, finite evidence, failed hypotheses and proposals.
Include exact sources, hashes, verifier pin and unchanged full kernel reports.
