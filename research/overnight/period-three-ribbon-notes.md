# A certified prefix restriction and a history-dependent rank search

Developed by Troy Lowry with OpenAI Codex, 2026-10-24. The period-three
constraint and the Rule 30 Prize problems remain open. No priority claim.

## What is proved

`Rule30ThreePrefixResearch` certifies a necessary condition on the left half
driven by the effective boundary `010`. Suppose column -1 has phases
`(*,0,1)` forever. Compare any current row with either of two period-three
ether references. If its first differing cell is at depth d+1, counted from
the boundary, then d is divisible by three. For a finite row a first
difference exists. Finiteness and the constraint survive every restart at
time 3n, so the condition holds at every such restart.

The two references have head modes zero and one, and the spatial codes
1272 and 159 in twelve-bit, least-significant-bit-first form. The module
proves their actual evolution under the same boundary and their agreement
with the forced head phases. Left permutivity propagates a first differing
cell to a head difference at exactly time d. A fixed phase cannot admit
that difference. The argument uses the kit's existing driven-left
permutivity and ether; it excludes no new temporal period.

All 59 declarations and sixteen selected headlines pass full replay by the
unchanged working and pinned checkers. See
`three-prefix-evidence/{catalog,pinned}/report.json` and reproduce with
`verify_three_prefix.py`. The pinned adaptation removes only module/import/
export wrappers. No additional axioms or native decision procedures are used.

Independent scalar controls check every word below 2^14 and 256 wide rows
with deliberately placed first differences: 16,640 cases, through depth 400.
Eight independent built-in Rule 30 cones compare 44,891 cells under the
prescribed boundary, all passing. The initial Wolfram control used the wrong
bit orientation when placing a left row on the spatial line; that control
failed, the orientation was corrected, and the full comparison then passed.
The scalar evolution and the Lean proof were not changed to accommodate it.

## What is only a search

The previous score depended only on the current row. The new score is
V(current,previous), retaining an actual finite predecessor. This matters:
G(55)=G(56)=400, so a unique finite inverse must not be assumed.

Two six-bit inverse pipelines read the latest row Y and reconstruct actual
rows X and W with G(W)=X and G(X)=Y. There are 500 raw reachable combined
pipeline states. The search also tracks the three initial head modes,
position modulo twelve, and first-reference-match flags. A delayed local
charge accounts for two-cell spatial ribbons without discarding their
prefix context. Exact scalar controls compare the generated rows and all
feature accounts on 256 finite histories. The inverse controls also check
8,192 possible current words, including eight accepted finite branches.
These graph coverage checks are not Lean proofs.

A width-20 finite fit with 3,076 features and 1,947 added wide histories
returns a floating solution, but its rational reconstruction is not an
exact certificate. Independent holdouts reject it: 905 of 4,056 accepted
histories violate a required inequality. The graph oracle finds a smaller
concrete violation at W=1962143, X=13267103, Y=116875423, a width-21 history.
It checks both scalar equalities and all necessary prefix restrictions.
This rejects that fitted score, not the period-three conjecture.

The unrestricted history graph has 61,974 vertices. Applying the now
certified necessary first-defect restriction leaves 59,508 vertices and
118,840 edges. Direct synthesis with two families of graph potentials
reaches its sixty-second limit with both dual simplex and an interior-point
solver. Those answers are unknown, not infeasibility proofs.

`period_three_ribbon_oracle.py` instead searches accepted paths for concrete
counterexamples to a proposed score. It reconstructs each finite history and
checks G independently before reporting it. When coefficients have a small
common denominator, the path arithmetic is exact. An exact fixed point
would supply graph potentials; a bounded search without a counterexample
does not prove the graph inequalities.

`period_three_ribbon_cegar.py` feeds those concrete histories back into an
L1-minimizing fit. Its reports retain every cut and distinguish iteration
limits, numerical issues, bounded oracle exhaustion, and a possible exact
graph certificate. Even an exact certificate would still require a Lean
proof of graph coverage and of the connection to `C3w w011` before a
period-three exclusion could be claimed. No ranking has been verified.

The objective remains the complete center-column problem. This route
targets its open period-three subcase; it does not address every period.
