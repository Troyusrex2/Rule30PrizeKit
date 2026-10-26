This module states the auxiliary observer criterion explicitly and proves that it implies `Rule30TraceEdge.EdgeObservable`, then the exact official Problem 1. The criterion remains an open hypothesis. It requires finite backgrounds, a finite mode initially supported in their difference with its left edge at a common lower bound, and the common-field constraint for all time; its conclusion concerns fixed physical observation columns.

The existing divided-difference identities and moving-front theorem now serve that stated route. The all-gauge barrier is also connected to `ModeObservable`: its finite initial mode satisfies initial subset and the common-field constraint but is invisible, while the periodic backgrounds have no left bound. The module docstring and catalog row describe these hypotheses directly, with attribution in the catalog row.

Validation at reference commit `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0:

- The exact staged module compiles and passes the unchanged official checker: all 198 constants fully replayed, seven explicit headlines accepted, no new axioms.
- The pinned `Rule30TraceEdge` dependency was freshly built and fully replayed (14 constants). The updated module remains core-only.
- Final guarded compile and replay took 2.73 seconds, with 752 MiB peak owned process-tree RSS. `git diff --check` passes.
- The PR changes only the module, its root import, and its catalog row relative to the current pinned main. A full catalog-root build was not run.

The new headlines are `edgeObservable_of_observerCriterion`, `problem1_of_observerCriterion`, and `barrier_mode_not_observable`. This proves the conditional bridge requested in review, not the open observer criterion itself.
