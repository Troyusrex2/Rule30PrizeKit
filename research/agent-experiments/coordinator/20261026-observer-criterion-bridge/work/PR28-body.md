Depends on #26. This module now connects its canonical fields explicitly to `Rule30DividedDifference.ObserverCriterion`, whose implication to `Rule30TraceEdge.EdgeObservable` is proved there. The new `ObserverConnection` theorems identify the canonical zero-gauge mode equation and common-field predicate exactly, then apply exterior coherence directly to that mode. Fixed-column observation remains the open conclusion.

The existing results are uniform in the canonical ages: initially supported common fields have exact phase coherence beyond the younger right front, and every nonzero auxiliary field over an older canonical background reaches arbitrarily large right-edge depths after every starting time. The escape theorem needs neither the common constraint nor an evolution hypothesis for the second coefficient background. These statements use dyadic returns and an asymmetric XOR-rigidity argument.

The module docstring now has a title and names the observer route; attribution is in its catalog row. This branch includes #26's updated head so the new import is available. Relative to that dependency, the change is the common-gauge module, its root import, and its catalog row.

Validation at reference commit `5473ffd075f63c9d626e63b8455805d4831b39ca`, Lean 4.35.0:

- The exact staged common-gauge source compiles and passes the unchanged official checker: all 174 constants fully replayed, five explicit headlines accepted, no new axioms.
- The imported divided-difference module was fully replayed (198 constants), as was the pinned `Rule30TraceEdge` module (14 constants).
- Final guarded compile and replay of the common-gauge module took 3.04 seconds with 754 MiB peak owned process-tree RSS. The source remains core-only and `git diff --check` passes.
- A full catalog-root build was not run.

New connection headlines: `ObserverConnection.canonical_mode_equation`, `ObserverConnection.canonical_common_iff`, and `ObserverConnection.observer_mode_right_wedge`. The observer criterion itself is still unproved.
