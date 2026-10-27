# Exact response filters and gated return constraints

Two new uniform Lean results concern actual finite-word Rule30 dynamics:

- A temporal difference filter erases both appended initial bits exactly
  under two explicit vanishing conditions on the older observation streams.
  This holds for every nonempty prefix, every positive filter order and all
  times, with no period premise.
- A gated two-cell extension inherits every supplied whole return of its
  older nonempty prefix. The gate predicate itself is not inherited, so this
  does not supply a repeated shortening argument.

Read the [precise statements and reproduction instructions](bundle/REPORT.md).
The new sources are [ResponseFilter](bundle/sources/Rule30CAResponseFilterResearch.lean)
and [GateReturn](bundle/sources/Rule30CAGateReturnResearch.lean). The former
compares two configurations with different appended initial bits; those
interventions are not automatically available within one observed orbit.

The two leaves add46 kernel-replayed constants and6 selected headlines.
The complete portable bundle, including13 previously published dependencies,
was freshly rebuilt and replayed:15 modules,1163 constants and49 headlines,
all passed in62.55 seconds with no resource stop or new axioms. Counts include
generated declarations. The official compiled dependency library was reused;
this is not a cold Mathlib build. The actual reference remains5473/Lean4.35.0.
See the [fresh reproduction receipt](reproduction-receipt.json).

The [notes](notes) are separately labelled PAPER results, not Lean theorems.
They derive an exact gap-four return and its marker-run interpretation,
identify the complete odd-cover defect that drives a clock birth, and give
concrete failures of simple global-maximum and white-insertion approaches.
Only named controls were used; no larger state/period sweep is hidden in them.
Independent source/scope audits and exact control reruns are included.

General plateau reconstruction, gate halving, reader completeness, the
physical-center bridge and Prize Problem1 remain open. No Wolfram essay was
submitted. All5145 hashes in the prior54 owned archives were verified unchanged.
artifacts.json records every file in this archive except itself.
