# New agent target: a uniform decoder for one previous bit

Please build on the checked canonical normal forms and this new reduction:

`Rule30ReaderObserverReductionResearch.parent_bit_complete_reduction`

It proves that full reader completeness at every width is equivalent to:

> Equal-length canonical rows with equal final-bit traces at all times
> have the same penultimate initial bit.

The property is `ParentBitObserver` in the source. Empty prefixes use the
specified false default. It is enough to prove a uniform formula for that
one bit; time covariance, normalization of shorter prefixes, and a checked
250-state extension invariant handle the rest. **This property is OPEN.**

The canonical language is `0*Sigma^{<=2} union 0*1(00|11)Sigma+`, formally the
seven-state DFA from the preceding checked module. It is invariant under
`x[j]'=x[j] XOR(x[j-1] OR x[j-2])` with missing bits zero. Normalization is
unique and commutes with updates. Apply prospective filters to canonical
rows; raw representatives can have different predecessor profiles.

New evidence worth investigating: on all canonical rows of every width
3..14, all raw coordinates lie in the F2 span of products of at most THREE
final-bit observations. This is a finite algebra experiment, not a proof
or an assertion for larger widths. At width 14 the cubic space has dimension
7,073 on 8,192 canonical rows; it contains all coordinate functions.

`work/diagnostics/newton-decoder-filters.json` gives explicit penultimate
filters through width 10, checked against literal trajectories. With
`d[k]=XOR_{i bit-subset k} f[i]`, they have degree at most three in `d` and
term counts 1,4,7,19,30,63,132 at widths 4..10. Can you derive a uniform
coefficient recurrence or a closed difference-algebra identity? An affine
parity-only filter already fails at width five; the four-row obstruction
is included. Do not replace a uniform proof by further rank tables.

A second checked module supplies a useful case: if a newer profile is
anti-periodic over a driving clock P and the older profile is P-periodic,
`OR(t) XOR OR(t+P)=NOT older(t)`. A periodic zero and forced flips recover
the newer profile too. `actual_or_clock_observer` lists the exact premises.
The non-clock-extending case is not solved. `plateau_local_counterexample`
formally gives an eight-step free-upstream band with equal OR outputs and
different newer profiles, despite two exact local equations. Any proposed
inverse must use the additional ancestry constraints it lacks.

No P1/Q01 claim is proved. Even full reader completeness leaves the fixed
physical-center bridge open. CollisionClock/preservation follow from full
reader separation via the older checked bridge; do not add them as separate
assumptions after separation. Mode+Common still does not make a recombination
Actual without ALL-TIME Subset. Do not drop those hypotheses.

Return one new versioned response directory beneath
`D:\MWB\Rule30\agent-inbox`, using RESPONSE_FORMAT.md and the manifest
schema; multiple findings may have separate statuses. Put READY last.
Revisions use a new ID and `supersedes`. Do not alter another response,
the coordinator checkout or shared reference build. Clearly distinguish
failed tests, conjectures, and full-kernel proofs. Precise counterexamples
and failed controls are welcome.
