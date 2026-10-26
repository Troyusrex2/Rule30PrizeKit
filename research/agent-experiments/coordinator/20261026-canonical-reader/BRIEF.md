# New target: observability on an invariant canonical language

The sound reader is now a fully checked equivalence relation. Every word
has a unique reader-equivalent canonical word. Canonical words form

`0* Sigma^{<=2} union 0*1(00|11)Sigma+`.

The seven-state DFA in `work/Rule30ReaderCanonicalResearch.lean` is the
formal definition. Normalization commutes with the white-boundary update
`x[j]'=x[j] XOR (x[j-1] OR x[j-2])`. The theorem
`canonical_completeness_reduction` proves that full reader completeness is
equivalent to:

> Equal-length canonical words with identical last-column traces at every
> time are identical words.

This **canonical observer remains open**. Exact census through width 30
found no counterexample, including all 1,073,741,824 states at that width.
This is finite evidence, not a proof. Canonical counting is independently
proved for all lengths: 2^(n-1) canonical words at length n>=3.

Please focus on a uniform observer/inverse-tree argument, a precise
counterexample, or a new certificate whose domain really is closed at all
lengths. Three-step, two-symbol-context first/last lex ranks still failed
after restriction to canonical rows; do not assume a simple local rank.
The reader's equivalence classes are not yet proved to be trace classes.

Do not assume Mode+Common makes a recombination Actual: the older theorem
retains ALL-TIME Subset. Do not turn sheared fixed depth into fixed physical
center. CollisionClock follows from full separation via the checked earlier
bridge; it is not an additional independent assumption after separation.

Return each independent response in a new versioned directory beneath
`D:\MWB\Rule30\agent-inbox`, using the existing RESPONSE_FORMAT.md and
manifest schema. Put `READY` last. Revisions use a fresh response ID and
`supersedes`. Do not edit another response, the coordinator checkout, or
the shared reference build. Label experiments, hypotheses, and full-kernel
proofs separately. Most useful: exact statements, failed controls, source
files, machine-replay instructions, and the dependency on any open claim.
