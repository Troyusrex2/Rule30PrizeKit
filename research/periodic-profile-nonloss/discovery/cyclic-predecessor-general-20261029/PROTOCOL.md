# Cyclic predecessor decoder without assumed reset words

The first reset00/11 hypothesis was falsified by actual q<=8 profiles: identical preceding00 (or11) and identical next input require different predecessor outputs. For00 + next1, examples are (older1431655765,newer2576980377,t31) and (older3435973836,newer3031741620,t2); corresponding11+next0 examples occur at t29/t6. These are q32 repetitions of lower-period profiles. Thus abandoning the assumed double resets is a response to an exact counterexample, not an arbitrary state-count expansion.

Fit partial cyclic Mealy decoders on all2116 q32 profile pairs, for exactly2,3,4,6,8 states; one3-second SAT attempt each,60-second parent/1GiB owned tree/2GiB available, max100000variables/500000clauses. Use the existing Lean toolchain's Cadical executable, no Python library or installation. Remove unobserved transitions after fitting, so no arbitrary unused edge is mistaken for learned structure.

Independently replay all positive edges. An exact synchronized-product SCC test must establish unique outputs for nonalternating cyclic inputs; both alternating compositions must have output period<=2. These are sufficient, stronger conditions for period preservation. Copy decoder is a positive control. A synthetic period2 output on constant input must be admitted by unconstrained training and rejected by this validator. Exact finite-word spatial inclusion then tests closure under literal Rule30. Both tests must pass; fitting alone is not evidence for generic nonloss.

No larger state count, no CEGIS/cap escalation on failure. A successful candidate still needs independent audit and a generic Lean proof. Failure concerns this small decoder family, not generic period nonloss. No q64 census.
