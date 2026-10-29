# Prefix-clock bridge

Target: convert the independently replayed PR51 shift law into an actual right-diagonal prefix-period word exclusion for any right-bounded initial configuration. Prefix period means every earlier diagonal has that period; individual diagonal periods may drop. No generic individual period-nonloss assumption is allowed.

First prove an abstract bi-infinite diagonal family with the literal Rule30 recurrence. Show prefix growth forces the newest diagonal to complement at the old prefix period. Then exclude prefix exponent pattern 11011 (explicit middle plateau) when base exponent >=2. Finally instantiate the family with Rule30Realization.evol, using the author's already proved rightDiag_step. Existence of prefix clocks for a right-bounded seed must be proved or explicitly retained as a hypothesis; no silent finite-seed step.

Computational control: all 512 nonzero width-ten seeds with their rightmost bit black, followed by zeroes through diagonal24. Prefix periods capped at65536, total time60s, local owned memory1GiB/system available2GiB. Record any cap as UNKNOWN. Compare generated periodic profiles to literal Rule30 evolution for every seed through time64/24 diagonals. Test the guarded pattern and record small-clock exceptions separately. No Lean claim from Python.

Formal runs: fresh dependency closure, unchanged Check replay, standard axioms only, no sorry/native tactics. One owned G913 process,300s/8GiB/2GiB available guards. Do not mutate a running package. No whole-catalog validation claim.
