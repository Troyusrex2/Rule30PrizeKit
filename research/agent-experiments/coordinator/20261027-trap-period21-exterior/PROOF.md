# Proof outline and exact scope

Let a temporal profile have21 Boolean entries, with bit t representing time t. Let U shift a profile by `U a(t)=a(t+1 mod21)`. For actual Rule30 columns,

    U C_j = C_(j-1) XOR (C_j OR C_(j+1)).

Thus a pair(a,b) has the unique left predecessor

    G(a,b) = (U a XOR(a OR b), a).

The implementation reduces the first numeric component modulo2^21. Both components of every actual encoded profile pair are below2^21. The physical bridge proves this formula directly from the official `IsR30` recurrence, including temporal wrap from20 to0 and spatial overlap of adjacent pairs.

If a bounded infinite right continuation existed, its successive pairs s(n) would satisfy `G(s(n+1))=s(n)`. Encode each pair as42 bits of `a+2^21*b`. The official `Rule30Jen.pigeonhole` theorem supplies i<j with equal encodings. Equality of all low42 bits and the proven bounds imply equality of the natural codes and then of both profiles. Applying G^i to that equality gives s(0)=s(j−i); applying G^(j−i) gives a positive return of s(0). No list of2^42 states is constructed or evaluated.

For the normalized trap head pair(1198372,1591590), the kernel checks a1967-step path to a closed26313-step cycle that avoids the head pair. A seed that reaches a closed cycle excluding itself cannot return: any sufficiently large multiple of a proposed return period reaches that cycle and would equal the forbidden seed. The certificate proves endpoint equality and exclusion at every position. It uses206 segments of at most128 steps, joined by a general SafePath composition theorem. No Nodup, minimal preperiod, or least-cycle assertion is needed or claimed.

The resulting `Physical.no_period21_history` excludes an actual right-half history having the specified normalized first two temporal profiles and common period21 in all columns. The stronger named connection checks all815 original packed trap states, including black driver phases, against the full head profile1591590. It also checks the21 bits of the driver profile1198372.

Once a correctly aligned state i is entered, the existing official trap invariant advances its label at every tick. Waiting21−label(i) ticks reaches label0. Shift the actual history by that amount. Its driver and full head then have exactly the two normalized profiles, and its common period21 is preserved. The physical obstruction gives the final contradiction for every entry label.

This argument does not require finite initial support. It excludes the specified common period, not all actual histories through the trap. The trap's nine shielding columns and arbitrary strip boundary input are never substituted for a full periodic exterior. The proof does not establish entry from arbitrary finite right rows, and does not prove Problem1. Natural-time, all-column, all-time common period21 is the formal input; the stronger varying-onset statement remains outside these Lean sources.
