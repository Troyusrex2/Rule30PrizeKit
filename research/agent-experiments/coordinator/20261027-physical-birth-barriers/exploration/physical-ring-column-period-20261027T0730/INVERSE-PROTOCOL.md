# One independent temporal-graph test

The initial ring search completed widths1..16,125 cycles, in0.218seconds.
It found no counterexample to K dividing2P, but did find the already known
period4/spatial7 ether disproving the stronger K dividingP claim. The
source audit confirms that this ether is already kernel certified.

The next test is a different exact quantifier, not a larger ring scan:
for each temporal clock K=1..9 enumerate cycles of the backward pair map
T(a,b)=(U(a) XOR(a OR b),a), U(a)(t)=a(t+1 modK).
By the proved finite predecessor-chain characterization, these cycles
cover ALL spatial periods of globally K-periodic physical Rule30 rows.
Test whether a cycle's global least temporal period divides twice the
least period of each nonconstant column. A negative result is still only
bounded in K and is not a theorem for arbitrary periods.

Limits: K<=9,45seconds, no adaptive rerun. At most262144 graph states.
Stop on the first counterexample, independently checking all scalar
physical stencils around its complete spatial/temporal cycle. Preserve
exact cycle data so a positive result can be proved separately in Lean.
No native checker, Wolfram, public write, or submission in this test.
