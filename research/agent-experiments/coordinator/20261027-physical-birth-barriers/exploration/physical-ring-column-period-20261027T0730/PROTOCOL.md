# Exact physical ring control

Frozen before execution. Test a proposed strengthening of adjacent-pair
period rigidity: in a full Rule30 orbit periodic in time with least global
period K, does a nonconstant individual column of least period P force
K to divide 2P? P rather than 2P is recorded as a stronger target.

A ring of width n lifts exactly to a spatially n-periodic configuration
on all integer sites. The update here is the PHYSICAL rule
x'(i)=x(i-1) XOR (x(i) OR x(i+1)); no sheared coordinate is involved.
Complete functional-graph cycles, rather than long finite observations,
give all-time examples. These initial rows are spatially infinite, and
cannot be used as finite-seed counterexamples.

Search widths 1 through 16 once, stopping at the first counterexample to
K|2P or at 45 seconds. No adaptive larger-width retry is authorized by
this protocol. KMP computes exact least periods of the cyclic column
words. Any candidate gets direct cyclic-word checks and scalar local-rule
verification before being reported. Full-cycle seed closure is checked.

This small pure-Python search allocates at most 65536 visited flags and
one graph path per width; it does not use the native Lean/Wolfram heap.
A failure to find a counterexample is only a bounded negative result,
not proof of either general claim. This phase does not build Lean, alter
repositories, publish, or submit. If a useful counterexample exists, a
subsequent separately scoped symbolic/kernel proof would be required.
