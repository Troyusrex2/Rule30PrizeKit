# Independent source and type audit: response filters

PASS. I read the entire Rule30CAResponseFilterResearch.lean source, all three
printed headline types, the final checker receipt, and its guarded replay
recipe. This is an independent source/scope audit, not a second build.

Exact audited source SHA:
17e628266760bc5202ea06153456cfe6b716dc06de848e8adbea9ae2b20b0949.

The three headline types accurately state:

* response_constraints: for any common nonempty older prefix and any two
  appended initial pairs, the two cross-run XORs expose the complemented
  older outputs, masked by the constant difference of the two g bits;
* filtered_response: at every time, the order(n+1) response filters equal
  delta_g times D^n chi and delta_g times(D^n chi+D^(n+1)oldR);
* erases_pair_iff: the order(n+1) filter erases ALL appended initial pairs
  exactly when D^n chi and D^(n+1)oldR vanish at every time.

Here chi=oldR+oldS, the difference is XOR, and D=1+time shift. The parameter
n ranges over all natural numbers, so the filter order is positive. There
is no claim about order zero. The off-by-one convention matches the earlier
paper's order-j condition D^(j-1)chi=0 and D^j oldR=0.

The proof uses the already literal nonempty-prefix observation_ors interface.
Thus it genuinely broadens the earlier four-older-bit macro formula to any
nonempty prefix; it does not assume virtual values for missing coordinates.
No period, least-clock, finite-window, or whole-return premise is inserted.

The constant g-response is proved from the same actual prefix-driven giter.
This is essential to moving its difference through arbitrary filters. The
head initial-bit difference need not be zero; positive derivatives remove
that constant response. Both arbitrary initial pairs remain quantified.

The necessity direction of erases_pair_iff legitimately chooses the actual
intervention pair(g,h)=(false,false) and(g',h')=(true,false), so delta_g=1.
The sufficiency direction keeps every g,h,g',h' and applies the complete
response formula. Filtered XOR linearity and positive-order complement
invariance are explicitly proved, rather than assumed.

The theorem compares TWO initial configurations sharing one older prefix.
It does not say these response differences are obtainable from a single
observed orbit, does not prove spatial inheritance of the filter condition,
and does not establish observer injectivity or Prize P1. No correction is
needed to the source or its intended research scope.

The inspected final receipt reports full replay of35 constants and three
headlines at pin5473ffd075f63c9d626e63b8455805d4831b39ca, unchanged checker
b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905,
no new axioms, and guard completion without a stop. These are root-run
receipts; this audit does not relabel them as an independent fresh replay.
As usual for partial claims, printed type and source review establish the
scope; the checker's typeMatches field is not an external expected-theorem
comparison.
