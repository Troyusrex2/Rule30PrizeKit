Paper-first reset/plateau audit. Owned phase only; no Lean build or external write planned.

Question: can the verified first-reset lemma for x'=l XOR(g OR x) close the right-diagonal gate/plateau gap? The literal right recurrence is D(n)=n XOR((n>>1) OR(n>>2)); its single-column update is a translation in its own bit, so the left-diagonal lemma cannot simply be reflected.

Exact candidate before controls: for an actual right-diagonal history, write the first columns a,b,c,d,e and E(t)=1 at even t. Assume q=b+E is isolated, q(t)q(t+1)=0. Define aHat=1+Eb and K=(1+E)d(1+c). At macrotime s put g=b(2s), f=c(2s), chi=d(2s) OR e(2s), kappa=K(2s+1). Then

    g(s+1)=(1+chi(s))*g(s)+chi(s)*(1+f(s))+kappa(s).

This is a reset latch WITH an older forcing term. For P>0, if f,chi,kappa are P-periodic from T and chi has a black value at some A>=T, the first-reset proof gives g P-periodic from T+P, without an output-clock premise. The unresolved gate condition is kappa=0, not synchronization alone.

Proof route: actual b gives Delta q=(1+c)(1+d). Isolation gives q=1 => c=d=0 and hence bc=Ec. Therefore Delta aHat+(b OR c)=K. Sum at two successive times; at even times aHat=1+b and the literal two-step equation for a gives the displayed forced-reset identity.

Only named small controls, no sweep: (1) n=2 and n=3, complementary genuine outputs behind the fixed black parent1, to falsify transferring an ordinary black-driver reset to the right recurrence; (2) known older word16, its actual extension33 and twice-extension66, for exactly16 literal ticks, checking q isolation, K, the forced-reset law, failure when kappa is deleted, and whole returns; (3) inherited boundary-free gated torus head234/neighbor21 with older154,149,86, to check that even a reset every macrotime does not force clock halving without finite ancestry. This third control is reused, not claimed new. No finite fit will be treated as a theorem.

Prior work consulted before the controls: forward-reset-onset-20261027T0045/PAPER.md and exact Lean source; gate-return-source-audit-20261027T0020/REPORT.md; gate-coefficient-audit-20261027T0020/PAPER.md; global-temporal-marker-20261027T0030/PAPER.md. Existing gated_return already proves equality of whole return sets for the old prefix and its gated two-cell extension; rederiving that is not a new result.
