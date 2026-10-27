# Parameterized event-map candidate, before tests

Use the same actual map D(n)=n XOR((n>>1) OR(n>>2)), finite n>=0,
positive even P, whole D^(2P)n=n, and selected even-OR/odd-head gates as
uniform-gate-halving-20261027T0010/PAPER.md. No period or gap is swept.

At a nontrivial even black-head event, the proved gap lemma gives
n=1+2^(4q)*m with q>=1 and m positive odd. Define

    Phi(m)=(4*m) XOR((2*m) OR m).

Exact parameterized candidate:

    D^t(n)=1 XOR 2^(4q-2t)*Phi^t(m), 0<=t<=2q.

This follows by the one-step shift identity and the permanent head XOR.
It predicts an exact even-event update for q>1:

    (q,m) -> (q-1,Phi^2(m)) after two D steps.

For q=1 the impact at time2 is 1 XOR Phi^2(m), which has low triple010.
The new task is a return relation after this impact, retaining the higher
tail and the branch e=1 OR(e=d=c=0). No claim is made that the return time
is bounded, that a fourth front bit is fixed, or that Phi shrinks support.

The inherited nonwhite torus has even black-head events only at phase6,
each with gap4, and therefore tests any proposed universal reinjection
decrease. It is an infinite-tail control, not a finite n counterexample.

No tests have been run in this phase. Any fixed scalar test will be named
in advance and will not search states, periods, widths, gaps, or returns.
No new Lean build, certificate, external write, or source modification.

Named control before execution: reuse only the inherited period-eight
profile torus, starting at its black-head phase6. Check its four macro rows
(times6,0,2,4 modulo8) against the symbolic four-bit register formula. The
predicted register path is1,10,10,14,1; it returns with gap4. This checks a
single already-known infinite-tail orbit, not a new event/return search.
