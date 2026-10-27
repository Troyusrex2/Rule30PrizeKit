The first-reset idea replaces the whole-prefix-return hypothesis with observation-period hypotheses in a local theorem. It does not resolve the spatial gate/plateau obstruction. A separate small Lean leaf now proves the positive statement; the forced-reset/cover-defect analysis below is paper-only. No example separating these hypotheses on actual finite lists is claimed; their possible equivalence is part of the older observability gap.

Use the exact finite-list CA dynamics A=singleChange false false, C=singleChange true false, T=C after A. Lists are older-first. For a finite list u, R_u(t) is its last bit after T^t and S_u(t) is its last bit after the A half-scan. These are the two moving-diagonal observations of the actual finite-white word100u. They are not fixed physical-center observations.

For u nonempty and two appended bits g,h, the existing Gated premise is, for every macrotime t,

    R_child(t)=1+g_t,    S_child(t)=1,

where g_t is the actual penultimate bit of T^t(u++[g,h]). Define f=R_u and chi=R_u+S_u. The literal two-step identity gives

    g_(t+1) = (1+chi_t)g_t + chi_t(1+f_t).          (1)

This is a reset latch: hold when chi=0 and reset to1+f when chi=1. The equality is derived from actual list scans, not assumed from a scalar analogy. In physical right-diagonal coordinates, chi is the OR of the two immediate predecessors of f at EVEN full times.

The new precise theorem is:

    For every finite u!=[], g,h and P>0,
    Gated(u,g,h) and Period(R_u,P) and Period(S_u,P)
    imply Period(R_child,P) and Period(S_child,P).

No whole-u P-return is supplied. P need not be least, even, or dyadic. The conclusion is a period of the two observations only; it does not assert a whole-child P-return. This weakens the input of the older gated_return result while correspondingly weakening its output.

Proof of the clock step: f and chi are P-periodic. If chi has a black value, move it to a residue R<P using the known DRIVER period. The reset at R and R+P makes g(R+1)=g(R+1+P), and forward induction gives P-periodicity from timeP. If chi is identically zero, equation(1) makes g constant instead. Thus no reset-witness premise is needed. For an actual finite word, an existing universal pure period M>0 is available from the actual finite-word evolution. Shift any time far enough by multiples of M to pull the eventual P-periodicity back to time0. This uses neither a supplied P-clock for g nor a least-period claim. Finally the two gates give the claimed periods of R_child and S_child.

The standalone formal leaf is `../gated-observation-reset-formal-20261027T0100/Rule30GatedObservationResetResearch.lean`, source SHA256 `a73205ebbe1316d2a16fd6716cf077245fbe33b206221ea4088df57562880258`. The unchanged official checker fully replayed24 own-module constants and four headlines, with no new axioms. Its exact actual-list headline is `gated_observation_period`; `gated_latch` proves(1). This is local worker verification, not a public backend submission or official catalog incorporation.

The left recurrence itself cannot be transferred across frames. In the literal right recurrence

    D(n)=n XOR((n>>1) OR(n>>2)),

an appended bit obeys x'=x+(older OR). Both initial bit choices remain complements forever. The genuine finite-white seeds2 and3, behind the fixed black parent1, form the two phases2,3,2,... . The driver is constant with period1 and black at every time, yet the child bit has period2. The reset in(1) is produced by the all-time gate constraint; it is not an intrinsic noninvertibility of the right-diagonal dynamics.

The exact connection to the missing phase condition is more revealing. In any actual right-diagonal history write the first five columns a,b,c,d,e, let E(t)=1 at even times, and suppose q=b+E is isolated: q(t)q(t+1)=0. Actual b gives Delta q=(1+c)(1+d), so q=1 forces c=d=0 and bc=Ec. Set

    aHat=1+Eb,    K=(1+E)d(1+c).

The already established cover-defect identity is

    Delta aHat+(b OR c)=K.

At macrotime s, put g=b(2s), f=c(2s), chi=d(2s) OR e(2s), and kappa=K(2s+1). Summing the defect identity at2s and2s+1 and using the literal two-step equation for a yields the exact forced latch

    g_(s+1)=(1+chi_s)g_s+chi_s(1+f_s)+kappa_s.     (2)

Thus periodic drivers can synchronize g even when kappa is nonzero. The gate-compatible latch(1) requires the full odd-cover defect to vanish. Synchronization alone gives no reason for that vanishing.

The previously named actual older word16 makes this obstruction concrete. Its genuine extension33 has an isolated marker, and its twice-extension66 has the prescribed initial head. Literal scalar evolution gives packed full-time profiles c=180, d=204, q=2, K=8 over eight ticks. The four macro profiles are g=15, f=6, chi=10, kappa=2. Equation(2) holds, while deleting kappa fails at macrotime1. The older word and its first extension return after8, but D^8(66)=67 and D^16(66)=66. K first becomes nonzero at time3; it is a transition residual, not the instantaneous gate failure. The head error starts at4, and the first literal odd-head gate fails at5. The original auxiliary timing assertion and its correction are preserved in ATTEMPT01.md. A separate phase-specific assertion on the reused torus was corrected in ATTEMPT02.md; neither correction changed the proposed identity.

The inherited boundary-free torus is a second scope control, not a new orbit discovery. Its head/neighbor/older profiles234,21,154,149,86,... give macro g=7, f=4, chi=15, kappa=0. It resets at EVERY macrotime and satisfies the actual gates, yet its macro observation period is4 rather than2. The reset accurately inherits the older driver's period; it cannot halve that period. Finite-white ancestry remains indispensable for the unresolved global assertion.

The chi=0 case requires care. It occurs for a one-bit u: R_u=S_u is the first toggling CA bit, so the reset mask is zero. At greater lengths chi=0 would mean two predecessor macro streams are zero, not two all-time physical streams. The boundary pair00 in100 becomes11 on the A half-scan, already demonstrating why the full-time constant-column theorem cannot simply be applied. This audit does not establish or refute chi=0 for all larger u; no width census was run, and its exclusion is unnecessary for the proved transfer theorem. Under Gated, chi=0 makes the child macrohead constant. The anchored constant-output theorem excludes constant1 in both child channels, leaving R_child=0,S_child=1, the already known alternating-head branch with one-cell phase-shift peeling. That observation is not a proof of iterable gate transfer.

The inverse information problem is unchanged. Equation(1) and the gate relation f<=g determine the parent observation pair when the child transition is00,01,or10; on a child11 transition they allow parent pairs00,01,or11. This is a local ambiguity, not a claim that all three alternatives occur on genuine finite-white all-time gated histories. The first-reset theorem determines a child from known drivers. It does not recover hidden drivers on a plateau, give a gate on the shorter prefix, or show K=0 is impossible for every finite-white noncore prefix. Those remain the actual missing spatial assertions. No P1 conclusion follows.
