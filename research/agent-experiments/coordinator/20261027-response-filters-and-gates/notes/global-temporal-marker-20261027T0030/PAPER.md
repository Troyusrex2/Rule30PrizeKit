# Full cyclic coefficients, an actual mask counterexample, and the cover defect

Paper-only global temporal-algebra lane. No new computation, state/period
census, finite certificate, or Lean build. The stronger previously stated
candidate that omits odd cover is false even for genuine finite-white
ancestry. The full phase-covered gate-halving candidate remains open.

## Two polynomial representations and the exact multiplicity resource

Fix N=2^k and represent an N-periodic Boolean profile v in two ways:

    v(t)=sum_j v_j B_j(t),  B_j(t)=binomial(t,j) mod2;
    V(z)=sum_(t=0)^(N-1) v(t) z^t in F2[z]/((1+z)^N).

Here v_j=(1+U)^j v(0), with the marked phase retained. Ordinary multiplication
of V polynomials is NOT pointwise multiplication of profiles. The latter
is Hadamard multiplication of the temporal coefficients, or
B_i B_j=B_(i OR j) in the binomial representation.

The exact change of basis is

    sum_t B_j(t)z^t = z^j(1+z)^(N-1-j).                  (1)

This follows by truncating the binomial generating function, using
(1+z)^N=1+z^N. Therefore, for a nonzero profile,

    nu_(1+z)(V)=N-1-deg_B(v).                            (2)

Distinct highest binomial indices have distinct lowest powers of1+z, so
the lowest valuation term cannot cancel. Time shift multiplies V by the
unit z^(-1), preserving valuation. For a dyadic P dividing N,

    v(t+P)=v(t) iff nu(V)>=N-P.                          (3)

This is also immediate from (1+U)^P=1+U^P. These are complete cyclic
polynomial identities, not a top-few-coefficient approximation.

The generic product estimate is only

    nu(F Hadamard G) >= max(0,nu(F)+nu(G)-(N-1)),          (4)

with the zero product handled separately. Indeed i OR j<=i+j bounds
the binomial degree of a pointwise product by the sum of the factor
degrees. The actual example below ATTAINS (4), so genuine overlapping
ancestry does not by itself improve it to monotonicity of valuation.

## The pre-existing stronger candidate is false on an actual word

The sealed isolated-marker paper explicitly left two candidates open:
even zero-runs plus odd cover, and the stronger version omitting cover.
Here is an exact analytic counterexample to the latter, with no search.

Use the actual older-first word10000, equivalently the finite diagonal
integer n=16. Its first three older bits100/111 alternate under A. On the
remaining two bits the exact two-tick return is

    T(a,b)=(1+a,1+a+b).

This follows directly from A=singleChange false false and
C=singleChange true false, T=C after A, using the frozen canonical section
identity. Starting at00, its four macro phases are00,11,01,10. The A
interleave reads the two newest coordinates as a and b+a, respectively.
Thus the actual newest profile c and its immediate older profile d have
the following closed formulas on the eight physical times. Write
epsilon=t mod2, u=floor(t/2) mod2, v=floor(t/4) mod2:

    d=u=B2;
    c=v+u+epsilon*u=B4+B2+B3.                            (5)

These are genuine coupled profiles, not free drivers. They have packed
values c=180 and d=204. The entire word returns after eight ticks, and
D^2(16)=19 !=16. In fact its least whole period is eight, as is also
visible from the four distinct T phases and the100/111 prefix phase.

Its older OR mask is252. The white-pair mask is

    w=(1+c)(1+d)=(1+u)(1+v)
      =B0+B2+B4+B6.                                     (6)

It is one exactly at times0,1, so the OR mask has one cyclic zero-run of
length TWO. Every zero-run is even, despite the genuine whole period eight.
This disproves the stronger finite-white statement with odd cover removed.

The odd-cover condition d<=c fails at time3. Switching the parity phase
does not fix the example: it fails on the other parity at time6. Thus this
is not a counterexample to the phase-covered candidate. The odd-cover
conjunct is substantive and cannot be inferred from even zero-runs.

The word16 is the permanent-head-flip companion of the already named
seed17 control in the gate-peeling paper. The derivation here uses the
literal canonical two-bit counter, not a new orbit enumeration or a claim
that an unanchored temporal array is reachable.

## An actual sharp valuation drop and an extremal isolated marker

For N=8, the ordinary temporal polynomials of (5) factor as

    C(z)=z^2(1+z)^3(1+z+z^2);
    D(z)=z^2(1+z)^5.

The constant-one profile has polynomial J8=(1+z)^7, so their complements
have valuations3 and5 as well. Nevertheless their Hadamard product w
has polynomial

    W(z)=1+z,

of valuation1. This is the sharp value3+5-7 in (4). Hence neither a
minimum-parent-valuation rule nor an additive valuation gain is justified
even for actual adjacent finite-white columns satisfying the even-run
condition. This is stronger than a counterexample using arbitrary profile
polynomials, but it does not refute a resource retaining the full ordered
parent data and the odd cover.

The unique isolated marker integrating this nonconstant mask is

    q=epsilon(1+u)(1+v)=B1+B3+B5+B7,

the single marker at time1. It has the largest possible binomial degree7
and ordinary polynomial Q(z)=z, of valuation zero. Thus isolation alone
does not create a high-multiplicity or low-degree constraint, even in this
actual anchored construction.

The inherited unanchored gated torus has white-pair mask96, equal to this
mask3 shifted by three temporal ticks. Thus its entire mask polynomial,
up to the prescribed cyclic shift, already occurs in genuine finite-white
ancestry. Ordered-parent and phase-cover information must be retained;
the mask by itself does not determine it.

## A positive full-profile identity: the odd-cover defect is the birth driver

There is a uniform implication retaining the complete cyclic data.
Let an actual older whole prefix return after an EVEN length L. Let c,d
be its two newest profiles. Assume its white-pair mask w=(1+c)(1+d)
admits an L-periodic isolated marker q with

    q(t+1)+q(t)=w(t).

The even-run criterion supplies such q, including the separately handled
constant-mask cases. Set E=even indicator and O=1+E=odd indicator. Then

    b=q+E

is a GENUINE appended column: its derivative is1+w=c OR d. Choose its
initial bit accordingly. It returns after L along with the older prefix.
Since q is isolated, q=1 implies c=d=0. Hence bc=Ec.

The head prescribed by the alternating gates would be

    aHat=1+E*b.

Its exact residual in the literal next-column recurrence is

    (1+U)aHat + (b OR c) = K,
    K=O*d*(1+c).                                         (7)

Proof: b'=b+(c OR d), so
(1+U)aHat=b+(1+E)(c OR d). Adding b OR c and substituting bc=Ec
leaves exactly(1+E)d(1+c). This uses all actual overlapping profiles.

Let a be the actual appended head with a(0)=aHat(0). Its error e=a+aHat
therefore satisfies

    e(0)=0;    (1+U)e=K.                                 (8)

Consequently:

* the prescribed all-time gates hold exactly when K is identically zero;
* the whole twice-extended word returns after L exactly when
  sum_(t<L) K(t)=0 in F2;
* if that sum is one, the whole twice-extended word returns after2L and
  fails to return after L.

The second and third statements follow by summing the actual head
increment: aHat and every older coordinate already return after L.
They concern whole-word return, not a replacement by a newest-column
clock. If L is nonminimal, no unproved least-period identification is made.

For dyadic L, the sum is exactly K_(L-1), its highest binomial coefficient.
The full profile K remains essential: a zero top coefficient gives return
compatibility but does not imply that every gate holds. The spatial
closure of K=0 is the unresolved part.

In the actual example above, the genuine appended b is

    b=1+B3+B5+B7,

with profile87 and initial bit one. The prescribed aHat is epsilon, but

    K=epsilon*d*(1+c)=B3+B7,

which is a single violation at time3. Its top coefficient is one. Thus
the actual additional head must double the whole return from eight to
sixteen. In integer coordinates the older word is16, the first extension
is33, and the twice-extended initial word with a(0)=aHat(0)=0 is66.
Equation(8) gives D^8(66)=67 and D^16(66)=66 without enumerating its orbit.

This is a positive boundary-to-head consequence of the full odd-cover
defect, but not a proof that every noncore actual prefix has nonzero K.

## What remains open and how this differs from earlier charges

The root task asked whether global valuation or full coefficient data can
exclude the oldest anti-periodic defect under the isolated-marker and
odd-cover conditions. The sharp actual product example rules out the
most direct monotonicity shortcut. Formula(7) identifies the precise
remaining object: the full marked profile K=O*d*(1+c), not merely the
valuation of w or its top coefficients.

A useful next boundary assertion would show that a genuine finite-white
noncore prefix whose mask admits an isolated marker cannot have K=0.
Here noncore means that the WHOLE prefix fails to return after two ticks;
no individual-column or canonical-DFA notion is substituted for it.
That assertion is not proved here. Claiming merely that K has odd weight
would be stronger still and would require a least-clock convention;
doubling a supplied period makes every full-cycle parity vanish.

The earlier ZeroRunSpatialChargeReductionResearch concerns counts in the
official Theta sideways reconstruction and states an unproved spatial
inequality. Its unrestricted extension has a separate counterexample.
CriticalChargeOneCoreResearch concerns a coupled Psi/free-stream counting
inequality and an ether construction. Neither is being reused as a theorem
about the present finite-white diagonal masks. The oriented-height papers
already connect safety with signed white-pair height; no new claim of that
equivalence is made here. This lane instead retains the whole cyclic
coefficient array and the exact missing phase-cover residual.

No unbounded gate-halving, reader theorem, physical-center bridge, or
Prize P1 conclusion follows. No frozen source was edited and no build
was launched for these paper results.
