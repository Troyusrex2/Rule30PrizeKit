# Independent audit of the full-profile cover defect

Reviewed global-temporal-marker-20261027T0030/PAPER.md in full. Outcome:
paper algebra and stated scope PASS. No Lean build, new orbit census,
source change, or claim of kernel verification. This audit uses exact
symbolic identities and the named word16 arithmetic only.

## Cyclic polynomial statements

For N=2^k and0<=j<N, the displayed generating identity for B_j is correct:
z^j(1+z)^(N-1-j). The unique largest nonzero binomial index supplies the
smallest(1+z) valuation, so nu(V)=N-1-deg_B(v). Time shift is multiplication
by the unit z^(-1) in the quotient. For dyadic P dividing N, the
annihilator condition for1+U^P is precisely nu(V)>=N-P. Interpret the zero
profile separately, or give it valuation infinity.

Pointwise multiplication is Hadamard multiplication of temporal profile
coefficients, not multiplication of the ordinary polynomials. The rule
B_i B_j=B_(i OR j) proves the stated lower bound
max(0,nu(F)+nu(G)-(N-1)). The source correctly keeps this distinction.

## Named genuine finite-white word16

The exact low-head D rows are

    16,28,19,30,17,29,18,31,16.

They follow by the literal operation n XOR((n>>1) OR(n>>2)); all eight
pre-return values are distinct. The newest and immediately older bit
profiles are respectively180 and204. Their OR is252, so their white-pair
mask is3: exactly the cyclic zero-run at times0,1. The whole period is8,
and D^2(16)=19. Odd cover d<=c fails at t3; the opposite parity has a
failure at t6. Thus the claimed stronger statement without cover is
refuted, while the phase-covered target is untouched.

Writing epsilon=B1,u=B2,v=B4 gives d=u and c=v+u+epsilon*u. Their white
mask is(1+u)(1+v)=B0+B2+B4+B6. The listed factorizations give valuations
3 and5 for the parents/complements and1 for their Hadamard product;
the lower bound is attained. The isolated marker is the single bit at
t1, q=B1+B3+B5+B7, of ordinary polynomial z and valuation zero.

The inherited mask96 equals U^3 applied to mask3 under Uv(t)=v(t+1).
This is a phase-shifted mask agreement, not an equality of ordered
parents or a finite-white realization of the entire inherited torus.

## Uniform K identity and whole-return consequence

Assume the complete older word has an even return L and its white-pair
mask w admits an L-periodic isolated q with Delta q=w. The constant-mask
cases are valid under even L: w=0 forces q=0, while w=1 permits either
alternating phase. Put E=even indicator and O=1+E.

For b=q+E, Delta b=w+1=c OR d, so b is an ACTUAL appended column after
choosing its initial bit. Isolation gives q=1 => c=d=0, hence bc=Ec.
With aHat=1+Eb,

    Delta aHat=b+O(c OR d),
    Delta aHat+(b OR c)=O*d*(1+c)=K.

This expansion is exact and retains the actual overlapping parents.
For the actual next column a initialized to aHat(0), e=a+aHat has
e(0)=0 and Delta e=K. Since aHat, b and the entire older word return at L,
the full twice-extended state returns at L iff the parity of K over L is
zero. Odd parity flips just the new head after L and returns after2L.
There is no assertion that a nonminimal supplied L is a least period.

All selected gates imply a=aHat: the odd gate fixes a=1, and the even
gate combined with the following odd gate forces a=1+b. Conversely
a=aHat yields the selected gates. Thus their all-time validity is
equivalent to K=0, not merely zero cycle parity. The paper states this
distinction correctly; a vanishing top binomial coefficient is not
silently promoted to pointwise cover.

For the named word16, b=1+B3+B5+B7 has profile87; aHat=epsilon; and
K=B3+B7 is a single bit at time3. Its cycle parity is one. The finite
initial extensions are33 and66, and the identity therefore implies
D^8(66)=67 and D^16(66)=66. These consequences are derived from the
proved-on-paper residual, not claimed as a separately replayed census.

No gap was found in these statements. The remaining assertion that a
noncore finite-white older word cannot have K=0 is explicitly unproved.
The audit supplies no gate-halving, reader, physical-center, or P1 claim.
