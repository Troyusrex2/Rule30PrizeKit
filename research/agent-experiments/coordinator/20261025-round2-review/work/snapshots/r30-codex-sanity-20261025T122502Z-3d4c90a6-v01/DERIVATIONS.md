# R2-03 derivations: bounded descent and nonlinear dyadic minors

These are explicit mathematical arguments for review, not Lean-kernel results.
The finite computations accompanying them do not prove the open growth lemma.

## 1. No bounded score can satisfy the original guarded descent

Let c : N -> {0,1} be ANY infinite binary sequence. Fix a natural B and a
function R(T,P) in {0,...,B}, for all T>=0 and P>=1. The following condition
cannot hold universally:

    c(T+u)=c(T+P+u) for u=0,1,2
        implies R(T+2,P) < R(T,P).

Proof: put L=2(B+1)+1. Among the 2^L+1 length-L blocks starting at
0,...,2^L, two are equal. Write their starting positions as T and T+P,
with P>0. For j=0,...,B, the length-three subblocks starting at offsets 2j
agree, because 2B+2=L-1. Therefore

    R(T,P) > R(T+2,P) > ... > R(T+2(B+1),P).

This requires B+1 strict decreases in a natural number initially at most B,
a contradiction. The argument also works if the allowed starts begin at
any prescribed T0. Overlapping repeated blocks cause no problem.

For our original canonical Rule 30 pairs, let a_t=Phi^t(1), with

    Phi(a)=a XOR ((a<<1) OR (a<<2)),
    (a,b,h)=(a_T<<P, a_(T+P), T+P).

Phi commutes with a positive bit shift. After u further Phi steps, observing
the two evolved rows at bit h+u gives c(T+u) and c(T+P+u). Advancing both rows twice
replaces T by T+2 and h by h+2, leaving P fixed. All canonical pairs satisfy
the original S hypotheses: the first row is positive even; the second
retains bit0=1 and equal bits1/2; the highest black bits are 2T+P and 2T+2P.
The low-bit and top-bit assertions follow directly from Phi by induction.

Consequently this obstruction applies to a rank of ANY fixed d-by-d matrix
over ANY field, since its rank lies in 0,...,d. It also applies to any other
score with a uniform finite ordered range. It is not limited to ordered
products, a coefficient box, or sampled assignments.

It does NOT refute the first-round absolute integer off-diagonal score,
whose range was unbounded. It does not refute growing matrix dimensions,
non-monotone growth, or a descent condition requiring an entire infinite
agreement rather than the three-bit guard. The hypothesis matters.

An explicit B=2 witness occurs at T=1,P=25: the two center blocks of length
7 are both 1011100. Their guards at T=1,3,5 force three strict decreases.
The exact canonical integers and observations are in results.json.

## 2. Exact nonlinear block identity

Work in GF(2)[x]. At physical time t pack position p into exponent i=t-p:

    F_t(x) = sum_(i>=0) bit(a_t,i) x^i,
    L(x) = 1+x+x^2,
    A_t(x) = sum_(i>=0) bit(a_t,i) bit(a_t,i+1) x^i.

The seed is F_0=1, all unlisted cells are white, and deg F_t=2t.
Since u OR v = u+v+uv over GF(2),

    F_(t+1) = L F_t + x^2 A_t.                         (1)

Iterating gives the block version of the already catalogued Duhamel formula:

    F_(t+q) = L^q F_t + sum_(j=0)^(q-1) L^(q-1-j) x^2 A_(t+j).  (2)

The basic Duhamel decomposition is NOT claimed as new. The proposed use is
to remove its linear part exactly on separated binary scales.

Put q=P*2^k, P>=1, and assume 2^k>t. Frobenius gives
L^q=L(x^(2^k))^P. When taking coefficient x^(t+q) in L^q F_t,
only exponent P*2^k from L^q can meet support [0,2t] of F_t:
any different multiple differs by at least 2^k>t. Its multiplier is
[x^P]L^P=1. To see the latter, if P=2m, Frobenius reduces the middle
coefficient to that of L^m; if P=2m+1, only the middle x term in L times
L^(2m) contributes, again reducing to the coefficient of L^m. The base is 1.

Writing c(t)=[x^t]F_t, we obtain

    c(t+q)+c(t)
      = [x^(t+q)] sum_(j<q) L^(q-1-j) x^2 A_(t+j).     (3)

For q=2^k there is an especially concrete kernel. Since q-1-j is the
k-bit complement of j,

    L^(2^k-1-j) = product_(0<=b<k, bit(j,b)=0)
                          (1+x^(2^b)+x^(2^(b+1))).       (4)

Define K_k(j,e) to be coefficient x^e of this product, or zero for e<0.
The right side of (3) is the parity of actual adjacent-black source pairs:

    sum_(j<2^k) sum_(z>=0)
       K_k(j,t+2^k-2-z) bit(a_(t+j),z) bit(a_(t+j),z+1). (5)

Both the binary-carry kernel and the source pairs can cancel. Presence of
a source or a path is insufficient. At t=0,q=4 the contributions from
source times j=1 and j=3 are both one, so their total is zero.

## 3. A growing-dimension minor target and its exact prize implication

For n>=1, K>=0, T>=0 with 2^K>T+n-1 define the n-by-n GF(2) matrix

    M(T,n,K)[i,j] = c(T+i+2^(K+j)) + c(T+i),  0<=i,j<n.

Each entry is the explicit nonlinear source parity (5), with t=T+i and
k=K+j. No learned matrices or independently chosen words enter it.

The proposed sufficient lemma U is:

    for every r>=1 there exist n>=1,K>=0 such that
       2^K>n-1 and rank_GF(2)(M(0,n,K)) >= r.

U IS OPEN. The 12 finite matrices in this response do not establish it.
There is no proposed positive per-time rank drift.

Here is its exact implication to official Problem 1. Suppose c has eventual
period P>=1 after T0. In any M(0,n,K), rows with i>=T0 depend only on i mod P:
both c(i) and c(i+2^(K+j)) are in the periodic tail. Their row span has
dimension at most P. The at most T0 earlier rows add at most T0 dimensions.
Thus rank M <= T0+P for EVERY n,K, contradicting U at r=T0+P+1. This excludes
every onset and positive period, not merely CQ01 or powers-of-two periods.
The argument uses only the definition of eventual periodicity.

One more structural, but still OPEN, way to attack U is an odd-minor lemma:
for every r, choose admissible n,K and r distinct row and column indices for which the
determinant of (5) is one. After expanding the determinant, this asks for
an odd residual among GF(2) matchings of actual
adjacent-black insertion events and their binary-carry kernels. A pairing
argument must come from seed ancestry and exhibit the leftover term; saying
that some contributing events exist is invalid. No such all-r pairing or
pivot construction has been supplied here.

This is deliberately a sufficient condition, not a claimed new equivalent
of aperiodicity. The catalog already has unbounded Hankel-rank equivalents.
For the binary digit-parity sequence, all entries of this matrix are one
under its separation condition, hence rank one: digit complexity alone is
not the needed mechanism.

The relation to the recent public cut-rank work is also elementary. If
A_K[u,v]=c(u+2^K v), then M(0,n,K) consists of the first n rows of the
columns A_K[:,2^j]+A_K[:,0]. It is a column-combination submatrix of a large
enough cut matrix. Thus its rank cannot exceed that cut rank. Neither the
public RankMax reduction nor our source identity proves a rank lower bound
for the single seed. The public source was read, not kernel-replayed here,
and is not used as a proof premise.

## 4. Why the barriers and controls do not disappear

M has unbounded dimension and uses spacetime source pairs throughout actual
cones. It is not a signed additive prefix energy of a reader absorbing
after the 26-cell ether prefix. It is also not a lower-bounded score required
to decrease at every physical step. This explains the difference in
hypotheses; it does not imply that U is true.

The official 7-by-4 ether table obeys the local rule in all 28 cells. On
that periodic spatial quotient, 28 nonlinear source-time sums cancel at
every column, despite 6 to 14 nonzero time contributions per column. The
finite right-half witness 0x6b70, driven by the alternating boundary, also
produces the known alternating free stream in our finite control and gives
rank zero. It is not the single-seed orbit. We do not apply the finite-row
support argument in (3) to this driven half or to an infinite ether row.
Only their appropriate local identities and rank controls were tested.

Removing the OR product gives Rule 150, for which the nonlinear source is
zero and the seed center is constant one. The finite Rule 90 and Rule 210
controls have rank one here, not the seed Rule 30 ranks. This is a necessary
sanity check on the proposed mechanism, not a proof of its growth.
