# Cancellation and bounded mismatch episodes in physical time

This is a paper derivation for the actual official single-seed physical columns. It does not prove the subcritical defect-frequency budget or Problem 1. It supplies a new uniform residence bound that uses coherence of an actual time shift, rather than treating two histories as independent drivers.

Assume the center `c(t)=cell t 0` has period P>0 from T. Choose **once** Q=2P and start n0≥T+Q. Write r(t)=cell t 1, z(t)=cell t 2, and put bars over the same streams shifted by Q into the past. All shifted times below are in range. Let delta=r XOR rbar, M=1-c, and N_Q(X)=sum[n0≤t<X] M(t)delta(t).

## Exact signed Duhamel, with physical cancellation events

Use zero-one integer values. The already checked recurrence has a=1-z and b=(1-rbar)(z XOR zbar), hence exactly

    delta(t+1) = a(t)delta(t)+b(t)-2a(t)delta(t)b(t).

Define the integer signed injection beta=b-2a*delta*b. Iterating this ordinary integer identity gives

    delta(t) = delta(n0) product[n0≤s<t] a(s)
               + sum[n0≤u<t] beta(u) product[u<s<t] a(s).

Consequently the earlier CHARGE expression becomes an **equality** after replacing b by beta in its outer weighted injection sum. The same initial term and weights W(u;X) occur. The last possible source remains X-2. This statement is a paper algebra identity; the earlier Lean inequality remains sealed and unchanged.

The negative correction is not arbitrary: a*delta*b=1 exactly at

    r=1, z=0, rbar=0, zbar=1.

This is the oriented collision of parent pairs 10 and 01, whose OR outputs agree. Reversing the two histories makes the same death appear as a zero-persistence event instead of this negative term. Positive beta also need not mean a genuinely new mismatch: the old positive decomposition may erase and reinject a mismatch in one update.

A symmetric, cancellation-aware birth/death decomposition is cleaner. Define

    B = (1-r)(1-rbar)(z XOR zbar),
    D = r(1-rbar)zbar + (1-r)rbar*z.

Then, under the common center forcing,

    delta(t+1) = delta(t) + B(t) - D(t).

B is exactly a true transition delta=0 to delta'=1; D is exactly a true transition delta=1 to delta'=0. Their supports are disjoint. Thus a true birth requires BOTH compared right bits to be white and a defect in the next physical column. A mismatch does not consume a fresh source at every time it is read.

For signed orientation d=r-rbar, the exact identity is

    d(t+1) = (1-2c(t))*[(1-z(t))*d(t) + (1-rbar(t))*(z(t)-zbar(t))].

When delta(t)=delta(t+1)=1, the OR outputs are different and have the same orientation as r and rbar. Hence

    r(t+1)=c(t) XOR r(t),
    d(t+1)=(1-2c(t))*d(t).

These identities retain physical phase and the actual shifted predecessor; no equality with a finite-list kappa variable is asserted.

## Uniform residence lemma: no Q+1 consecutive mismatches

**Claim.** For every t≥T+Q there exists j≤Q such that delta(t+j)=0, where Q=2P is fixed above.

Suppose instead delta=1 at all Q+1 times t,t+1,...,t+Q. Each of the Q updates then has a live mismatch both before and after it, so the preceding identity forces r(s+1)=c(s) XOR r(s) at every s=t,...,t+Q-1. The Q=2P center bits come in identical P-separated pairs; their XOR is zero. It follows that r(t+Q)=r(t). But delta(t+Q)=r(t+Q) XOR r(t), because the second history is the literal Q-shift of the first. This contradicts delta(t+Q)=1.

This proof genuinely uses shift coherence in its final equality. A pair of independent histories with the same center forcing would not suffice. It also uses the parity of an entire fixed Q-period; using Q=P with an odd number of black center phases would not justify the cancellation.

Thus every actual uninterrupted mismatch episode after n0 has at most Q readings. This is stronger than the trivial observation that a periodic white mask has short white runs: the **unmasked** mismatch itself must disappear, so one episode cannot survive through arbitrarily many mask periods. A product of the earlier positive coefficients a may nevertheless survive much longer; in that representation signed injections must cancel it. No common z=zbar=1 reset is required for this conclusion.

## A real uniform count estimate, with the remaining frequency problem explicit

Let H_Q be the number of white center phases in one Q-period after T. Every interval of at most Q consecutive times after T contains at most H_Q white phases: extend it to exactly Q times, whose periodic phase multiset is fixed. This is an upper bound; shorter intervals need not have the same total.

Partition the mismatch support on [n0,X) into consecutive episodes. The initial episode, if delta(n0)=1, contributes at most H_Q masked readings. Every later episode starts immediately after a unique true birth B(u)=1 with n0≤u<X-1, and contributes at most H_Q readings, even if it extends beyond X. Therefore

    N_Q(X) ≤ H_Q * (delta(n0) + sum[n0≤u<X-1] B(u)).

This is a uniform multiplicity bound, with Q and H_Q fixed independently of X. It is obtained only after retaining the signed cancellations or equivalently using genuine births/deaths. Counting the raw b terms and their original positive survival weights can be much looser.

This does **not** supply a subcritical upper bound on the number of true births. For example, the sufficient open estimate

    sum B(u) ≤ C + floor(m/H_Q), at X=4^m*n0,

would give N_Q(X)≤H_Q(C+1)+m when H_Q>0. But no such birth-frequency estimate is established here. Births whose entire episode misses the white mask can be omitted; that refined visible-birth count is within fixed multiplicative/additive constants of N_Q, but identifying its sparse growth remains a genuine task.

## Physical left-column transport and a limitation of signed potentials

The official `cell_left` identity, with the center periodic at both t and t+1, gives the exact bit relation

    cell(t,-1) XOR cell(t-Q,-1) = M(t)*delta(t).

Thus N_Q counts actual Q-shift defects of physical column -1. It is not an observer of a moving coordinate.

There is also an exact local identity valid in any actual Rule 30 history:

    cell(t,-2) = cell(t+1,-1) XOR cell(t,-1)
                  XOR (c(t) AND c(t+1)).

To derive it, write l=cell(t,-1). The update of the center gives c(t)c(t+1)=c(t)(1-l); therefore l OR c = l XOR (c(t)c(t+1)), and the update of l gives the displayed equation. Since c(t)c(t+1) is Q-periodic, if h(t)=M(t)delta(t), then

    cell(t,-2) XOR cell(t-Q,-2) = h(t+1) XOR h(t).

This transports defects to temporal boundaries of their runs. It does not bound run counts or total white readings: replacing a positive count by its signed derivative can erase precisely the cost that needs to be controlled.

For example, the natural signed masked total telescopes automatically:

    sum[n0≤t<X] M(t)*(r(t)-r(t-Q))
      = sum[X-Q≤t<X] M(t)r(t) - sum[n0-Q≤t<n0] M(t)r(t).

Each boundary sum lies between zero and H_Q, so the absolute signed total is at most H_Q. This bounds only the difference between the two orientations of defects. Their **sum** is N_Q and can be large without violating that identity. A potential based solely on this signed boundary term therefore cannot provide the needed nonnegative defect budget without an additional control of cancellations or births.

The finite-white single-seed left boundary is what supplies the already proved doubling-window LOWER bound. Nothing in the new transport identities turns it into an upper bound on births. No nonnegative potential has yet been found that charges repeated births without reusing credit. The next specific open target is the frequency of the exact events r=rbar=0, z!=zbar, or a cancellation-aware budget for their visible episodes, at one fixed Q=2P over unbounded horizons.

No simulation of a hypothetical eventually periodic actual center was used, no free temporal strip was promoted to a genuine seed, and no width/clock census or horizon-dependent Q was used.
