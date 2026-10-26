# Exact signed event-height identity

Status: elementary algebraic proof; no Lean verification and no D3* proof.

Use older-first finite-white coordinates, but this local identity also holds
for arbitrary drivers obeying the recurrence. Let `X_i(t)` be 0 or 1 and set
`y_i(t)=1-X_i(t)`. Define

* `Z_(i-1)(t)=y_(i-2)(t)y_(i-1)(t)`, the pair00 immediately older than i;
* `E_i(t)=Z_(i-1)(t)y_i(t)`, the triple000 ending at i;
* `q_i(t)=(-1)^t(2y_i(t)-1)`, a sign in {-1,+1};
* `H_A(T)=sum_(0<=t<T) (-1)^t A(t)`, with H_A(0)=0.

The update toggles `y_i` unless `Z_(i-1)=1`. Therefore, over the integers,

    y_i(t)+y_i(t+1)-1 = 2E_i(t)-Z_(i-1)(t).

Multiplying by `-2(-1)^t` gives

    q_i(t+1)-q_i(t)
      = 2(-1)^t [Z_(i-1)(t)-2E_i(t)].

Consequently, for every T,

    H_Z(T)-2H_E(T) = [q_i(T)-q_i(0)]/2.

This is an exact marked-height relation. Its correction takes two adjacent
integer values: {0,-1} when q_i(0)=1, and {0,+1} when q_i(0)=-1.
For any even common temporal period P it implies

    sum_(t<P) (-1)^t Z_(i-1)(t)
      = 2 sum_(t<P) (-1)^t E_i(t).

If i is Safe then E_i is identically zero, hence H_Z takes at most two
adjacent values. Conversely, a periodic nonempty Z has alternating temporal
parities exactly when its cyclic signed cumulative height has oscillation
one and drift zero; this is the old odd-gap/scalar criterion, not new.
The mark q_i(0) is essential. The complementary unsafe child can have E_i=Z
and the same height oscillation one, so height alone cannot identify safety.

Candidate rejected by preserved controls: signed pair-height amplitude
cannot propagate monotonically through three unsafe columns. In the genuine
white word 10000001, common clock32, pair-height amplitudes at consecutive
positions are [0,0,16,8,1,4,6,3]; its E cardinalities are
[0,0,0,8,4,8,6,5]. The final amplitude decreases6 to3 with all relevant
events nonempty. Independent literal-orbit calculation is retained in the
adversarial worker's owned tree. A direct checker will accompany this note.

Nothing here supplies the missing finite-white ancestry implication.
