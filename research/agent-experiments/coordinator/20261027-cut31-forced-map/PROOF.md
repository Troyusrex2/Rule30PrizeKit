# Proof organization and exact scope

The source uses the existing physical inverse recurrence

```
X0(t)=0, X1(t)=a(t),
X(k+2,t)=X(k+1,t+1) XOR (X(k+1,t) OR X(k,t)).
```

For `a = boundary G`, even boundary times are `NOT G(r)` and odd boundary times are black. This is the leftward physical reconstruction, not a fixed-width finite-word evolution.

The actual gate's checked eight-bit windows lie in `[8,9,16,18,33,36,66,72,132,144]` at every natural starting index. `actual_prefixes` extends these windows by one overlapping bit at a time. Nine extensions give length17. `cover_certificate`, proved by ordinary kernel `decide`, covers these extensions by the listed26 words. Thus `actual_seventeen` includes the first actual window and does not assume an artificial prehistory or a separately supplied language premise.

`columns_sound` connects the packed evaluator with `Rule30ZeroBoundary.recon`. A gate block of17 bits gives33 boundary bits. These determine columns31 and32 at both sampled physical times0 and1. `local_certificate` checks the four corrected formulas on all26 words using ordinary kernel `decide`. `encoded_boundary` and `encoded_recon` transport this certificate to arbitrary actual natural indices. No Python result is imported as an axiom or used as a trusted theorem.

The coordinate offset is exact: `G(r)=u empty(155+r)` is sampled at the white physical times `2*(155+r)+1=311+2r`. Official `Psi_free` supplies those values, and `Psi_inX` supplies the intervening black values. Therefore `actual_history311` identifies the full input boundary at `t+311`, and `actual_reconstruction` identifies every reconstructed column.

At the cut, `B=X32` and `L=X31 AND NOT X32`. Since `X31 OR B = B XOR L`, the first new interior column is `B(t+1) XOR B(t) XOR L(t)`. The later columns satisfy the original recurrence. `forced_tail_at` proves this generic fact at an arbitrary cut, and `actual_forced_tail` gives

```
forall n t,
forcedTail (B refinedGate) (L refinedGate) n t
  = zrow (Psi empty) (t+311) (n+32).
```

The index `n=0` is column32. The equality includes the full tail, not just its first observer bit. Finite support of `Psi empty` is neither assumed nor proved.

The two older certificate sources are unchanged. The new leaf contributes107 kernel-replayed constants and6 checked headlines; the three selected checker modules together contribute401 constants and10 headlines. Existing dependency compilations are distinguished from full checker replay in the receipts. The14 official source hashes match the stated pin; the7 research sources include the unchanged dependencies as well as the new leaf.

The paper-only five/six-position consequence is a noncancellation statement for the displayed forcing formula. It is not an upper bound on a consumed reserve, a bound on the number of forcing episodes, or a contradiction to finite support. The transformed boundary loses the old constant-parity form, and its forcing is nonzero. A support-compatible closed class or another finite-left compatibility argument remains open. `CQ01Empty` and Prize Problem1 remain open.
