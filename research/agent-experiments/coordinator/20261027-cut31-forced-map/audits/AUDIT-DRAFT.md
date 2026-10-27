# Cut-31 draft source and scope review

The complete 9,375-byte draft at SHA256 `e64ac54ce99570a05a7c343bbd80280234583af8b2d2a3c3fcade1da89f60f31` passes mathematical/source-scope review. The exact bytes are preserved as `DRAFT-REVIEWED.lean`. The author file still had that hash at the final input readback. This review makes **no elaboration or kernel verdict**; final frozen bytes and printed types must be checked separately after the author's run.

The six dependency sources used for semantic inspection are hashed in `INPUTS.json`. This review follows their definitions and bridge statements; it does not rerun or independently recheck the large `DrivenEmptyCore` proof table. The earlier independent 26-word scalar audit is retained separately at hash `2eb3549e2c23122d276124cde4946d0d5f18dfb08dd80358b1fd91296a72808b`.

## Actual Nat gate and coverage

`refinedGate r` is exactly `u empty (155+r)`, where `u R s = drv altCol R (2*s+1) 1`. `DrivenEmptyCore.entry` is `wall (white 155)=true`; the imported `white_core` induction preserves that wall for all `155+r`. The imported `windowWord_allowed r` therefore gives the listed eight-bit words at **every natural index of refinedGate**, including zero. This is stronger than obtaining an eventual prefix condition from an abstract bi-infinite gap language.

The new `actual_eight` is an encoding conversion of that theorem. `rolling_word` identifies the last eight bits after appending one bit. The `actual_prefixes` induction retains the actual prefix and checks its new trailing eight-bit window, rather than assuming that a separately supplied abstract word is legal. `cover_certificate` covers `prefixes 9` by the explicit 26-element `allowed17`, and `actual_seventeen` derives actual membership for every `r`.

Consequently `cut31_actual (r : Nat)` has no `Allowed17`, eventual-onset, unknown-boundary, or supplied-language hypothesis. It states the conjunction of all four actual identities for `B refinedGate` and `L refinedGate` at times `2*r` and `2*r+1`. The ten eight-bit values and 26 seventeen-bit values match the previously audited language. Whether the proposed `by decide` terms elaborate and replay remains the author's formal-validation task.

## Scalar orientation and bounded encoding

The `columns a n` pair is `(X_n,X_(n+1))`; after 31 transitions it is `(X_31,X_32)`. The right shift reads temporal input at `t+1`. `columns_sound` proves equality with the official `recon` recurrence by bit extensionality and induction, so the packed computation is not an unexplained physical simulation.

The boundary packing has 33 physical bits. `encoded_boundary` explicitly proves the even/odd phase and division identities for the shift `2*r`. `encoded_recon` requires `k+t<=33` and invokes actual reconstruction locality. This covers all four uses: depths 31 and 32 at times 0 and 1, including the largest endpoint 32+1=33. No omitted encoded right tail is used outside its justified cone.

The formula definitions agree with the independent scalar audit. The odd corrections are precisely `pulse(r+4) && pulse(r+12)` for `B`, and `pulse(r+5) && pulse(r+13)` for `L`. The even equations are unchanged. `L` means the masked value `X_31 && !X_32`, not the full older column when `X_32` is black.

## Exact onset 311 and history bridge

The new `actual_history311` correctly matches the absolute phases. For local even time `t=2*r`, global time is `311+2*r=2*(155+r)+1`, where `Psi_free` gives the complement of `u empty (155+r)`. For local odd time `2*r+1`, global time is `2*(156+r)`, where `Psi_inX` gives a black head. These are exactly the imported `boundary`'s even and odd branches.

`actual_reconstruction` combines that column equality with `recon_shift` and `history_eq_recon`. Its scope is all natural depths and times:

```
X refinedGate k t = zrow (Psi empty) (t+311) k.
```

The time origin is not silently moved to 310 or 312. `Psi empty` is the reconstructed zero-boundary **left** start associated with the actual periodically driven empty **right** half. Its finite support is not assumed or proved here; this is not the actual single-seed center history.

## Full forced tail

The first new tail cell is defined as

`B(t+1) XOR B(t) XOR L(t)`.

This is exact because `B(t) OR X_31(t) = B(t) XOR (X_31(t) AND NOT B(t))`. The Boolean case proof in `forced_tail_exact` establishes that equality, and the two-column induction then gives the whole tail, for arbitrary `G`, not only legal gates. Combining with the actual history bridge gives

```
forcedTail (B refinedGate) (L refinedGate) n t
  = zrow (Psi empty) (t+311) (n+32).
```

Thus the draft retains the nonzero forcing and does not replace the cut boundary by an unforced white wall. It does not assert a second-reset class closure, support decrease, nonfiniteness of `Psi empty`, or a prize conclusion.

## Review disposition

No mathematical scope defect found. The only textual observation sent to the author was the harmless leading docstring typo `/-!+#`. The draft contains no `sorry`, new `axiom`, `unsafe`, native decision shortcut, executable IO/meta hook, or kernel-skip option. There was no reviewer build, trajectory, source edit, or public write. Later source hashes are not automatically covered by this draft review.
