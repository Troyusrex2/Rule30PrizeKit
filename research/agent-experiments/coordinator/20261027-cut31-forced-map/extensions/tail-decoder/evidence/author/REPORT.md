# Exact local tail decoder: full kernel PASS

The separate leaf `Rule30Cut31TailDecoderResearch.lean` proves two actual decoders, importing the unchanged frozen cut-31 map. Source SHA256: `2b563e10d29840681e3bb33b6780a69a693a753d683ed19db29dc82ffcb8f40b`.

Let G(r)=u empty(155+r), K(r)=G(r) AND G(r+3), and retain the exact physical cut-31 observations B,L from the preceding verified module. Define

    M(r) = L(2r) AND L(2r+2).

The proved identities, at every natural r, are

    M(r) = K(r+7),
    G(r+7) = NOT B(2r+12)
             XOR M(r) XOR M(r+4) XOR M(r+6)
             XOR M(r+7) XOR M(r+11).

The printed second headline uses the reverse equality orientation, with `gateRead` on the left. The statement is identical in content.

## Proof and exact scope

The marker identity uses the SAME 26 allowed seventeen-bit words as the frozen map. Its new small certificate checks

    lEven(w,0) AND lEven(w,1) = pulse(w,7).

The verified `actual_seventeen` theorem supplies actual window membership, including r=0. The short-marker separation intuition is therefore not an additional premise or an unproved language-to-trajectory bridge. No longer window, larger search, or new trajectory was used.

Substitution of the frozen four-formula theorem gives `actual_marker_decoder`. The even B formula at r+6 reads the five markers at r+7, r+11, r+13, r+14, r+18. Substitution of the marker decoder and a Boolean XOR cancellation lemma gives `actual_gate_tail_decoder`. This second proof is symbolic and introduces no new finite certificate domain.

These are all-time observations of the literal original gate. The inherited map already connects B and L to `zrow (Psi empty)` at time t+311. The decoder has no finite-support hypothesis, and neither theorem asks for an external clock or supplied marker sequence.

## What the decoder does and does not establish

It recovers the old gate tail after seven gate samples from the complete new interface. The relevant samples are one B bit at physical time 2r+12 and even L bits through 2r+24. Thus the new interface has not discarded this original gate information.

This does NOT establish that the class is closed under a second physical cut. Defining the image class of a boundary map gives no theorem about how further Rule 30 evolution or spatial cutting acts on it. The decoder is a nonlinear operation on temporal observations, not a proved physical restart map. No bound on the finite support of the row reconstructed from a decoded trace has been proved. In particular, neither a local temporal horizon nor the number 31 is automatically a support cost or spatial gain.

The complemented gate decoder can be written without a constant term. That may motivate a separately specified zero-preserving spacetime code, but no such code, boundary condition, or commutation with the Rule 30 update is established here. Those are genuinely additional obligations, not consequences of the two headline identities. No experiment testing them was run in this phase.

No class closure, support descent, periodicity conclusion, CQ01Empty, or prize conclusion is claimed.

## Validation

The first and only attempt passed the unchanged full checker: **9 constants, 2 headlines**, all headline types and axiom lists printed, no new axioms, zero source-build warnings. The checker's own replay-deprecation warning is preserved in the raw log.

Current official pin: `7d665044b904117af9e82328aeb90a30692b2b85`. Lean 4.35 binary SHA256: `ec7a472d1c12a09b0c0c718f7427c2be527b3f5f07810fdbe076c2507c7a91ea`. Unchanged checker SHA256: `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`.

All 21 existing dependency source copies and compiled objects were checked against the preceding frozen package's source hashes and successful object receipts. Only this new leaf was compiled/replayed; dependencies were not rebuilt. Object companions were copied with exact hashes recorded, and the copied dependency objects/companions were rechecked afterward. `SOURCE-CLOSURE.json` and `build-order.json` give the complete 22-source map for a separate fresh validation.

remote worker-only guard: 2.4226 seconds, peak owned RSS 789557248 bytes, minimum system available memory 44755075072 bytes, no stop. Limits remained 300 seconds, 8 GiB owned RSS, and 2 GiB minimum system available memory. Preflight found no live Lean/Lake jobs and 45609447424 bytes available. No local Lean/Wolfram, installation, account action, public write, or edit of the old sealed map occurred. All owned jobs are terminal.

The exact mathematical receipts and printed types are under `attempt01/Rule30Cut31TailDecoderResearch`. Private dispatch/guard commands are operational provenance, not intended public payload; a later public bundle should use a portable project and resource-only extracts.
