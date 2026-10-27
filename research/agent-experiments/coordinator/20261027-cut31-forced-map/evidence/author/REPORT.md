# Actual cut-31 forced boundary: full kernel PASS

The new research leaf proves the four corrected cut-31 boundary formulas for **every window of the actual gate** `refinedGate r = u empty (155+r)`. It also proves the literal all-depth physical connection

    forcedTail (B refinedGate) (L refinedGate) n t
      = zrow (Psi empty) (t+311) (n+32).

There is no `Allowed17` hypothesis, finite-support premise, bi-infinite extension premise, supplied clock, or assumed reset closure. The complete forcing is retained: `B(t)=X(32,t)` and `L(t)=X(31,t) AND NOT X(32,t)`.

Final source: `Rule30Cut31ForcedMapResearch.lean`, SHA256 `40f5dee5473493137db9c25f10dd76e2051424321ea0c08fc52452ea1df846ca`.

## What closes the actual-entry and locality gaps

The previously verified `Rule30EmptyGateLanguageResearch.windowWord_allowed` gives every actual eight-bit window, starting at every natural r including zero, in the ten-word list `[8,9,16,18,33,36,66,72,132,144]`. This is stronger than the bare next-gap and no-successive-short-gap assertions. In particular, its initial window cannot begin with five white bits.

`actual_prefixes` proves overlap-extension coverage from these actual windows, and `cover_certificate` checks that the nine extensions are covered by the listed 26 seventeen-bit words. It does not enumerate all 131072 Boolean words or require an unproved embedding into a bi-infinite language. `actual_seventeen` has only the index r as a parameter.

`columns_sound` connects the packed inverse evaluator to the official scalar `recon`. A 33-time-bit boundary prefix is enough for both columns 31 and 32 at times 0 and 1; the final sampled gate index is 16. `local_certificate` checks the four formulas on the 26 allowed words using ordinary kernel `decide`. `encoded_boundary` and `encoded_recon` prove the locality transport to each actual index r.

`actual_history311` follows directly from official `Psi_free` and `Psi_inX`; `actual_reconstruction` uses official `recon_shift` and `history_eq_recon`. These equalities are unconditional on finite support. The generic `forced_tail_at` proves the all-depth tail reconstruction from both B and its mask L, and supplies the final actual identity.

## Exact formulas

All additions below are XOR and products are AND. Write `K_i=G(r+i)G(r+i+3)` with G the actual refined gate.

    B(2r)   = 1 + G(r+1) + K1 + K5 + K7 + K8 + K12
    B(2r+1) = 1 + K3 + K4 + K7 + K8 + K11 + K13 + K4*K12
    L(2r)   = K6 + K7 + K12
    L(2r+1) = K7 + K8 + K13 + K5*K13

The two quadratic corrections are retained. The finite evaluator establishes the formulas directly, not by trusting the prior Python residual classification.

## Validation and provenance

All execution occurred in a new owned remote worker directory. No local Lean/Wolfram, installation, authentication, public write, or old-archive edit occurred. The official checker is unchanged, SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`; the Lean 4.35 binary is also hash-checked. Current official pin is `7d665044b904117af9e82328aeb90a30692b2b85`.

The 18 imported modules from the earlier 0255 closure were reused after checking their source hashes against the saved source closure and their compiled hashes against prior receipts. Four are research dependencies; all fourteen official source bytes match the current-pin checkout. Object companions were copied with exact hashes recorded. Reused objects were checked again after the successful leaf run. This is not a cold build of those 18 modules or the entire catalog.

Two missing, unchanged dependencies were freshly built and fully replayed in attempt01:

- `DrivenEmptyCore`: 276 constants, 2 headlines, full PASS, 35.37 seconds including replay and printed types.
- `Rule30EmptyGateLanguageResearch`: 18 constants, 2 headlines, full PASS, 2.01 seconds including replay and printed types.

The final leaf in attempt03 passed full replay of **107 constants and all 6 headlines**, with no new axioms and zero source-build warnings. All six types and axiom lists were printed. The complete three-source fresh scope is therefore **401 constants and 10 headlines**, across separate successful receipts; the first attempt's leaf failed and is not counted as a pass. The unchanged checker's own replay-deprecation warning remains in its raw logs.

Final guard: 2.9713 seconds, peak owned RSS 803430400 bytes, minimum system available memory 44752662528 bytes, no guard stop. Limits remained 300 seconds / 8 GiB owned RSS / 2 GiB minimum free memory. Each attempt used a fresh preflight; no unrelated jobs were signaled.

Attempt01 preserved the original source and errors: three small rewrite/elaboration issues and heartbeat exhaustion from concretely unfolding the depth-32 tail helper. The two dependencies passed. Attempt02 generalized the cut index and fixed those issues, but failed on natural-addition normalization in the helper. Attempt03 changes only those normalizations and passes. The finite coverage and local certificate data are unchanged across attempts. All failure logs, exact source copies, and diffs are retained.

## Limits

This proves an exact new forced boundary class for the actual empty-driven trace. It proves neither closure under a second reset nor any positive support gain, upper charge bound, `CQ01Empty`, or prize problem. The same-history carrier shift is not treated as a waiting-time support reset. The optional five/six-pulse counting consequence remains paper-only and is not claimed among the six verified headlines.

The accompanying `INPUTS.json`, `SOURCE-CLOSURE.json`, and `build-order.json` identify every exact source and provide the complete fresh-replay order for an independent verifier. The root owns independent validation and any later publication.
