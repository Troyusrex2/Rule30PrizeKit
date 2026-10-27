# Independent final cut-31 source, type and receipt audit

**PASS.** The final source `Rule30Cut31ForcedMapResearch.lean`, SHA256 `40f5dee5473493137db9c25f10dd76e2051424321ea0c08fc52452ea1df846ca`, preserves the reviewed actual-gate statements and exact forced-tail bridge. All ten printed headline types and their axiom lists were read. The saved full-checker receipts support the author's stated validation scope. This reviewer performed no Lean build or replay.

## Source change review

The earlier complete draft review covered SHA256 `e64ac54ce99570a05a7c343bbd80280234583af8b2d2a3c3fcade1da89f60f31`. The complete diff to the final source was inspected and saved. Changes are:

- Corrected the docstring heading and removed an unused simplifier argument.
- Normalized `1+t` versus `t+1`, used the current conditional-rewrite name, removed an already-consumed rewrite, and made the two boundary functions explicit in `recon_local`.
- Factored the Boolean masked-stencil identity and proved the forced-tail induction at an arbitrary cut `j`, avoiding concrete depth-32 reduction. The generic helper is stronger; specializing `j=31` gives exactly the prior `forced_tail_exact` statement.

The gate definitions, ten eight-bit words, 26 seventeen-bit words, four formula definitions, local certificate, age 311, and six headline statements are unchanged in mathematical scope. The final source contains no new axiom, `sorry`, unsafe/native proof shortcut, executable meta/IO hook, or kernel-skip option.

## Actual hypotheses and coordinates

The imported `windowWord_allowed` applies at every natural index of `refinedGate r = u empty (155+r)`. `actual_eight`, the overlap-extension induction, and the kernel-checked coverage certificate derive `actual_seventeen` for every `r`. The printed `cut31_actual` type has only `r : Nat` and concludes all four boundary identities. There is no supplied `Allowed17`, eventual-window, arbitrary-right-tail, or bi-infinite-extension premise.

The packed pair after 31 transitions is `(X_31,X_32)`, in the same physical leftward reconstruction orientation as the official `recon`. The encoded 33-bit boundary suffices for depths 31/32 at both times 0/1; the maximum required sum is 32+1=33. The two nonlinear odd corrections are retained, and both even formulas agree with the independently audited 26-word scalar table.

`actual_history311` and `actual_reconstruction` preserve absolute phase. Local even time `2r` corresponds to global odd time `2(155+r)+1`, so `Psi_free` supplies the complement of the actual right gate. Local odd time `2r+1` corresponds to global even time `2(156+r)`, where `Psi_inX` supplies black. The printed reconstruction type is unconditional for all `k,t : Nat`:

```
X refinedGate k t = zrow (Psi empty) (t+311) k.
```

Here `Psi empty` is the zero-boundary left start reconstructed from the right half driven by an alternating center. Its finite support is neither assumed nor proved. This is not the actual single-seed center history.

The boundary uses `B=X_32` and `L=X_31 AND NOT X_32`. The exact identity `B OR X_31 = B XOR L` justifies the first tail cell. The new `forced_tail_at` proves the subsequent reconstruction for arbitrary gate `G` and arbitrary cut index `j`, including `j=0`. Its specialization and the actual-history bridge give the printed final theorem for every `n,t : Nat`:

```
forcedTail (B refinedGate) (L refinedGate) n t
  = zrow (Psi empty) (t+311) (n+32).
```

Thus the nonzero forcing has not been silently dropped. No second-reset closure, finite-support descent, `CQ01Empty`, or prize result follows from these statements. The five/six nonzero-tick packet count remains a separate paper consequence, not one of the six formal headlines.

## Exact receipt review

The checker file matches the unchanged SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`; the recorded kit pin is `7d665044b904117af9e82328aeb90a30692b2b85`, Lean 4.35.0. For each of the following, the raw checker JSON agrees with its report, the copied source hash agrees with the reported source, and every headline is found as a theorem with accepted type/axioms:

| Module | Successful saved receipt | Replayed constants | Printed headlines |
|---|---|---:|---:|
| `Rule30Certificates.DrivenEmptyCore` | `attempt01` | 276 | 2 |
| `Rule30EmptyGateLanguageResearch` | `attempt01` | 18 | 2 |
| `Rule30Cut31ForcedMapResearch` | `attempt03` | 107 | 6 |

The total is **401 constants / 10 headlines across three successful module receipts**. Constants include internal/generated declarations owned by each module; this is not a count of handwritten theorems or transitive imported constants. The respective non-internal declared counts are 270, 12 and 64.

The six leaf headline types are `actual_seventeen`, `cut31_actual`, `actual_history311`, `actual_reconstruction`, `forced_tail_exact`, and `actual_forced_tail`. The dependency headlines are `good_all`, `entry`, `windowWord_allowed`, and `no_successive_short_gaps`. All ten printed axiom lists contain only `propext` and/or `Quot.sound`. All three source-build logs are empty; the unchanged checker has its existing replay-deprecation warning. No new axioms are reported.

The first two leaf attempts failed and are preserved. Attempt01's dependency passes remain valid, but the attempt as a whole failed on leaf rewrites/inference and concrete-recursion heartbeat exhaustion. Attempt02 failed on natural-addition normalization in the generic helper. Neither failed leaf was relabeled as a pass.

The final worker guard records exit 0, no guard stop, 2.971275 seconds, peak owned RSS 803,430,400 bytes, and minimum system available memory 44,752,662,528 bytes. Limits remained 300 seconds, 8 GiB owned memory, and 2 GiB minimum free memory.

## Reused closure and seal

Eighteen prior dependency modules were reused: fourteen official and four research modules. Their local source hashes were checked; all fourteen official source files match the current-pin checkout. Recorded compiled-object hashes agree between the input manifest and the executed runner's reuse records. The runner checks those objects before and after use; this reviewer did not independently rehash remote objects or rebuild them.

All **72 payload hashes** in the author seal `2365d1f65ac6a6d9b5dfc492e85d51f00eedd878d642021fdcbc9f3c7380fdde` were independently checked. The complete 21-source closure was checked against actual source import headers, and its supplied build order is acyclic and complete. This consists of fourteen official sources plus seven research sources: the eighteen reused modules and the three freshly checked modules above.

The author's `REPORT.md` hash is `c58313f03c6e6758a02e507edc0469641ce9494d803fae6277ccb9c129e3604f` and accurately states these limits. An independent root-owned fresh all-source Lake run is separate work and is **not covered by this review at sealing time**. No reviewer build, trajectory, public write, or source mutation occurred.
