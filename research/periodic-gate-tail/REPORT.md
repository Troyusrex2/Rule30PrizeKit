# Unbounded gate pasts for the periodic gap-five future

## Exact new result

Let G5(r) be true exactly when r%5=0, and let oddTrace(G)(t) be true on odd times and NOT G(t/2) on even times. Use the official zero-wall reconstruction lam from Rule30ZeroBoundary. For ANY two n-bit pasts h,g prepended to G5, the reconstructed rows agree at every spatial depth k>=1+620*n. Both n and all past bits are quantified, with no bounded search premise. Past admissibility is unnecessary, so the statement includes all admissible pasts in this subclass.

The canonical theorem is Rule30PeriodicGateTail.arbitrary_gate_pasts_agree_from. The existential-tail version is arbitrary_gate_pasts_agree. gatePrepend constructs the finite past in reverse index order; because h and g range over all Boolean functions, this covers every same-length prefix. The shared infinite future is specifically G5. Arbitrary legal infinite futures remain open.

This is complementary to Rule30GatePastThree: that result fixes past length3 and allows an arbitrary legal future; this result permits every past length but fixes the periodic future. Neither theorem subsumes the other.

## Mechanism

The boundary word is the ten-bit periodic word1022 (all black except time0mod10), proved equal to oddTrace(G5). Sideways reconstruction has a 155-cell periodic spatial carrier from positive depth1. The profile recurrence is kernel-checked on all155 spatial residues and10 time residues, then lifted to all indices.

For every one of the ten phases, one155-cell driver block sends ALL four inverse input pairs to the same reference pair. Finite computation is checked by ordinary Lean decide and kernel replay, without native_decide or a solver. The generic spatial argument permits an arbitrary finite input prefix and an arbitrary offset. It aligns a complete carrier block beyond the prefix; the inverse reaches the preceding time phase within at most310 additional cells. Induction gives310 cells per arbitrary inverse head, or620 per gate bit (two inverse heads). All later agreement propagates by the official back recurrence.

The source also connects history operators to lam by official realization/uniqueness and proves the gate-prefix trace identity. No hand-waving identification of a backwards row with a prepended trace is needed.

## Validation and provenance

New module:125 replayed constants,15 headline types; no new axioms or proof-source warnings. Source SHA-256 948e1dd57d9f928a617abdbd23fe8290d3b2d5763d99f5adae6fb1a40ae0428b. Fresh nine-source Lake build and unchanged checker passed in attempt05. Exact official pin932cf8dde039b89b1dcbe9636867bb1b2057fef0; Check.lean SHA-256 b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905.

A further fresh twelve-source integration build compiled all four PR47 modules, replayed every owned constant in all four through the unchanged checker, checked452 constants/39 headline types in total, and passed a joint four-import smoke check. No proof objects were reused. The whole catalog was not rebuilt. The original three modules remain byte-for-byte unchanged (327 constants/24 headlines);125/15 is the new addition.

The carrier was discovered in an earlier sealed computation, copied as CARRIER-SOURCE.json here. Its SHA-256 is6f06437dcb3824dd4ed1ccc6ecc263fa2a36b434272bb02280776eed2e68d13a. The initial probe's displayed reference-end indices153,154 were wrong; the correct inverse end indices are154,155 (the latter wraps to0). Mapping ranks were unaffected. SYNC-RESULT-INITIAL.json retains the original observation; audit.py independently checked all1550 recurrence cells and40 input-pair maps at the correct indices before formalization. Current probe.py is corrected. The Lean certificate checks the correct endpoints directly.

An independent literal rule30 truth-table implementation checked190 finite inverse histories, forward boundary readings for20 ticks, and the five gate windows33,16,8,132,66, all in S. It confirms conventions and the310/620 bounds; the theorem itself quantifies all lengths. Python checks are labeled separately from Lean results.

## Limits and next experiment

This proves far-tail coalescence for a concrete eventually periodic-future subclass. It does NOT prove generic finite two-step predecessor existence, arbitrary-future tail equivalence, or a Prize problem. The base has a nonzero periodic spatial tail; finite-support equivalence in this subclass is not a useful substitute for the still-missing generic finite-row closure. No conclusion about the actual single-seed center column follows by itself.

Eventually periodic gap-five futures approximate many legal prefixes, but the convergence bound depends on the total prepended length. Density alone does not extend this proof to arbitrary infinite futures.

One pre-registered follow-up tested the next primitive legal gap cycle3,5, with a100000-state/5s cap. It returned after364 profile states:39 transient states followed by a325-cell cycle, with temporal period16. All16 phase blocks synchronize all four inverse input pairs. Independent literal checks confirmed5200 reference cells and64 maps. This is Python evidence only, NOT a second Lean-verified future. It is a focused Claude follow-up. The transient39 means the gap-five near-wall proof cannot simply be copied with constants replaced.

All research remains within the same original four-point grant (baseline4%, cutoff7%, ceiling8%), with no reset or paid model worker. No computer settings or real security configuration were changed. No Prize submission was made.
