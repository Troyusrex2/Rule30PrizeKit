# Exact statements and proof audit

All spatial indices are depths away from the white wall. The official rule is

    F(L)(k)=L(k+1) XOR (L(k) OR L(k-1)), k>=1; F(L)(0)=0.
    back(b,y)(0)=0; back(b,y)(1)=b;
    back(b,y)(k+2)=y(k+1) XOR(back(b,y)(k+1) OR back(b,y)(k)).

## First and second head coalescence

`OddGateWindow L` means there is an eight-bit word w in S such that the first eight odd readings are black and the first eight even readings are the complements of w's bits. The theorem `first_inverse_heads_agree` gives

    back(false,L)(k)=back(true,L)(k), k>=7.

`first_actual_preimage_iff_prescribed` identifies existence of an actual finitely supported, zero-wall P with F(P)=L with finiteness of `back(true,L)`.

For P=`back(true,L)`, its boundary begins with black and then follows L's history shifted by one tick. The same local condition gives an even-black boundary window for P. `second_inverse_heads_agree` proves

    back(false,P)(k)=back(true,P)(k), k>=11.

These statements hold for arbitrary, possibly infinite rows. They follow from the official `history_eq_recon` and `recon_local`: a finite boundary history determines a finite spatial prefix. Ten explicit gate cases give equal adjacent inverse cells. The inverse recurrence propagates that pair equality for every larger depth. Tail equality gives finiteness equivalence directly, without a bound on the row width.

## Four two-step histories

`AdmissibleHistory20 L` requires a word w<1024, all three overlapping eight-bit windows of w in S, and the first twenty actual boundary readings equal the odd-black/complementary-w pattern. This is a local consequence of the full gate hypothesis.

The twelve `HistoryCertificate` entries contain finite triangular reconstruction tables, two first-preimage prefixes, and four second-preimage prefixes. `history_certificates_valid` checks each local recurrence through the Lean kernel. The general `triangle_sound` proof identifies each certified cell with the official `recon`; `back_valid_sound` identifies the certified inverse prefixes with official `back`. Python's generator is not a trusted premise.

`gate_prefix_coverage` checks all 1024 ten-bit words and proves the certificate list is exactly the legal-prefix list. The general continuation proof first synchronizes the parent rows after depth 7, then synchronizes all four child pairs at depths 20 and 21. Since the parent targets agree thereafter, the actual inverse recurrence gives equality of every later child cell.

`all_two_step_heads_agree` and `two_step_finiteness_independent` use the equivalent enumerated local predicate `LegalHistory20`; `admissible_history_legal` connects the three-window encoding to it. The actual-predecessor headline has no assumed branch choice:

    (there exists a finite zero-wall Q with F^2(Q)=L)
      iff back(true,back(true,L)) is finite.

Its name is `any_actual_two_step_preimage_iff_canonical`. The representation of every actual preimage uses official `eq_back` and the semiflow, not a sampled inverse algorithm.

Neither direction asserts that the left-hand side is true. The outstanding mathematical task is finite-predecessor existence under the **full future** gate constraints. Once that existence is proved, head compatibility no longer requires an additional finiteness argument.

## Actual predecessors with a different wall bit

`wallBack` permits both initial inverse bits to vary: the wall value at depth0 and the head at depth1. `wall_merge_certificate` checks all four choices against each certified local gate history. The recurrence then proves `wall_and_head_agree`: every choice agrees with the prescribed white-wall, head-1 inverse for all depths >=12.

`actual_image_representation` identifies every row satisfying the ordinary local predecessor equations with its corresponding `wallBack`, without assuming that its wall was white. `finite_actual_image_transfer` therefore transfers an arbitrary actual finite predecessor to the canonical white-wall inverse under the local gate condition. The concrete `single_seed_left_inverse_finite` theorem supplies that finite predecessor from the actual single-seed row one age earlier, using the official edge-support theorem and the literal Rule30 recurrence.

This settles the first-inverse finiteness issue for actual positive-age left rows under the stated local gate hypothesis. It does not prove generic finite-row closure: an arbitrary finite class row need not already have a finite predecessor, and a newly chosen inverse need not itself be an actual single-seed row. Actual ancestry provides a finite onset reserve rather than an indefinitely repeatable descent.

## Run criterion

`Rule30InverseRunsResearch` quotients an inverse pair into three states: A=00, B=01 or 11, C=10. Reading zero gives A->A, B->B, C->B; reading one gives the cycle A->B->C->A. The initial head-1 state is B. The official finite-preimage criterion gives finiteness iff the scan ends in A, for every finite support bound.

A positive white gap normalizes B and C to B without changing acceptance. Thus a black run's length modulo three gives the exact flag update. `finite_inverse_run_blocks` states this for a supplied exact list of black/white blocks; it does not conceal an all-time condition or claim a general temporal invariant.

## Editing three gate bits against an arbitrary future

The separate `Rule30GatePastThreeResearch` module fixes a common gate future G and two admissible three-bit pasts p,q. The function `history` prepends six inverse heads, alternating a forced black head with the complement of the next gate-past bit. `history_gate_prefix` proves this is exactly the official reconstruction of p::G or q::G, rather than leaving the temporal interpretation implicit.

The twelve future-prefix certificates carry all six intermediate inverse layers. A generic model-soundness induction identifies each layer with actual `back`. The certificate checks equal adjacent cells at depths20,21 in every layer, and `joint_tail` propagates the whole coupled state to every larger spatial depth. Comparing only the final layer would have been insufficient when its targets differ; the formal proof checks the complete coupled state.

`reconstructed_gate_prefix_edits_agree` and its finite-support equivalence quantify over an arbitrary infinite shared future whose first ten bits have the stated legal-window encoding. Only the first three bits are edited, and each three-bit past must make the straddling S-windows legal. No periodic-future premise is used. The extension to an unbounded edited past is not proved.

## Failed development attempts

The first coalescence compilation needed a corrected final list-membership case and updated core conditional lemma names. The next extension needed a core-compatible replacement for an unavailable tactic. The table certificate needed an explicit global decidability instance; two local-instance formulations failed elaboration/kernel compilation, and an anonymous finite-index inequality needed explicit coercion reduction. All these failed builds were rejected before the final successful replay. The final source has zero warnings and no new axioms.

The fresh public validation succeeded. Retrieving its resource receipt initially used a filename without the guard's trailing hyphen; the missing-file transfer failed after the build had passed. The correct existing receipt was then retrieved without rerunning or relabelling the build.
