# Independent gated-observation source audit — PASS

Reviewed source: `../gated-observation-reset-formal-20261027T0100/Rule30GatedObservationResetResearch.lean`, SHA256 `a73205ebbe1316d2a16fd6716cf077245fbe33b206221ea4088df57562880258`.

Reviewed paper: `../right-gate-reset-audit-20261027T0055/PAPER.md`, SHA256 `219201172d04edb30bd1ed239585e6c79b78eeb1a84e28976990adb4b9b2b03f`.

No semantic or quantifier defect found. This is an independent source/type/provenance review, not a second Lean execution. The worker's exact source-bound receipt records unchanged-checker PASS for 24 module-owned constants and four headline types, no new axioms. The reviewer verified that receipt and both sealed manifests; root remains responsible for independent replay/adoption.

## Exact result

For every nonempty finite older-first list `u`, appended bits `g,h`, and positive natural `P`, all-time `Gated u g h` and pure `P`-periods of `outR u` and `outS u` imply pure `P`-periods of both observations of `u ++ [g,h]`. No whole-`u` return at `P` occurs in the hypotheses, and no whole-child return at `P` occurs in the conclusion. The result needs neither an even, dyadic, nor least `P`. The copied elaborated types are in `REVIEWED-HEADLINE-TYPES.txt`.

`Gated` is the imported actual-list condition, at every macrotime: child `outR` equals the complement of the actual penultimate iterate `giter`, and child `outS` is true. It is not a finite certificate or an assumed abstract reset equation. The representation remains the genuine `100u` finite-white evolution with its two moving-diagonal observations; no fixed physical-center statement is added.

## Proof checks

1. `two_step_last` retains the nonempty-prefix hypothesis and derives the two-scan identity using explicit scan memories. Its snoc reduction includes the singleton case; it does not silently apply the longer-prefix macro formula at the boundary.
2. `gated_latch` derives the reset equation from actual `titer_append_two`, `T_append_two`, and the first gate at consecutive macrotimes. The second gate is used at the final observation transfer. There is no abstract ancestry assumption replacing the actual lists.
3. `latch_eventual` moves a true reset-mask value to its first-period residue using only the driver's supplied period. A reset at that residue and one period later gives equality that propagates forward. If the mask is identically false, the recurrence instead makes the latch constant. No reset-witness premise or exclusion of the zero-mask branch is hidden.
4. `latch_period` pulls eventual periodicity back using an independently available positive period `M` of the latch. The shift is `P*M`; neither `P | M` nor a supplied `P`-period of the latch is needed.
5. `outR_has_period` obtains that separate positive `M` from the proved universal pure finite-word period. Its use of `word0`, `iter_even_odd`, and `r_word0` preserves the actual boundary and the factor-of-two macrotime conversion. The final proof applies it to `u ++ [g]`, whose last observation is precisely `giter u g`. It does not insert a whole-older return at the target `P`.

The paper faithfully separates the checked positive theorem from its forced-latch/cover-defect discussion and controls, which are paper/Python evidence. The paper's zero-mask consequence (constant child macrohead, with the all-black pair excluded by the anchored constant-output theorem) is a valid additional source-level deduction, not a new checked headline of this leaf. The first-reset theorem does not establish gate inheritance, vanishing cover defect, an iterable spatial descent, whole-word reconstruction, or Prize Problem 1.

The input hypothesis is syntactically weaker than the older whole-return theorem, with a correspondingly weaker output. No actual finite-list example separating those inputs has been proved here; the paper correctly leaves that observability issue open.

## Provenance

`audit.py` independently checked all 43 files in the formal manifest and all 10 files in the paper manifest. It recursively parsed the exact source imports and obtained 10 research modules (including this leaf) and three official modules. Every research source hash matched. For all three official modules, raw Git source bytes at compiled reference `5473ffd075f63c9d626e63b8455805d4831b39ca` and current pin `7d665044b904117af9e82328aeb90a30692b2b85` matched each other and the declared hashes. No additional import was encountered. The larger dependency inventory includes unused modules; it is not the actual imported closure.

The worker receipt names unchanged checker SHA256 `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. Its successful guard records 2.184 seconds, 782,372,864 bytes peak owned RSS, and 44,706,009,088 bytes minimum available system memory, with the prescribed 300-second/8-GiB/2-GiB limits. These are authenticated-by-manifest worker records, not measurements from a new reviewer build. No Wolfram/backend evaluation or public submission is asserted.

The review did not modify author sources, sealed bundles, or any catalog worktree, and ran no new evolution experiment or Lean build.
