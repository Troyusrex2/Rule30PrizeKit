# Uniform physical mismatch residence — worker PASS

Frozen source `Rule30PhysicalDefectEpisodeResearch.lean`, SHA256 `e7f9b792bc8b8db49725417cc309d60ffbde8832a8d8252e7292ea5ca1adb0d2`.

Full unchanged-checker replay passed **23 module-owned constants and four headline types**, with no new axioms and zero source warnings. This is a worker result; independent root replay is not claimed here.

The exact new headline is:

    P>0;
    the actual single-seed center has period P from T;
    t≥T+2P;
    therefore there exists j≤2P with
      mismatch (2P) (t+j)=false.

Here `mismatch Q s` is literally `cell s 1 XOR cell (s-Q) 1`, imported from the frozen physical defect-budget source. Thus Q=2P is chosen once, and the forbidden episode includes **all Q+1 readings at both endpoints**. This bounds each uninterrupted mismatch episode by Q readings. It supplies no estimate of how often episodes begin and does not prove Problem 1.

The proof first shows that a mismatch alive before and after one update forces `r(t+1)=c(t) XOR r(t)`. Two identical P-blocks of center bits then cancel over 2P updates. If the mismatch survived all Q+1 readings, this would make `r(t+Q)=r(t)`, contradicting the mismatch at the final reading. This last equality uses the exact time-shift relation between the two compared streams; two independent histories would not suffice. Neither a period for the right column nor a whole-state return, common column-two reset, or moving-coordinate correspondence is assumed.

The other headlines are `live_mismatch_step`, the finite XOR-block cancellation lemma `xor_two_blocks`, and the exact physical `true_birth_iff`: a transition from mismatch false to true occurs exactly when both compared column-one bits are false and the compared column-two bits differ. This pins down the remaining frequency target without claiming it is sparse.

The associated paper is `../physical-defect-upper-audit-20261027T0130/PAPER.md`, SHA256 `0132c9c729356a943ddc109106b5e2137de05cc208c4d431b06b537a8813eb4a`. Its signed Duhamel expansion, left-column identities, and episode-count estimate remain paper arguments, not headline claims of this module. In the paper estimate every interval of length at most Q has at most the fixed H_Q white phases; equality is asserted only for a complete period. The original weighted-charge sources and their 94-constant delivery remain unchanged.

Dependencies: exact frozen `Rule30PhysicalDefectBudgetResearch` SHA `0ce4c056a39b761d297e4a51468e32d8deb7baf662507c6297cf477e1e2f506f`, then official `Rule30MaskedJen → Rule30Prize → Rule30Jen`. The dependency source/object hashes are in `inputs.json`; a copy of the unchanged core source accompanies this delivery. All compiled dependencies were hash-checked, and the fresh module used a private library. Original compiled pin is `5473ffd075f63c9d626e63b8455805d4831b39ca`; the official closure has already been byte-checked at audited pin `7d665044b904117af9e82328aeb90a30692b2b85` in the prior sealed delivery. No reference files or catalog worktrees were changed.

Final evidence: `formal/attempt02/report.json`, `types.log`, `build.log`, and `evidence/replay-attempt02.guard.json`. Unchanged checker SHA256 is `b882f2527a1d6e720828a0c729cc80c3977905ed9207d09af22f8d153a073905`. Guard: 2.184 seconds, 778,919,936 bytes peak owned RSS, 44,614,279,168 bytes minimum available memory; limits 300 seconds / 8 GiB / minimum 2 GiB. All jobs are terminal.

Attempt01 is preserved. It exposed an incorrectly parsed local Bool helper target: `r || z=r` needed parentheses around `r || z`; its use failed, and the corrected exact equality is what was checked. A final XOR cancellation was also made explicit. No premise was added to the intended theorem to repair either issue. No other build attempts or searches occurred.

For a fresh replay, use a new owned phase and the recorded `replay.py` commands. Build the module against the exact core dependency, then invoke the unchanged checker with the four headline names in `inputs.json`. The runner checks the toolchain, checker, core source/object, and all three official dependencies and prints the final types. Do not modify or rerun this sealed delivery in place. No publication or submission was performed.
