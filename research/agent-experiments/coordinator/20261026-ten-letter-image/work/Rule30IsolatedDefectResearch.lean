module
public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways

/-! A ten-letter actual-image obstruction found while testing the delayed
defect family against the round-three realizability question. The finite
case proof checks every local relation in Lean; no solver result is trusted.
The uniform corollary applies to infinite as well as finite right halves.
This does not settle P1, CQ01 or the canonical center observer. -/
@[expose] public section
namespace Rule30IsolatedDefectResearch
open Ruliology.CellularAutomata
open Rule30Jen Rule30PeriodTwoSideways Rule30PeriodTwoCoupled
open Rule30Ether (drv drv_col0)
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def word : List Bool := [true,false,true,false,true,true,true,false,true,false]

theorem no_profile (c : Nat → Nat → Bool)
    (hs : ∀ t p, c (t+1) (p+1)=rule (c t p) (c t (p+1)) (c t (p+2)))
    (hb : ∀ t, c t 0=decide (t%2=1))
    (hw : ∀ i, i<10 → c (2*i) 1= !(word.getD i false)) : False := by
  have v1 : c 0 0=false := by simpa using hb 0
  have v2 : c 1 0=true := by simpa using hb 1
  have v3 : c 2 0=false := by simpa using hb 2
  have v4 : c 3 0=true := by simpa using hb 3
  have v5 : c 4 0=false := by simpa using hb 4
  have v6 : c 5 0=true := by simpa using hb 5
  have v7 : c 6 0=false := by simpa using hb 6
  have v8 : c 7 0=true := by simpa using hb 7
  have v9 : c 8 0=false := by simpa using hb 8
  have v10 : c 9 0=true := by simpa using hb 9
  have v11 : c 10 0=false := by simpa using hb 10
  have v12 : c 11 0=true := by simpa using hb 11
  have v13 : c 12 0=false := by simpa using hb 12
  have v14 : c 13 0=true := by simpa using hb 13
  have v15 : c 14 0=false := by simpa using hb 14
  have v16 : c 15 0=true := by simpa using hb 15
  have v17 : c 16 0=false := by simpa using hb 16
  have v18 : c 17 0=true := by simpa using hb 17
  have v19 : c 18 0=false := by simpa using hb 18
  have v20 : c 0 1=false := by simpa [word] using hw 0 (by decide)
  have v21 : c 2 1=true := by simpa [word] using hw 1 (by decide)
  have v22 : c 4 1=false := by simpa [word] using hw 2 (by decide)
  have v23 : c 6 1=true := by simpa [word] using hw 3 (by decide)
  have v24 : c 8 1=false := by simpa [word] using hw 4 (by decide)
  have v25 : c 10 1=false := by simpa [word] using hw 5 (by decide)
  have v26 : c 12 1=false := by simpa [word] using hw 6 (by decide)
  have v27 : c 14 1=true := by simpa [word] using hw 7 (by decide)
  have v28 : c 16 1=false := by simpa [word] using hw 8 (by decide)
  have v29 : c 18 1=true := by simpa [word] using hw 9 (by decide)
  have v30 : c 1 1=false := by
    have he := hs 1 0
    rw [v21, v2] at he
    revert he
    cases c 1 1 <;> cases c 1 2 <;> decide +kernel
  have v31 : c 1 2=false := by
    have he := hs 1 0
    rw [v21, v2] at he
    revert he
    cases c 1 1 <;> cases c 1 2 <;> decide +kernel
  have v32 : c 3 1=true := by
    have he := hs 2 0
    rw [v3, v21] at he
    revert he
    cases c 3 1 <;> cases c 2 2 <;> decide +kernel
  have v33 : c 5 1=false := by
    have he := hs 5 0
    rw [v23, v6] at he
    revert he
    cases c 5 1 <;> cases c 5 2 <;> decide +kernel
  have v34 : c 5 2=false := by
    have he := hs 5 0
    rw [v23, v6] at he
    revert he
    cases c 5 1 <;> cases c 5 2 <;> decide +kernel
  have v35 : c 7 1=true := by
    have he := hs 6 0
    rw [v7, v23] at he
    revert he
    cases c 7 1 <;> cases c 6 2 <;> decide +kernel
  have v36 : c 13 1=false := by
    have he := hs 13 0
    rw [v27, v14] at he
    revert he
    cases c 13 1 <;> cases c 13 2 <;> decide +kernel
  have v37 : c 13 2=false := by
    have he := hs 13 0
    rw [v27, v14] at he
    revert he
    cases c 13 1 <;> cases c 13 2 <;> decide +kernel
  have v38 : c 15 1=true := by
    have he := hs 14 0
    rw [v15, v27] at he
    revert he
    cases c 15 1 <;> cases c 14 2 <;> decide +kernel
  have v39 : c 17 1=false := by
    have he := hs 17 0
    rw [v29, v18] at he
    revert he
    cases c 17 1 <;> cases c 17 2 <;> decide +kernel
  have v40 : c 17 2=false := by
    have he := hs 17 0
    rw [v29, v18] at he
    revert he
    cases c 17 1 <;> cases c 17 2 <;> decide +kernel
  have v41 : c 0 2=false := by
    have he := hs 0 0
    rw [v30, v1, v20] at he
    revert he
    cases c 0 2 <;> decide +kernel
  have v42 : c 0 3=false := by
    have he := hs 0 1
    rw [v31, v20, v41] at he
    revert he
    cases c 0 3 <;> decide +kernel
  have v43 : c 4 2=false := by
    have he := hs 4 0
    rw [v33, v5, v22] at he
    revert he
    cases c 4 2 <;> decide +kernel
  have v44 : c 4 3=false := by
    have he := hs 4 1
    rw [v34, v22, v43] at he
    revert he
    cases c 4 3 <;> decide +kernel
  have v45 : c 12 2=false := by
    have he := hs 12 0
    rw [v36, v13, v26] at he
    revert he
    cases c 12 2 <;> decide +kernel
  have v46 : c 12 3=false := by
    have he := hs 12 1
    rw [v37, v26, v45] at he
    revert he
    cases c 12 3 <;> decide +kernel
  have v47 : c 16 2=false := by
    have he := hs 16 0
    rw [v39, v17, v28] at he
    revert he
    cases c 16 2 <;> decide +kernel
  have v48 : c 16 3=false := by
    have he := hs 16 1
    rw [v40, v28, v47] at he
    revert he
    cases c 16 3 <;> decide +kernel
  cases v49 : c 1 3 with
  | false =>
    have v50 : c 0 4=false := by
      have he := hs 0 2
      rw [v49, v41, v42] at he
      revert he
      cases c 0 4 <;> decide +kernel
    have v51 : c 2 2=false := by
      have he := hs 1 1
      rw [v30, v31, v49] at he
      revert he
      cases c 2 2 <;> decide +kernel
    cases v52 : c 3 2 with
    | false =>
      have v53 : c 2 3=true := by
        have he := hs 2 1
        rw [v52, v21, v51] at he
        revert he
        cases c 2 3 <;> decide +kernel
      have v54 : c 3 3=true := by
        have he := hs 2 2
        rw [v51, v53] at he
        revert he
        cases c 3 3 <;> cases c 2 4 <;> decide +kernel
      have he := hs 3 2
      rw [v44, v52, v54] at he
      revert he
      cases c 3 4 <;> decide +kernel
    | true =>
      have v55 : c 2 3=false := by
        have he := hs 2 1
        rw [v52, v21, v51] at he
        revert he
        cases c 2 3 <;> decide +kernel
      have v56 : c 1 4=false := by
        have he := hs 1 2
        rw [v55, v31, v49] at he
        revert he
        cases c 1 4 <;> decide +kernel
      have v57 : c 0 5=false := by
        have he := hs 0 3
        rw [v56, v42, v50] at he
        revert he
        cases c 0 5 <;> decide +kernel
      cases v58 : c 3 3 with
      | false =>
        have v59 : c 2 4=false := by
          have he := hs 2 2
          rw [v58, v51, v55] at he
          revert he
          cases c 2 4 <;> decide +kernel
        have v60 : c 3 4=true := by
          have he := hs 3 2
          rw [v44, v52, v58] at he
          revert he
          cases c 3 4 <;> decide +kernel
        have v61 : c 4 4=true := by
          have he := hs 3 3
          rw [v58, v60] at he
          revert he
          cases c 4 4 <;> cases c 3 5 <;> decide +kernel
        have v62 : c 5 3=true := by
          have he := hs 4 2
          rw [v43, v44, v61] at he
          revert he
          cases c 5 3 <;> decide +kernel
        have v63 : c 5 4=true := by
          have he := hs 4 3
          rw [v44, v61] at he
          revert he
          cases c 5 4 <;> cases c 4 5 <;> decide +kernel
        have v64 : c 6 2=true := by
          have he := hs 5 1
          rw [v33, v34, v62] at he
          revert he
          cases c 6 2 <;> decide +kernel
        have v65 : c 6 3=true := by
          have he := hs 5 2
          rw [v34, v62, v63] at he
          revert he
          cases c 6 3 <;> decide +kernel
        have v66 : c 6 4=false := by
          have he := hs 5 3
          rw [v62, v63] at he
          revert he
          cases c 6 4 <;> cases c 5 5 <;> decide +kernel
        have v67 : c 7 2=false := by
          have he := hs 6 1
          rw [v23, v64, v65] at he
          revert he
          cases c 7 2 <;> decide +kernel
        have v68 : c 7 3=false := by
          have he := hs 6 2
          rw [v64, v65, v66] at he
          revert he
          cases c 7 3 <;> decide +kernel
        have v69 : c 8 2=true := by
          have he := hs 7 1
          rw [v35, v67, v68] at he
          revert he
          cases c 8 2 <;> decide +kernel
        have v70 : c 9 1=true := by
          have he := hs 8 0
          rw [v9, v24, v69] at he
          revert he
          cases c 9 1 <;> decide +kernel
        have v71 : c 9 2=true := by
          have he := hs 8 1
          rw [v24, v69] at he
          revert he
          cases c 9 2 <;> cases c 8 3 <;> decide +kernel
        have v72 : c 10 2=false := by
          have he := hs 9 1
          rw [v70, v71] at he
          revert he
          cases c 10 2 <;> cases c 9 3 <;> decide +kernel
        have v73 : c 11 1=false := by
          have he := hs 10 0
          rw [v11, v25, v72] at he
          revert he
          cases c 11 1 <;> decide +kernel
        have v74 : c 11 2=true := by
          have he := hs 11 0
          rw [v26, v12, v73] at he
          revert he
          cases c 11 2 <;> decide +kernel
        have he := hs 11 1
        rw [v45, v73, v74] at he
        revert he
        cases c 11 3 <;> decide +kernel
      | true =>
        have v75 : c 2 4=true := by
          have he := hs 2 2
          rw [v58, v51, v55] at he
          revert he
          cases c 2 4 <;> decide +kernel
        have v76 : c 3 4=true := by
          have he := hs 2 3
          rw [v55, v75] at he
          revert he
          cases c 3 4 <;> cases c 2 5 <;> decide +kernel
        have v77 : c 4 4=false := by
          have he := hs 3 3
          rw [v58, v76] at he
          revert he
          cases c 4 4 <;> cases c 3 5 <;> decide +kernel
        have v78 : c 5 3=false := by
          have he := hs 4 2
          rw [v43, v44, v77] at he
          revert he
          cases c 5 3 <;> decide +kernel
        have v79 : c 6 2=false := by
          have he := hs 5 1
          rw [v33, v34, v78] at he
          revert he
          cases c 6 2 <;> decide +kernel
        have v80 : c 1 5=true := by
          have he := hs 1 3
          rw [v75, v49, v56] at he
          revert he
          cases c 1 5 <;> decide +kernel
        have v81 : c 2 5=true := by
          have he := hs 1 4
          rw [v56, v80] at he
          revert he
          cases c 2 5 <;> cases c 1 6 <;> decide +kernel
        have v82 : c 3 5=false := by
          have he := hs 2 4
          rw [v75, v81] at he
          revert he
          cases c 3 5 <;> cases c 2 6 <;> decide +kernel
        have v83 : c 0 6=true := by
          have he := hs 0 4
          rw [v80, v50, v57] at he
          revert he
          cases c 0 6 <;> decide +kernel
        have v84 : c 1 6=true := by
          have he := hs 0 5
          rw [v57, v83] at he
          revert he
          cases c 1 6 <;> cases c 0 7 <;> decide +kernel
        have v85 : c 2 6=false := by
          have he := hs 1 5
          rw [v80, v84] at he
          revert he
          cases c 2 6 <;> cases c 1 7 <;> decide +kernel
        cases v86 : c 3 6 with
        | false =>
          have v87 : c 2 7=true := by
            have he := hs 2 5
            rw [v86, v81, v85] at he
            revert he
            cases c 2 7 <;> decide +kernel
          have v88 : c 3 7=true := by
            have he := hs 2 6
            rw [v85, v87] at he
            revert he
            cases c 3 7 <;> cases c 2 8 <;> decide +kernel
          have v89 : c 4 5=true := by
            have he := hs 3 4
            rw [v76, v82, v86] at he
            revert he
            cases c 4 5 <;> decide +kernel
          have v90 : c 4 6=true := by
            have he := hs 3 5
            rw [v82, v86, v88] at he
            revert he
            cases c 4 6 <;> decide +kernel
          have v91 : c 4 7=true := by
            have he := hs 3 6
            rw [v86, v88] at he
            revert he
            cases c 4 7 <;> cases c 3 8 <;> decide +kernel
          have v92 : c 5 4=true := by
            have he := hs 4 3
            rw [v44, v77, v89] at he
            revert he
            cases c 5 4 <;> decide +kernel
          have v93 : c 5 5=true := by
            have he := hs 4 4
            rw [v77, v89, v90] at he
            revert he
            cases c 5 5 <;> decide +kernel
          have v94 : c 5 6=false := by
            have he := hs 4 5
            rw [v89, v90, v91] at he
            revert he
            cases c 5 6 <;> decide +kernel
          have v95 : c 5 7=false := by
            have he := hs 4 6
            rw [v90, v91] at he
            revert he
            cases c 5 7 <;> cases c 4 8 <;> decide +kernel
          have v96 : c 6 3=true := by
            have he := hs 5 2
            rw [v34, v78, v92] at he
            revert he
            cases c 6 3 <;> decide +kernel
          have v97 : c 6 4=true := by
            have he := hs 5 3
            rw [v78, v92, v93] at he
            revert he
            cases c 6 4 <;> decide +kernel
          have v98 : c 6 5=false := by
            have he := hs 5 4
            rw [v92, v93, v94] at he
            revert he
            cases c 6 5 <;> decide +kernel
          have v99 : c 6 6=true := by
            have he := hs 5 5
            rw [v93, v94, v95] at he
            revert he
            cases c 6 6 <;> decide +kernel
          have v100 : c 7 2=false := by
            have he := hs 6 1
            rw [v23, v79, v96] at he
            revert he
            cases c 7 2 <;> decide +kernel
          have v101 : c 7 3=true := by
            have he := hs 6 2
            rw [v79, v96, v97] at he
            revert he
            cases c 7 3 <;> decide +kernel
          have v102 : c 7 4=false := by
            have he := hs 6 3
            rw [v96, v97, v98] at he
            revert he
            cases c 7 4 <;> decide +kernel
          have v103 : c 7 5=false := by
            have he := hs 6 4
            rw [v97, v98, v99] at he
            revert he
            cases c 7 5 <;> decide +kernel
          have v104 : c 7 6=true := by
            have he := hs 6 5
            rw [v98, v99] at he
            revert he
            cases c 7 6 <;> cases c 6 7 <;> decide +kernel
          have v105 : c 8 2=false := by
            have he := hs 7 1
            rw [v35, v100, v101] at he
            revert he
            cases c 8 2 <;> decide +kernel
          have v106 : c 8 3=true := by
            have he := hs 7 2
            rw [v100, v101, v102] at he
            revert he
            cases c 8 3 <;> decide +kernel
          have v107 : c 8 4=true := by
            have he := hs 7 3
            rw [v101, v102, v103] at he
            revert he
            cases c 8 4 <;> decide +kernel
          have v108 : c 8 5=true := by
            have he := hs 7 4
            rw [v102, v103, v104] at he
            revert he
            cases c 8 5 <;> decide +kernel
          have v109 : c 8 6=true := by
            have he := hs 7 5
            rw [v103, v104] at he
            revert he
            cases c 8 6 <;> cases c 7 7 <;> decide +kernel
          have v110 : c 9 1=false := by
            have he := hs 8 0
            rw [v9, v24, v105] at he
            revert he
            cases c 9 1 <;> decide +kernel
          have v111 : c 9 2=true := by
            have he := hs 8 1
            rw [v24, v105, v106] at he
            revert he
            cases c 9 2 <;> decide +kernel
          have v112 : c 9 3=true := by
            have he := hs 8 2
            rw [v105, v106, v107] at he
            revert he
            cases c 9 3 <;> decide +kernel
          have v113 : c 9 4=false := by
            have he := hs 8 3
            rw [v106, v107, v108] at he
            revert he
            cases c 9 4 <;> decide +kernel
          have v114 : c 9 5=false := by
            have he := hs 8 4
            rw [v107, v108, v109] at he
            revert he
            cases c 9 5 <;> decide +kernel
          have v115 : c 9 6=false := by
            have he := hs 8 5
            rw [v108, v109] at he
            revert he
            cases c 9 6 <;> cases c 8 7 <;> decide +kernel
          have v116 : c 10 2=true := by
            have he := hs 9 1
            rw [v110, v111, v112] at he
            revert he
            cases c 10 2 <;> decide +kernel
          have v117 : c 10 3=false := by
            have he := hs 9 2
            rw [v111, v112, v113] at he
            revert he
            cases c 10 3 <;> decide +kernel
          have v118 : c 10 4=true := by
            have he := hs 9 3
            rw [v112, v113, v114] at he
            revert he
            cases c 10 4 <;> decide +kernel
          have v119 : c 10 5=false := by
            have he := hs 9 4
            rw [v113, v114, v115] at he
            revert he
            cases c 10 5 <;> decide +kernel
          have v120 : c 11 1=true := by
            have he := hs 10 0
            rw [v11, v25, v116] at he
            revert he
            cases c 11 1 <;> decide +kernel
          have v121 : c 11 2=true := by
            have he := hs 10 1
            rw [v25, v116, v117] at he
            revert he
            cases c 11 2 <;> decide +kernel
          have v122 : c 11 3=false := by
            have he := hs 10 2
            rw [v116, v117, v118] at he
            revert he
            cases c 11 3 <;> decide +kernel
          have v123 : c 11 4=true := by
            have he := hs 10 3
            rw [v117, v118, v119] at he
            revert he
            cases c 11 4 <;> decide +kernel
          have v124 : c 12 4=true := by
            have he := hs 11 3
            rw [v122, v123] at he
            revert he
            cases c 12 4 <;> cases c 11 5 <;> decide +kernel
          have v125 : c 13 3=true := by
            have he := hs 12 2
            rw [v45, v46, v124] at he
            revert he
            cases c 13 3 <;> decide +kernel
          have v126 : c 13 4=true := by
            have he := hs 12 3
            rw [v46, v124] at he
            revert he
            cases c 13 4 <;> cases c 12 5 <;> decide +kernel
          have v127 : c 14 2=true := by
            have he := hs 13 1
            rw [v36, v37, v125] at he
            revert he
            cases c 14 2 <;> decide +kernel
          have v128 : c 14 3=true := by
            have he := hs 13 2
            rw [v37, v125, v126] at he
            revert he
            cases c 14 3 <;> decide +kernel
          have v129 : c 14 4=false := by
            have he := hs 13 3
            rw [v125, v126] at he
            revert he
            cases c 14 4 <;> cases c 13 5 <;> decide +kernel
          have v130 : c 15 2=false := by
            have he := hs 14 1
            rw [v27, v127, v128] at he
            revert he
            cases c 15 2 <;> decide +kernel
          have v131 : c 15 3=false := by
            have he := hs 14 2
            rw [v127, v128, v129] at he
            revert he
            cases c 15 3 <;> decide +kernel
          have he := hs 15 1
          rw [v47, v38, v130, v131] at he
          revert he
          decide +kernel
        | true =>
          have v132 : c 2 7=false := by
            have he := hs 2 5
            rw [v86, v81, v85] at he
            revert he
            cases c 2 7 <;> decide +kernel
          have v133 : c 4 5=false := by
            have he := hs 3 4
            rw [v76, v82, v86] at he
            revert he
            cases c 4 5 <;> decide +kernel
          have v134 : c 4 6=true := by
            have he := hs 3 5
            rw [v82, v86] at he
            revert he
            cases c 4 6 <;> cases c 3 7 <;> decide +kernel
          have v135 : c 5 4=false := by
            have he := hs 4 3
            rw [v44, v77, v133] at he
            revert he
            cases c 5 4 <;> decide +kernel
          have v136 : c 5 5=true := by
            have he := hs 4 4
            rw [v77, v133, v134] at he
            revert he
            cases c 5 5 <;> decide +kernel
          have v137 : c 5 6=true := by
            have he := hs 4 5
            rw [v133, v134] at he
            revert he
            cases c 5 6 <;> cases c 4 7 <;> decide +kernel
          have v138 : c 6 3=false := by
            have he := hs 5 2
            rw [v34, v78, v135] at he
            revert he
            cases c 6 3 <;> decide +kernel
          have v139 : c 6 4=true := by
            have he := hs 5 3
            rw [v78, v135, v136] at he
            revert he
            cases c 6 4 <;> decide +kernel
          have v140 : c 6 5=true := by
            have he := hs 5 4
            rw [v135, v136, v137] at he
            revert he
            cases c 6 5 <;> decide +kernel
          have v141 : c 6 6=false := by
            have he := hs 5 5
            rw [v136, v137] at he
            revert he
            cases c 6 6 <;> cases c 5 7 <;> decide +kernel
          have v142 : c 7 2=true := by
            have he := hs 6 1
            rw [v23, v79, v138] at he
            revert he
            cases c 7 2 <;> decide +kernel
          have v143 : c 7 3=true := by
            have he := hs 6 2
            rw [v79, v138, v139] at he
            revert he
            cases c 7 3 <;> decide +kernel
          have v144 : c 7 4=true := by
            have he := hs 6 3
            rw [v138, v139, v140] at he
            revert he
            cases c 7 4 <;> decide +kernel
          have v145 : c 7 5=false := by
            have he := hs 6 4
            rw [v139, v140, v141] at he
            revert he
            cases c 7 5 <;> decide +kernel
          have v146 : c 8 2=false := by
            have he := hs 7 1
            rw [v35, v142, v143] at he
            revert he
            cases c 8 2 <;> decide +kernel
          have v147 : c 8 3=false := by
            have he := hs 7 2
            rw [v142, v143, v144] at he
            revert he
            cases c 8 3 <;> decide +kernel
          have v148 : c 8 4=false := by
            have he := hs 7 3
            rw [v143, v144, v145] at he
            revert he
            cases c 8 4 <;> decide +kernel
          have v149 : c 9 1=false := by
            have he := hs 8 0
            rw [v9, v24, v146] at he
            revert he
            cases c 9 1 <;> decide +kernel
          have v150 : c 9 2=false := by
            have he := hs 8 1
            rw [v24, v146, v147] at he
            revert he
            cases c 9 2 <;> decide +kernel
          have v151 : c 9 3=false := by
            have he := hs 8 2
            rw [v146, v147, v148] at he
            revert he
            cases c 9 3 <;> decide +kernel
          have he := hs 9 0
          rw [v25, v10, v149, v150] at he
          revert he
          decide +kernel
  | true =>
    have v152 : c 0 4=true := by
      have he := hs 0 2
      rw [v49, v41, v42] at he
      revert he
      cases c 0 4 <;> decide +kernel
    have v153 : c 1 4=true := by
      have he := hs 0 3
      rw [v42, v152] at he
      revert he
      cases c 1 4 <;> cases c 0 5 <;> decide +kernel
    have v154 : c 2 2=true := by
      have he := hs 1 1
      rw [v30, v31, v49] at he
      revert he
      cases c 2 2 <;> decide +kernel
    have v155 : c 2 3=true := by
      have he := hs 1 2
      rw [v31, v49, v153] at he
      revert he
      cases c 2 3 <;> decide +kernel
    have v156 : c 2 4=false := by
      have he := hs 1 3
      rw [v49, v153] at he
      revert he
      cases c 2 4 <;> cases c 1 5 <;> decide +kernel
    have v157 : c 3 2=false := by
      have he := hs 2 1
      rw [v21, v154, v155] at he
      revert he
      cases c 3 2 <;> decide +kernel
    have v158 : c 3 3=false := by
      have he := hs 2 2
      rw [v154, v155, v156] at he
      revert he
      cases c 3 3 <;> decide +kernel
    have he := hs 3 1
    rw [v43, v32, v157, v158] at he
    revert he
    decide +kernel

theorem no_free_1010111010 (R : Nat → Bool) (s : Nat) :
    (List.range 10).map (fun i => !u R (s+i)) ≠ word := by
  intro h
  let c : Nat → Nat → Bool := fun t p => drv altCol R (2*s+1+t) p
  apply no_profile c
  · intro t p
    dsimp [c]
    rw [show 2*s+1+(t+1)=2*s+1+t+1 by omega]
    rfl
  · intro t
    dsimp [c]
    rw [drv_col0]
    unfold altCol
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq]
    omega
  · intro i hi
    have hh := congrArg (fun l : List Bool => l.getD i false) h
    have hv : (!u R (s+i))=word.getD i false := by
      simpa [List.getD_eq_getElem?_getD,hi] using hh
    have hv' : u R (s+i)= !(word.getD i false) := by
      cases hu : u R (s+i) <;> cases hw : word.getD i false <;> simp_all
    dsimp [c]
    unfold u at hv'
    rw [show 2*(s+i)+1=2*s+1+2*i by omega] at hv'
    exact hv'

def singleFlip (L s : Nat) : Bool := if s=L then true else decide (s%2=1)

theorem isolated_word (L : Nat) (hL : 6≤L) (he : L%2=0) :
    (List.range 10).map (fun i => singleFlip L (L-5+i))=word := by
  have hv (i : Nat) (hi : i<10) :
      singleFlip L (L-5+i)=decide (i=0 ∨ i=2 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=8) := by
    unfold singleFlip
    by_cases h : L-5+i=L
    · rw [if_pos h]
      have : i=5 := by omega
      simp [this]
    · rw [if_neg h]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
  have hr : List.range 10=[0,1,2,3,4,5,6,7,8,9] := by decide +kernel
  have h0 : singleFlip L (L-5)=true := by simpa using hv 0 (by omega)
  rw [hr]
  simp only [List.map_cons,List.map_nil]
  simp [word,h0,hv 1 (by omega),hv 2 (by omega),hv 3 (by omega),
    hv 4 (by omega),hv 5 (by omega),hv 6 (by omega),hv 7 (by omega),hv 8 (by omega),hv 9 (by omega)]

theorem no_actual_isolated_flip (L : Nat) (hL : 6≤L) (he : L%2=0)
    (R : Nat → Bool) : ¬ (∀ s, (!u R s)=singleFlip L s) := by
  intro h
  apply no_free_1010111010 R (L-5)
  simpa only [h] using isolated_word L hL he

theorem delayed_family_not_actual (j : Nat) (hj : 0<j) (R : Nat → Bool) :
    ¬ (∀ s, (!u R s)=singleFlip (4*j+2) s) :=
  no_actual_isolated_flip (4*j+2) (by omega) (by omega) R

end Rule30IsolatedDefectResearch

