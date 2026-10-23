module

public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101ForwardResearch
public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101TailResearch
public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Back0Research
public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Back1Research
public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Back2Research
public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101ForceResearch

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tube10101Research
open Rule30StripCertificates
set_option maxHeartbeats 0
theorem Qstep (n : Nat) (hn : n < 24)  :
    Rule30SparsePreimageResearch.restrictedPreCheck 16 false Z (Q (n+1)) (Q n) = true := by
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Qstep0
  · exact Qstep1
  · exact Qstep2
  · exact Qstep3
  · exact Qstep4
  · exact Qstep5
  · exact Qstep6
  · exact Qstep7
  · exact Qstep8
  · exact Qstep9
  · exact Qstep10
  · exact Qstep11
  · exact Qstep12
  · exact Qstep13
  · exact Qstep14
  · exact Qstep15
  · exact Qstep16
  · exact Qstep17
  · exact Qstep18
  · exact Qstep19
  · exact Qstep20
  · exact Qstep21
  · exact Qstep22
  · exact Qstep23
theorem Pstep (j : Nat) (hj : j < 5)  :
    preCheck 16 (tail.getD j false) (P j) (P (j+1)) = true := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact Pstep0
  · exact Pstep1
  · exact Pstep2
  · exact Pstep3
  · exact Pstep4
theorem Sstep (j : Nat) (hj : j < 5)  :
    image 16 (tail.getD j false) (S j) = S (j+1) := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact Sstep0
  · exact Sstep1
  · exact Sstep2
  · exact Sstep3
  · exact Sstep4
theorem Qforce (n : Nat) (hn : n ≤ 24)  :
    colConst 16 (Z &&& Q n) (decide (n ≤ 8)) = true := by
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Qforce0
  · exact Qforce1
  · exact Qforce2
  · exact Qforce3
  · exact Qforce4
  · exact Qforce5
  · exact Qforce6
  · exact Qforce7
  · exact Qforce8
  · exact Qforce9
  · exact Qforce10
  · exact Qforce11
  · exact Qforce12
  · exact Qforce13
  · exact Qforce14
  · exact Qforce15
  · exact Qforce16
  · exact Qforce17
  · exact Qforce18
  · exact Qforce19
  · exact Qforce20
  · exact Qforce21
  · exact Qforce22
  · exact Qforce23
  · exact Qforce24
theorem Pforce (j : Nat) (hj : j < 5) (hw : tail.getD j false = false) :
    colConst 16 (S j &&& P j) false = true := by
  have hcases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · simp [tail] at hw
  · exact Pforce1
  · simp [tail] at hw
  · exact Pforce3
  · simp [tail] at hw

end Ruliology.CellularAutomata.Rule30Tube10101Research
