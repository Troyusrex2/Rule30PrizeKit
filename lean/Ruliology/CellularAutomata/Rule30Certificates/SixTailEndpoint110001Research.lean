module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks15Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30RestrictedBackwardTubeResearch
theorem Pstep (j : Nat) (h : j < 6)  : preCheck K (tail.getD j false) (P j) (P (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
theorem Sstep (j : Nat) (h : j < 6)  : image K (tail.getD j false) (S j) = S (j+1) := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact s0
  · exact s1
  · exact s2
  · exact s3
  · exact s4
  · exact s5
theorem Qstep (j : Nat) (h : j < 14)  : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q (j+1)) (Q j) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact q0
  · exact q1
  · exact q2
  · exact q3
  · exact q4
  · exact q5
  · exact q6
  · exact q7
  · exact q8
  · exact q9
  · exact q10
  · exact q11
  · exact q12
  · exact q13
theorem Qforce (j : Nat) (h : j ≤ 14)  : colConst K (Z &&& Q j) (b j) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact qf0
  · exact qf1
  · exact qf2
  · exact qf3
  · exact qf4
  · exact qf5
  · exact qf6
  · exact qf7
  · exact qf8
  · exact qf9
  · exact qf10
  · exact qf11
  · exact qf12
  · exact qf13
  · exact qf14
theorem Pforce (j : Nat) (h : j < 6) (hz : tail.getD j false = false) : colConst K (S j &&& P j) (c j) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [tail] at hz
  · simp [tail] at hz
  · exact pf2
  · exact pf3
  · exact pf4
  · simp [tail] at hz

theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 74 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  apply Rule30RestrictedBackwardTubeResearch.no_padding_of_endpoint_tube hlo hzero i tail
    K L Z Q P S b c (by decide) Zzero Zfixed (by rfl) (by rfl) (by rfl) (by rfl)
  · intro d hd; exact Qstep d (by simpa [L] using hd)
  · intro j hj; exact Pstep j (by simpa [tail] using hj)
  · intro j hj; exact Sstep j (by simpa [tail] using hj)
  · intro d hd; exact Qforce d (by simpa [L] using hd)
  · intro j hj hz; exact Pforce j (by simpa [tail] using hj) hz
  · simp [tail]; omega
  · simp [K, tail]; omega
  · simp [L]; omega
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
