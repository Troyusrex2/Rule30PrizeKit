module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110001Steps9Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9
  · exact step10
  · exact step11
  · exact step12
  · exact step13
  · exact step14
  · exact step15
  · exact step16
  · exact step17
  · exact step18
  · exact step19

/-- Uniform column exclusion, for every padding length at least 77. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 77 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110001
