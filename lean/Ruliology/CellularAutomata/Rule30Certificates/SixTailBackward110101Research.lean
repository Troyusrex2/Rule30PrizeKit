module
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110101Steps1Research
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110101
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110101
