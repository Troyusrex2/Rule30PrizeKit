module

public import Ruliology.CellularAutomata.Rule30Certificates.WhitePaddingShortTailSecondResearch

@[expose] public section

/-! Cached one-step checks for the white-padding family `0^r 111`, r >=49.
Each finite claim is checked by Lean; no external or native decision procedure is used. -/

namespace Ruliology.CellularAutomata.Rule30WhitePaddingResearch.Heavy111

open Rule30StripCertificates Rule30WhitePaddingResearch

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem reachedFull : zeros 14 49 (fullSet 14) = F28 := by
  rw [zeros_stable 14 28 (fullSet 14) stableF 49 (by decide)]
  exact reachF28

theorem firstTail : applyWord 14 tail F28 = S1 := by decide +kernel

theorem secondTail : applyWord 14 tail H49 = S2 := by decide +kernel

theorem reachedS2 : zeros 14 49 S2 = I32 := by
  rw [zeros_stable 14 32 S2 stableI 49 (by decide)]
  exact reachI32

theorem stableFull : zeros 14 (49+1) (fullSet 14) = zeros 14 49 (fullSet 14) := by
  rw [zeros_succ, reachedFull, fixedF]

theorem stableS2 : zeros 14 (49+1) S2 = zeros 14 49 S2 := by
  rw [zeros_succ, reachedS2, fixedI]

theorem returnCheck : subsetB 14 (applyWord 14 tail I32) S2 = true := by decide +kernel

theorem prefixCheck : (List.range (49+1)).all (fun j => Forces 14 (zeros 14 j S2)) = true := by
  apply List.all_eq_true.mpr
  intro j hj
  have hjlt : j < 50 := List.mem_range.mp hj
  by_cases h : j ≤ 32
  · have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 ∨ j = 32 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [reachI0, reachI1, reachI2, reachI3, reachI4, reachI5, reachI6, reachI7, reachI8, reachI9, reachI10, reachI11, reachI12, reachI13, reachI14, reachI15, reachI16, reachI17, reachI18, reachI19, reachI20, reachI21, reachI22, reachI23, reachI24, reachI25, reachI26, reachI27, reachI28, reachI29, reachI30, reachI31, reachI32] <;> decide +kernel
  · rw [zeros_stable 14 32 S2 stableI j (by omega), reachI32]
    decide +kernel

theorem tailCheck : (List.range tail.length).all (fun j => tail.getD j false ||
    Forces 14 (applyWord 14 (tail.take j) I32)) = true := by decide +kernel

theorem strip_certificate (r : Nat) (hr : 49 ≤ r) :
    stripCert (List.replicate r false ++ tail) 14 2 = true := by
  apply padding_strip tail 14 49 S1 S2
  · rw [reachedFull]; exact firstTail
  · rw [reachH49]; exact secondTail
  · exact stableFull
  · exact stableH
  · exact stableS2
  · rw [reachedS2]; exact returnCheck
  · exact prefixCheck
  · rw [reachedS2]; exact tailCheck
  · exact hr

theorem no_padding (r : Nat) (hr : 49 ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ tail) := by
  apply no_padding_word tail 14 49 S1 S2
  · rw [reachedFull]; exact firstTail
  · rw [reachH49]; exact secondTail
  · exact stableFull
  · exact stableH
  · exact stableS2
  · rw [reachedS2]; exact returnCheck
  · exact prefixCheck
  · rw [reachedS2]; exact tailCheck
  · decide
  · decide
  · exact hr

end Ruliology.CellularAutomata.Rule30WhitePaddingResearch.Heavy111
