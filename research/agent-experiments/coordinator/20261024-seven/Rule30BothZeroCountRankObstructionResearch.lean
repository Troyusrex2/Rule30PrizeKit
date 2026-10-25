import Rule30GoldenCompactBudgetResearch

/-! An algebraic obstruction to a restricted ranking family. The five
constraints are independently reconstructed from actual right-driven
examples by bothzero_linear_obstruction.py. This module checks the algebraic
contradiction, not an equivalence between that Python model and official
spacetime evolution. It says nothing against other ranking families. -/

namespace Rule30BothZeroCountRankObstructionResearch

def energy (w : Nat → Nat) (c0 c1 c2 c3 : Nat) : Nat :=
  w 0 + c0*w 1 + c1*w 2 + c2*w 3 + c3*w 4

theorem no_natural_count_rank_for_five_constraints (a b : Nat → Nat)
    (h1 : energy a 6 9 8 3 + 1 ≤ energy b 5 7 8 4)
    (h2 : energy b 6 5 7 4 ≤ energy a 3 9 6 2)
    (h3 : energy b 10 10 11 7 ≤ energy a 9 11 11 5)
    (h4 : energy a 4 7 5 2 + 1 ≤ energy b 4 3 5 4)
    (h5 : energy a 8 16 12 6 + 1 ≤ energy b 11 9 12 8) : False := by
  have q1 := Nat.mul_le_mul_left 17 h1
  have q2 := Nat.mul_le_mul_left 39 h2
  have q3 := Nat.mul_le_mul_left 16 h3
  have q4 := Nat.mul_le_mul_left 26 h4
  have q5 := Nat.mul_le_mul_left 12 h5
  simp only [energy] at *
  omega

end Rule30BothZeroCountRankObstructionResearch
