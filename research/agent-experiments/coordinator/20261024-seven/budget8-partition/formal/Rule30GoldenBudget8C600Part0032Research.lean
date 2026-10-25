import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0032Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 4505265338247535231652591424573306573163681014248842

theorem path_eq : path 1100587471888 41=q := by rfl

theorem literal_cert : dfs 8 61 41 q=true := by decide +kernel

theorem cert : dfs 8 61 41 (path 1100587471888 41)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0032Research
