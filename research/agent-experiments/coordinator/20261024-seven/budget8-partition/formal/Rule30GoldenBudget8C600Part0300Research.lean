import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0300Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 689968597674

theorem path_eq : path 94 8=q := by rfl

theorem literal_cert : dfs 8 94 8 q=true := by decide +kernel

theorem cert : dfs 8 94 8 (path 94 8)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0300Research
