import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0403Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 2186566261

theorem path_eq : path 45 6=q := by rfl

theorem literal_cert : dfs 8 96 6 q=true := by decide +kernel

theorem cert : dfs 8 96 6 (path 45 6)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0403Research
