import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0331Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 3256974026757796273529220041628330

theorem path_eq : path 41943177 26=q := by rfl

theorem literal_cert : dfs 8 76 26 q=true := by decide +kernel

theorem cert : dfs 8 76 26 (path 41943177 26)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0331Research
