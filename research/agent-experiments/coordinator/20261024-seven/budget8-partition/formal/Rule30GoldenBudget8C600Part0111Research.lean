import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0111Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 185145603383564536490

theorem path_eq : path 18640 15=q := by rfl

theorem literal_cert : dfs 8 87 15 q=true := by decide +kernel

theorem cert : dfs 8 87 15 (path 18640 15)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0111Research
