import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0383Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 724892163848713610

theorem path_eq : path 4197 13=q := by rfl

theorem literal_cert : dfs 8 89 13 q=true := by decide +kernel

theorem cert : dfs 8 89 13 (path 4197 13)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0383Research
