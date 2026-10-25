import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0390Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 226158596012525135189

theorem path_eq : path 21525 15=q := by rfl

theorem literal_cert : dfs 8 87 15 q=true := by decide +kernel

theorem cert : dfs 8 87 15 (path 21525 15)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0390Research
