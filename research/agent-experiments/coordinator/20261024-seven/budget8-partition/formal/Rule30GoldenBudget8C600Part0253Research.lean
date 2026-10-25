import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0253Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 8843691391370

theorem path_eq : path 204 9=q := by rfl

theorem literal_cert : dfs 8 93 9 q=true := by decide +kernel

theorem cert : dfs 8 93 9 (path 204 9)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0253Research
