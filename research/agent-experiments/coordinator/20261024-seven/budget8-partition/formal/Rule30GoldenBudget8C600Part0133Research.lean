import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0133Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 196329643627450865594746485

theorem path_eq : path 720968 20=q := by rfl

theorem literal_cert : dfs 8 82 20 q=true := by decide +kernel

theorem cert : dfs 8 82 20 (path 720968 20)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0133Research
