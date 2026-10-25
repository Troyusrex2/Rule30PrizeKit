import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0139Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 456096479714166069086890

theorem path_eq : path 8264 18=q := by rfl

theorem literal_cert : dfs 8 84 18 q=true := by decide +kernel

theorem cert : dfs 8 84 18 (path 8264 18)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0139Research
