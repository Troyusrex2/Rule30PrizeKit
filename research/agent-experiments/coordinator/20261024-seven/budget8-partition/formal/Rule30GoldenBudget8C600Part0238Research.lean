import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0238Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 48463247919329685185877

theorem path_eq : path 98444 17=q := by rfl

theorem literal_cert : dfs 8 85 17 q=true := by decide +kernel

theorem cert : dfs 8 85 17 (path 98444 17)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0238Research
