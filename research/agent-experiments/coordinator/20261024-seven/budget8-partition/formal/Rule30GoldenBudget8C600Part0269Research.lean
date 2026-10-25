import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0269Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 47506825890367869356714

theorem path_eq : path 65734 17=q := by rfl

theorem literal_cert : dfs 8 85 17 q=true := by decide +kernel

theorem cert : dfs 8 85 17 (path 65734 17)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0269Research
