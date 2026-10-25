import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0028Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 3945544960855248196040305275046241666199652823441326372234

theorem path_eq : path 1075844112 46=q := by rfl

theorem literal_cert : dfs 8 56 46 q=true := by decide +kernel

theorem cert : dfs 8 56 46 (path 1075844112 46)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0028Research
