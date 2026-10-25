import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0261Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 176674375031466

theorem path_eq : path 668 10=q := by rfl

theorem literal_cert : dfs 8 92 10 q=true := by decide +kernel

theorem cert : dfs 8 92 10 (path 668 10)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0261Research
