import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0293Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 34516071818

theorem path_eq : path 86 7=q := by rfl

theorem literal_cert : dfs 8 95 7 q=true := by decide +kernel

theorem cert : dfs 8 95 7 (path 86 7)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0293Research
