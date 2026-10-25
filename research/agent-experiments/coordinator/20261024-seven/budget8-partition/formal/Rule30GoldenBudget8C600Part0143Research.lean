import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0143Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 213070944883824470773601358476629

theorem path_eq : path 16818248 25=q := by rfl

theorem literal_cert : dfs 8 77 25 q=true := by decide +kernel

theorem cert : dfs 8 77 25 (path 16818248 25)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0143Research
