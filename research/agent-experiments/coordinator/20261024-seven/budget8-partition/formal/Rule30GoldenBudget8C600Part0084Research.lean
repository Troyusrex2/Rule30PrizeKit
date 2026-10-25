import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0084Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 12158128730458715702606218

theorem path_eq : path 281104 19=q := by rfl

theorem literal_cert : dfs 8 83 19 q=true := by decide +kernel

theorem cert : dfs 8 83 19 (path 281104 19)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0084Research
