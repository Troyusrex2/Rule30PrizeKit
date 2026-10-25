import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0227Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 3414290206400392299213264413947221

theorem path_eq : path 8650892 26=q := by rfl

theorem literal_cert : dfs 8 76 26 q=true := by decide +kernel

theorem cert : dfs 8 76 26 (path 8650892 26)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0227Research
