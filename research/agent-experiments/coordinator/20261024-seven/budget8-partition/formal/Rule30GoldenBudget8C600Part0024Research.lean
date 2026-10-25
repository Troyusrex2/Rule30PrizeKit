import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0024Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 2765432812215521715539010029532501

theorem path_eq : path 33559568 26=q := by rfl

theorem literal_cert : dfs 8 76 26 q=true := by decide +kernel

theorem cert : dfs 8 76 26 (path 33559568 26)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0024Research
