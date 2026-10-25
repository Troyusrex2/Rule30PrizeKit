import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0016Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 3730033655726377156427451050

theorem path_eq : path 1722384 21=q := by rfl

theorem literal_cert : dfs 8 81 21 q=true := by decide +kernel

theorem cert : dfs 8 81 21 (path 1722384 21)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0016Research
