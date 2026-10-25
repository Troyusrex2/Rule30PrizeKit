import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0262Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 11051304646026

theorem path_eq : path 412 9=q := by rfl

theorem literal_cert : dfs 8 93 9 q=true := by decide +kernel

theorem cert : dfs 8 93 9 (path 412 9)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0262Research
