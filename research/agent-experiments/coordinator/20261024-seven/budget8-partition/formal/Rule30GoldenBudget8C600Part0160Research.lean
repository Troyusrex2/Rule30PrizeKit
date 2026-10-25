import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0160Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 45272688795219338

theorem path_eq : path 3400 12=q := by rfl

theorem literal_cert : dfs 8 90 12 q=true := by decide +kernel

theorem cert : dfs 8 90 12 (path 3400 12)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0160Research
