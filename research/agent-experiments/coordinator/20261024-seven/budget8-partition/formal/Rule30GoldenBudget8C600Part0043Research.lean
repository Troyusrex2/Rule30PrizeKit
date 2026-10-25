import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0043Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 813121858579847145221956760917

theorem path_eq : path 6296592 23=q := by rfl

theorem literal_cert : dfs 8 79 23 q=true := by decide +kernel

theorem cert : dfs 8 79 23 (path 6296592 23)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0043Research
