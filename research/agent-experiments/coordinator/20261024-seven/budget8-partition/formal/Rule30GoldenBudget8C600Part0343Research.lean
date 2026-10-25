import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0343Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 13316914258595947246952275686741

theorem path_eq : path 1179785 24=q := by rfl

theorem literal_cert : dfs 8 78 24 q=true := by decide +kernel

theorem cert : dfs 8 78 24 (path 1179785 24)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0343Research
