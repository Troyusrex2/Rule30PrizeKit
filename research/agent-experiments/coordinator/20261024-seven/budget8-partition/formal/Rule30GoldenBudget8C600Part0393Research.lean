import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0393Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 36638636291475061

theorem path_eq : path 533 12=q := by rfl

theorem literal_cert : dfs 8 90 12 q=true := by decide +kernel

theorem cert : dfs 8 90 12 (path 533 12)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0393Research
