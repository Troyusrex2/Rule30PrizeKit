import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0164Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 15384087167827929190730361834101

theorem path_eq : path 12584136 24=q := by rfl

theorem literal_cert : dfs 8 78 24 q=true := by decide +kernel

theorem cert : dfs 8 78 24 (path 12584136 24)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0164Research
