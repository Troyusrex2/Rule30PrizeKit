import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0048Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 13652529357045486760480076058362246485

theorem path_eq : path 268456976 29=q := by rfl

theorem literal_cert : dfs 8 73 29 q=true := by decide +kernel

theorem cert : dfs 8 73 29 (path 268456976 29)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0048Research
