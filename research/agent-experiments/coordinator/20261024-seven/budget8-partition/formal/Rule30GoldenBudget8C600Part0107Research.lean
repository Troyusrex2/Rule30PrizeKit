import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0107Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 795567889086212090717260133770

theorem path_eq : path 4196560 23=q := by rfl

theorem literal_cert : dfs 8 79 23 q=true := by decide +kernel

theorem cert : dfs 8 79 23 (path 4196560 23)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0107Research
