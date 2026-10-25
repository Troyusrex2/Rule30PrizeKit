import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0397Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 9373844963303967349

theorem path_eq : path 77 14=q := by rfl

theorem literal_cert : dfs 8 88 14 q=true := by decide +kernel

theorem cert : dfs 8 88 14 (path 77 14)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0397Research
