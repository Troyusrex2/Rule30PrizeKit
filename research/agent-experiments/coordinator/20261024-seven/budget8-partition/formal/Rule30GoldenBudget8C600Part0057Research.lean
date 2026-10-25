import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0057Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 9284826303054640522

theorem path_eq : path 13328 14=q := by rfl

theorem literal_cert : dfs 8 88 14 q=true := by decide +kernel

theorem cert : dfs 8 88 14 (path 13328 14)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0057Research
