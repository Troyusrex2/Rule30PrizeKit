import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0165Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 52020684200245523930091779413

theorem path_eq : path 2098376 22=q := by rfl

theorem literal_cert : dfs 8 80 22 q=true := by decide +kernel

theorem cert : dfs 8 80 22 (path 2098376 22)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0165Research
