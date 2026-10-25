import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0037Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 1069394052439444624985004921964184525731157

theorem path_eq : path 5370811408 33=q := by rfl

theorem literal_cert : dfs 8 69 33 q=true := by decide +kernel

theorem cert : dfs 8 69 33 (path 5370811408 33)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0037Research
