import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0100Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 2373334697964739054250

theorem path_eq : path 912 16=q := by rfl

theorem literal_cert : dfs 8 86 16 q=true := by decide +kernel

theorem cert : dfs 8 86 16 (path 912 16)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0100Research
