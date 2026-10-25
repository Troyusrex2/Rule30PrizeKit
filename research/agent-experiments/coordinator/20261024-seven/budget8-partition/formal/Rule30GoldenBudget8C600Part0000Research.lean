import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0000Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 7892673589952964716819797

theorem path_eq : path 34832 19=q := by rfl

theorem literal_cert : dfs 8 83 19 q=true := by decide +kernel

theorem cert : dfs 8 83 19 (path 34832 19)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0000Research
