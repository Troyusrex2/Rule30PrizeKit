import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0053Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 3105311535453136003405777578

theorem path_eq : path 1070096 21=q := by rfl

theorem literal_cert : dfs 8 81 21 q=true := by decide +kernel

theorem cert : dfs 8 81 21 (path 1070096 21)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0053Research
