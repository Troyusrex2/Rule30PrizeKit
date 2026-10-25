import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0060Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 62523908781795496549026632343123338

theorem path_eq : path 69213200 27=q := by rfl

theorem literal_cert : dfs 8 75 27 q=true := by decide +kernel

theorem cert : dfs 8 75 27 (path 69213200 27)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0060Research
