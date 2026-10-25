import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0345Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 954041705168277336977854302890

theorem path_eq : path 5374089 23=q := by rfl

theorem literal_cert : dfs 8 79 23 q=true := by decide +kernel

theorem cert : dfs 8 79 23 (path 5374089 23)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0345Research
