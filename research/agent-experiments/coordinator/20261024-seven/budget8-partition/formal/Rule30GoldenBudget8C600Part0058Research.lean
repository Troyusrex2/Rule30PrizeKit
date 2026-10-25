import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0058Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 835500484323020962285386998808926890

theorem path_eq : path 2104336 28=q := by rfl

theorem literal_cert : dfs 8 74 28 q=true := by decide +kernel

theorem cert : dfs 8 74 28 (path 2104336 28)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0058Research
