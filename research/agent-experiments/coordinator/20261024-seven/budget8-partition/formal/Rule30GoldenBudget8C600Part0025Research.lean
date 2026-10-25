import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0025Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 163415306756371897470853214243498

theorem path_eq : path 16782352 25=q := by rfl

theorem literal_cert : dfs 8 77 25 q=true := by decide +kernel

theorem cert : dfs 8 77 25 (path 16782352 25)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0025Research
