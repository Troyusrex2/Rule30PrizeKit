import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0221Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 203722111941391368900491225249162

theorem path_eq : path 25165964 25=q := by rfl

theorem literal_cert : dfs 8 77 25 q=true := by decide +kernel

theorem cert : dfs 8 77 25 (path 25165964 25)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0221Research
