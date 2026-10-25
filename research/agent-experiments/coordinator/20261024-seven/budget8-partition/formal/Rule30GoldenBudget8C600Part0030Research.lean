import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0030Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 1155114771436794864122651457088767461435409339592051370

theorem path_eq : path 4399122355216 43=q := by rfl

theorem literal_cert : dfs 8 59 43 q=true := by decide +kernel

theorem cert : dfs 8 59 43 (path 4399122355216 43)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0030Research
