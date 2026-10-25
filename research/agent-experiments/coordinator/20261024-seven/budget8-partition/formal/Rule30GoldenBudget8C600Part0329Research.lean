import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0329Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 41847258967868104295891557473946282

theorem path_eq : path 8388745 27=q := by rfl

theorem literal_cert : dfs 8 75 27 q=true := by decide +kernel

theorem cert : dfs 8 75 27 (path 8388745 27)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0329Research
