import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0047Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 10703304741397704667376073710638598826

theorem path_eq : path 21520 29=q := by rfl

theorem literal_cert : dfs 8 73 29 q=true := by decide +kernel

theorem cert : dfs 8 73 29 (path 21520 29)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0047Research
