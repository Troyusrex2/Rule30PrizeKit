import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0038Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 65571702752095079883525689593630014929290

theorem path_eq : path 3223327760 32=q := by rfl

theorem literal_cert : dfs 8 70 32 q=true := by decide +kernel

theorem cert : dfs 8 70 32 (path 3223327760 32)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0038Research
