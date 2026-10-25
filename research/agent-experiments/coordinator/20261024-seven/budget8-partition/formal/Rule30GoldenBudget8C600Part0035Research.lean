import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0035Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 68717884842276529961995390755477516464729799050

theorem path_eq : path 69795320848 37=q := by rfl

theorem literal_cert : dfs 8 65 37 q=true := by decide +kernel

theorem cert : dfs 8 65 37 (path 69795320848 37)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0035Research
