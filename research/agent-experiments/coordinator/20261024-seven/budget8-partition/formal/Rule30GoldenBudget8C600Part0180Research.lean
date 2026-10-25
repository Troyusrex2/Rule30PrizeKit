import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0180Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 49779233267870744748005087914

theorem path_eq : path 2097832 22=q := by rfl

theorem literal_cert : dfs 8 80 22 q=true := by decide +kernel

theorem cert : dfs 8 80 22 (path 2097832 22)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0180Research
