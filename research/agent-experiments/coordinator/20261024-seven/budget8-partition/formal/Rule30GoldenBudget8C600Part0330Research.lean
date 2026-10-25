import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0330Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 54665741837375960009056997961528661

theorem path_eq : path 75497609 27=q := by rfl

theorem literal_cert : dfs 8 75 27 q=true := by decide +kernel

theorem cert : dfs 8 75 27 (path 75497609 27)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0330Research
