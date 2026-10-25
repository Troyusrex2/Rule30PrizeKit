import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0036Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 270866941893180141169222252943425956692183669

theorem path_eq : path 18255713296 35=q := by rfl

theorem literal_cert : dfs 8 67 35 q=true := by decide +kernel

theorem cert : dfs 8 67 35 (path 18255713296 35)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0036Research
