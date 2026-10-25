import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0029Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 4766962570759364624120379281600613131047247597913184242293

theorem path_eq : path 35185447932944 46=q := by rfl

theorem literal_cert : dfs 8 56 46 q=true := by decide +kernel

theorem cert : dfs 8 56 46 (path 35185447932944 46)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0029Research
