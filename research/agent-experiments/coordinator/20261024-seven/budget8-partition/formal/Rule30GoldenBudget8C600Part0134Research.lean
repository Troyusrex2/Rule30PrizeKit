import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0134Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 2014876364469138302408488277

theorem path_eq : path 32840 21=q := by rfl

theorem literal_cert : dfs 8 81 21 q=true := by decide +kernel

theorem cert : dfs 8 81 21 (path 32840 21)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0134Research
