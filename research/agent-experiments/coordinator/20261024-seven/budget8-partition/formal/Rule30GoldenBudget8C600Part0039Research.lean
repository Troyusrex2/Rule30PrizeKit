import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0039Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 215795131021593607892996144716223694453

theorem path_eq : path 538973200 30=q := by rfl

theorem literal_cert : dfs 8 72 30 q=true := by decide +kernel

theorem cert : dfs 8 72 30 (path 538973200 30)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0039Research
