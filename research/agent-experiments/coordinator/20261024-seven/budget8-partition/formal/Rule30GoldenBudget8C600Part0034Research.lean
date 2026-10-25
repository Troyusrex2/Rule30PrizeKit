import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0034Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 1099212619953641484720898659448834101195135847082

theorem path_eq : path 138514797584 38=q := by rfl

theorem literal_cert : dfs 8 64 38 q=true := by decide +kernel

theorem cert : dfs 8 64 38 (path 138514797584 38)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0034Research
