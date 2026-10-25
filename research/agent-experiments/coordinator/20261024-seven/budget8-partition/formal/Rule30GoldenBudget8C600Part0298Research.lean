import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0298Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 3391792940944042

theorem path_eq : path 1566 11=q := by rfl

theorem literal_cert : dfs 8 91 11 q=true := by decide +kernel

theorem cert : dfs 8 91 11 (path 1566 11)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0298Research
