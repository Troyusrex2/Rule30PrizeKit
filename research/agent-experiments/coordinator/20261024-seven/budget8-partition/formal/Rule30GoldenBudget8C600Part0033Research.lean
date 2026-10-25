import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0033Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 18312360095202312986407894613565851726304681571669

theorem path_eq : path 275953751056 39=q := by rfl

theorem literal_cert : dfs 8 63 39 q=true := by decide +kernel

theorem cert : dfs 8 63 39 (path 275953751056 39)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0033Research
