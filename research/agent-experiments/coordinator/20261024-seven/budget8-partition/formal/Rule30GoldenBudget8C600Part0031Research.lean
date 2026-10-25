import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudget8C600Part0031Research
open Rule30GoldenCompactBudgetResearch

def q : Nat := 72055928414902525002842003627257442977236053398477482

theorem path_eq : path 2200099099664 42=q := by rfl

theorem literal_cert : dfs 8 60 42 q=true := by decide +kernel

theorem cert : dfs 8 60 42 (path 2200099099664 42)=true := by
  rw [path_eq]
  exact literal_cert

end Rule30GoldenBudget8C600Part0031Research
