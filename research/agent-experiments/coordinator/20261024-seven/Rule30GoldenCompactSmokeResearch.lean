import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenCompactSmokeResearch
open Rule30GoldenCompactBudgetResearch (check)

theorem initial_run_boundary : check 0 4=false ∧ check 0 5=true := by decide +kernel

theorem one_black_boundary : check 1 11=false ∧ check 1 12=true := by decide +kernel

theorem two_black_boundary : check 2 16=false ∧ check 2 17=true := by decide +kernel

theorem small_frontier_compact_agree : (List.range 3).all (fun b =>
    (List.range 18).all (fun K => check b K == Rule30GoldenBudgetResearch.check b K)) = true := by decide +kernel

end Rule30GoldenCompactSmokeResearch
