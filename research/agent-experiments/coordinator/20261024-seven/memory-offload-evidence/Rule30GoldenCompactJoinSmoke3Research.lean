import Rule30GoldenCompactPathResearch
import Rule30GoldenBudget8C600Part0001Research
import Rule30GoldenBudget8C600Part0002Research

set_option maxHeartbeats 0
set_option maxRecDepth 200000

namespace Rule30GoldenCompactJoinSmoke3Research
open Rule30GoldenCompactBudgetResearch
open Rule30GoldenCompactPathResearch

theorem joined : dfs 8 82 20 (path 296976 20)=true := by
  apply dfs_of_children (fuel:=81)
  · have hc := Rule30GoldenBudget8C600Part0001Research.cert
    rw [zero_extension 296976 20 (by decide +kernel)] at hc
    exact hc
  · have hc := Rule30GoldenBudget8C600Part0002Research.cert
    change dfs 8 81 21 (path (296976 ||| 2^20) (20+1))=true at hc
    rw [one_extension 296976 20] at hc
    exact hc

end Rule30GoldenCompactJoinSmoke3Research
