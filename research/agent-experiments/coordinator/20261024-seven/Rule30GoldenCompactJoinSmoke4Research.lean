import Rule30GoldenCompactPathResearch
import Rule30GoldenBudget8C600Part0001Research
import Rule30GoldenBudget8C600Part0002Research

set_option maxHeartbeats 0
set_option maxRecDepth 200000

namespace Rule30GoldenCompactJoinSmoke4Research
open Rule30GoldenCompactBudgetResearch
open Rule30GoldenCompactPathResearch

theorem joined : dfs 8 82 20 (path 296976 20)=true := by
  apply dfs_of_children (fuel:=81)
  · have hc := Rule30GoldenBudget8C600Part0001Research.cert
    rw [zero_extension 296976 20 (by decide +kernel)] at hc
    exact hc
  · have hc := Rule30GoldenBudget8C600Part0002Research.cert
    have hn : (296976 ||| 2^20)=1345552 := by decide +kernel
    have hp := one_extension 296976 20
    rw [hn] at hp
    rw [hp] at hc
    exact hc

end Rule30GoldenCompactJoinSmoke4Research
