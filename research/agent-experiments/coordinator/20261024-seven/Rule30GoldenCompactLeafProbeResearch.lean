import Rule30GoldenCompactBudgetResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenCompactLeafProbeResearch
open Rule30GoldenCompactBudgetResearch

theorem cert : dfs 8 87 15 (path 2064 15) = true := by decide +kernel

end Rule30GoldenCompactLeafProbeResearch
