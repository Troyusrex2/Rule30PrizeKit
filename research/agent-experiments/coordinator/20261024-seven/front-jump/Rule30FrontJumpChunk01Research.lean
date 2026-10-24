import Rule30FrontJumpStatesResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30FrontJumpResearch
open Rule30FrontLanesResearch

theorem run_01 : run 34 (allMask 12) 8192 state001 = state002 := by
  decide +kernel

end Rule30FrontJumpResearch
