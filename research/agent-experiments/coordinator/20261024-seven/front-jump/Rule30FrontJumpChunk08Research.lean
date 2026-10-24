import Rule30FrontJumpStatesResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30FrontJumpResearch
open Rule30FrontLanesResearch

theorem run_08 : run 34 (allMask 12) 4531 state008 = state009 := by
  decide +kernel

end Rule30FrontJumpResearch
