import Rule30FrontJumpChunk00Research
import Rule30FrontJumpChunk01Research
import Rule30FrontJumpChunk02Research
import Rule30FrontJumpChunk03Research
import Rule30FrontJumpChunk04Research
import Rule30FrontJumpChunk05Research
import Rule30FrontJumpChunk06Research
import Rule30FrontJumpChunk07Research
import Rule30FrontJumpChunk08Research

namespace Rule30FrontJumpResearch
open Rule30FrontLanesResearch

theorem run_prefix : run 34 (allMask 12) 61005 (initial 12 13 0) = state008 := by
  rw [initial_eq]
  exact (run_chain (run_chain (run_chain run_00 run_01) (run_chain run_02 run_03)) (run_chain (run_chain run_04 run_05) (run_chain run_06 run_07)))

theorem run_full : run 34 (allMask 12) 65536 (initial 12 13 0) = state009 := by
  rw [initial_eq]
  exact (run_chain (run_chain (run_chain run_00 run_01) (run_chain run_02 run_03)) (run_chain (run_chain run_04 run_05) (run_chain run_06 (run_chain run_07 run_08))))

end Rule30FrontJumpResearch
