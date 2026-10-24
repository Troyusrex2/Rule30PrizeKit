module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_176 : seg 46 45 1 52717921763341 0 8192 1441792 46351287058445 0 = true := by
  decide +kernel

theorem seg_177 : seg 46 45 1 62689879523341 0 8192 1449984 52717921763341 0 = true := by
  decide +kernel

theorem seg_178 : seg 46 45 1 54636161531917 0 8192 1458176 62689879523341 0 = true := by
  decide +kernel

theorem seg_179 : seg 46 45 1 55467355144205 0 8192 1466368 54636161531917 0 = true := by
  decide +kernel

theorem seg_180 : seg 46 45 1 54755883745293 0 8192 1474560 55467355144205 0 = true := by
  decide +kernel

theorem seg_181 : seg 46 45 1 5547487133709 0 8192 1482752 54755883745293 0 = true := by
  decide +kernel

theorem seg_182 : seg 46 45 1 26145495973901 0 8192 1490944 5547487133709 0 = true := by
  decide +kernel

theorem seg_183 : seg 46 45 1 4277787426829 0 8192 1499136 26145495973901 0 = true := by
  decide +kernel

theorem path_chunk_22 : PathOK 46 45 1 1441792 (46351287058445, 0) (4277787426829, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 52717921763341 0 8192 1441792 46351287058445 0 seg_176) (seg_sound 46 45 1 62689879523341 0 8192 1449984 52717921763341 0 seg_177)) (path_append (seg_sound 46 45 1 54636161531917 0 8192 1458176 62689879523341 0 seg_178) (seg_sound 46 45 1 55467355144205 0 8192 1466368 54636161531917 0 seg_179))) (path_append (path_append (seg_sound 46 45 1 54755883745293 0 8192 1474560 55467355144205 0 seg_180) (seg_sound 46 45 1 5547487133709 0 8192 1482752 54755883745293 0 seg_181)) (path_append (seg_sound 46 45 1 26145495973901 0 8192 1490944 5547487133709 0 seg_182) (seg_sound 46 45 1 4277787426829 0 8192 1499136 26145495973901 0 seg_183))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
