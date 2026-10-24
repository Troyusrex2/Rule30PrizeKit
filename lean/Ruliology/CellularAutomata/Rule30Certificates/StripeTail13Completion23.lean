module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_184 : seg 46 45 1 64554851631117 0 8192 1507328 4277787426829 0 = true := by
  decide +kernel

theorem seg_185 : seg 46 45 1 584652423181 0 8192 1515520 64554851631117 0 = true := by
  decide +kernel

theorem seg_186 : seg 46 45 1 67022847213581 0 8192 1523712 584652423181 0 = true := by
  decide +kernel

theorem seg_187 : seg 46 45 1 42530913648653 0 8192 1531904 67022847213581 0 = true := by
  decide +kernel

theorem seg_188 : seg 46 45 1 44362062888973 0 8192 1540096 42530913648653 0 = true := by
  decide +kernel

theorem seg_189 : seg 46 45 1 37313065254925 0 8192 1548288 44362062888973 0 = true := by
  decide +kernel

theorem seg_190 : seg 46 45 1 13896249245709 0 8192 1556480 37313065254925 0 = true := by
  decide +kernel

theorem seg_191 : seg 46 45 1 51127290691597 0 8192 1564672 13896249245709 0 = true := by
  decide +kernel

theorem path_chunk_23 : PathOK 46 45 1 1507328 (4277787426829, 0) (51127290691597, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 64554851631117 0 8192 1507328 4277787426829 0 seg_184) (seg_sound 46 45 1 584652423181 0 8192 1515520 64554851631117 0 seg_185)) (path_append (seg_sound 46 45 1 67022847213581 0 8192 1523712 584652423181 0 seg_186) (seg_sound 46 45 1 42530913648653 0 8192 1531904 67022847213581 0 seg_187))) (path_append (path_append (seg_sound 46 45 1 44362062888973 0 8192 1540096 42530913648653 0 seg_188) (seg_sound 46 45 1 37313065254925 0 8192 1548288 44362062888973 0 seg_189)) (path_append (seg_sound 46 45 1 13896249245709 0 8192 1556480 37313065254925 0 seg_190) (seg_sound 46 45 1 51127290691597 0 8192 1564672 13896249245709 0 seg_191))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
