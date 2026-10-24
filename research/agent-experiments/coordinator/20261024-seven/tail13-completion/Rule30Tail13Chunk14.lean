module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_112 : seg 46 45 1 37874514788365 0 8192 917504 57896159150093 0 = true := by
  decide +kernel

theorem seg_113 : seg 46 45 1 22557705109517 0 8192 925696 37874514788365 0 = true := by
  decide +kernel

theorem seg_114 : seg 46 45 1 63982010368013 0 8192 933888 22557705109517 0 = true := by
  decide +kernel

theorem seg_115 : seg 46 45 1 27429808635917 0 8192 942080 63982010368013 0 = true := by
  decide +kernel

theorem seg_116 : seg 46 45 1 45410034909197 0 8192 950272 27429808635917 0 = true := by
  decide +kernel

theorem seg_117 : seg 46 45 1 52276731314189 0 8192 958464 45410034909197 0 = true := by
  decide +kernel

theorem seg_118 : seg 46 45 1 23396716904461 0 8192 966656 52276731314189 0 = true := by
  decide +kernel

theorem seg_119 : seg 46 45 1 16922171146253 0 8192 974848 23396716904461 0 = true := by
  decide +kernel

theorem path_chunk_14 : PathOK 46 45 1 917504 (57896159150093, 0) (16922171146253, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 37874514788365 0 8192 917504 57896159150093 0 seg_112) (seg_sound 46 45 1 22557705109517 0 8192 925696 37874514788365 0 seg_113)) (path_append (seg_sound 46 45 1 63982010368013 0 8192 933888 22557705109517 0 seg_114) (seg_sound 46 45 1 27429808635917 0 8192 942080 63982010368013 0 seg_115))) (path_append (path_append (seg_sound 46 45 1 45410034909197 0 8192 950272 27429808635917 0 seg_116) (seg_sound 46 45 1 52276731314189 0 8192 958464 45410034909197 0 seg_117)) (path_append (seg_sound 46 45 1 23396716904461 0 8192 966656 52276731314189 0 seg_118) (seg_sound 46 45 1 16922171146253 0 8192 974848 23396716904461 0 seg_119))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
