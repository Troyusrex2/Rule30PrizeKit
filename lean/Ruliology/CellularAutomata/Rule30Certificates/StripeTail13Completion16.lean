module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_128 : seg 46 45 1 43681310572557 0 8192 1048576 13194139533325 0 = true := by
  decide +kernel

theorem seg_129 : seg 46 45 1 53240951472141 0 8192 1056768 43681310572557 0 = true := by
  decide +kernel

theorem seg_130 : seg 46 45 1 38521444237325 0 8192 1064960 53240951472141 0 = true := by
  decide +kernel

theorem seg_131 : seg 46 45 1 48492328255501 0 8192 1073152 38521444237325 0 = true := by
  decide +kernel

theorem seg_132 : seg 46 45 1 5793256570893 0 8192 1081344 48492328255501 0 = true := by
  decide +kernel

theorem seg_133 : seg 46 45 1 49631031459853 0 8192 1089536 5793256570893 0 = true := by
  decide +kernel

theorem seg_134 : seg 46 45 1 13604191469581 0 8192 1097728 49631031459853 0 = true := by
  decide +kernel

theorem seg_135 : seg 46 45 1 69870527971341 0 8192 1105920 13604191469581 0 = true := by
  decide +kernel

theorem path_chunk_16 : PathOK 46 45 1 1048576 (13194139533325, 0) (69870527971341, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 43681310572557 0 8192 1048576 13194139533325 0 seg_128) (seg_sound 46 45 1 53240951472141 0 8192 1056768 43681310572557 0 seg_129)) (path_append (seg_sound 46 45 1 38521444237325 0 8192 1064960 53240951472141 0 seg_130) (seg_sound 46 45 1 48492328255501 0 8192 1073152 38521444237325 0 seg_131))) (path_append (path_append (seg_sound 46 45 1 5793256570893 0 8192 1081344 48492328255501 0 seg_132) (seg_sound 46 45 1 49631031459853 0 8192 1089536 5793256570893 0 seg_133)) (path_append (seg_sound 46 45 1 13604191469581 0 8192 1097728 49631031459853 0 seg_134) (seg_sound 46 45 1 69870527971341 0 8192 1105920 13604191469581 0 seg_135))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
