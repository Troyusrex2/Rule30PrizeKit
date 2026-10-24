module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_136 : seg 46 45 1 21433379979277 0 8192 1114112 69870527971341 0 = true := by
  decide +kernel

theorem seg_137 : seg 46 45 1 19241990357005 0 8192 1122304 21433379979277 0 = true := by
  decide +kernel

theorem seg_138 : seg 46 45 1 17510464225293 0 8192 1130496 19241990357005 0 = true := by
  decide +kernel

theorem seg_139 : seg 46 45 1 31913754492941 0 8192 1138688 17510464225293 0 = true := by
  decide +kernel

theorem seg_140 : seg 46 45 1 50649895010317 0 8192 1146880 31913754492941 0 = true := by
  decide +kernel

theorem seg_141 : seg 46 45 1 63804423536653 0 8192 1155072 50649895010317 0 = true := by
  decide +kernel

theorem seg_142 : seg 46 45 1 53856624967693 0 8192 1163264 63804423536653 0 = true := by
  decide +kernel

theorem seg_143 : seg 46 45 1 39341900431373 0 8192 1171456 53856624967693 0 = true := by
  decide +kernel

theorem path_chunk_17 : PathOK 46 45 1 1114112 (69870527971341, 0) (39341900431373, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 21433379979277 0 8192 1114112 69870527971341 0 seg_136) (seg_sound 46 45 1 19241990357005 0 8192 1122304 21433379979277 0 seg_137)) (path_append (seg_sound 46 45 1 17510464225293 0 8192 1130496 19241990357005 0 seg_138) (seg_sound 46 45 1 31913754492941 0 8192 1138688 17510464225293 0 seg_139))) (path_append (path_append (seg_sound 46 45 1 50649895010317 0 8192 1146880 31913754492941 0 seg_140) (seg_sound 46 45 1 63804423536653 0 8192 1155072 50649895010317 0 seg_141)) (path_append (seg_sound 46 45 1 53856624967693 0 8192 1163264 63804423536653 0 seg_142) (seg_sound 46 45 1 39341900431373 0 8192 1171456 53856624967693 0 seg_143))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
