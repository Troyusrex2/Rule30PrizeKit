module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_144 : seg 46 45 1 43509511880717 0 8192 1179648 39341900431373 0 = true := by
  decide +kernel

theorem seg_145 : seg 46 45 1 55405614989325 0 8192 1187840 43509511880717 0 = true := by
  decide +kernel

theorem seg_146 : seg 46 45 1 35807024906253 0 8192 1196032 55405614989325 0 = true := by
  decide +kernel

theorem seg_147 : seg 46 45 1 23444078985229 0 8192 1204224 35807024906253 0 = true := by
  decide +kernel

theorem seg_148 : seg 46 45 1 31803578515469 0 8192 1212416 23444078985229 0 = true := by
  decide +kernel

theorem seg_149 : seg 46 45 1 15305652830221 0 8192 1220608 31803578515469 0 = true := by
  decide +kernel

theorem seg_150 : seg 46 45 1 1269045395469 0 8192 1228800 15305652830221 0 = true := by
  decide +kernel

theorem seg_151 : seg 46 45 1 59115929862157 0 8192 1236992 1269045395469 0 = true := by
  decide +kernel

theorem path_chunk_18 : PathOK 46 45 1 1179648 (39341900431373, 0) (59115929862157, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 43509511880717 0 8192 1179648 39341900431373 0 seg_144) (seg_sound 46 45 1 55405614989325 0 8192 1187840 43509511880717 0 seg_145)) (path_append (seg_sound 46 45 1 35807024906253 0 8192 1196032 55405614989325 0 seg_146) (seg_sound 46 45 1 23444078985229 0 8192 1204224 35807024906253 0 seg_147))) (path_append (path_append (seg_sound 46 45 1 31803578515469 0 8192 1212416 23444078985229 0 seg_148) (seg_sound 46 45 1 15305652830221 0 8192 1220608 31803578515469 0 seg_149)) (path_append (seg_sound 46 45 1 1269045395469 0 8192 1228800 15305652830221 0 seg_150) (seg_sound 46 45 1 59115929862157 0 8192 1236992 1269045395469 0 seg_151))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
