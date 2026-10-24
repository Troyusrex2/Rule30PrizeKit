module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_208 : seg 46 45 1 27566593277965 0 8192 1703936 49787260895245 0 = true := by
  decide +kernel

theorem seg_209 : seg 46 45 1 14173928947725 0 8192 1712128 27566593277965 0 = true := by
  decide +kernel

theorem seg_210 : seg 46 45 1 27560687697933 0 8192 1720320 14173928947725 0 = true := by
  decide +kernel

theorem seg_211 : seg 46 45 1 14098230149133 0 8192 1728512 27560687697933 0 = true := by
  decide +kernel

theorem seg_212 : seg 46 45 1 2666520379405 0 8192 1736704 14098230149133 0 = true := by
  decide +kernel

theorem seg_213 : seg 46 45 1 44442710966285 0 8192 1744896 2666520379405 0 = true := by
  decide +kernel

theorem seg_214 : seg 46 45 1 29306591903757 0 8192 1753088 44442710966285 0 = true := by
  decide +kernel

theorem seg_215 : seg 46 45 1 15685220565005 0 8192 1761280 29306591903757 0 = true := by
  decide +kernel

theorem path_chunk_26 : PathOK 46 45 1 1703936 (49787260895245, 0) (15685220565005, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 27566593277965 0 8192 1703936 49787260895245 0 seg_208) (seg_sound 46 45 1 14173928947725 0 8192 1712128 27566593277965 0 seg_209)) (path_append (seg_sound 46 45 1 27560687697933 0 8192 1720320 14173928947725 0 seg_210) (seg_sound 46 45 1 14098230149133 0 8192 1728512 27560687697933 0 seg_211))) (path_append (path_append (seg_sound 46 45 1 2666520379405 0 8192 1736704 14098230149133 0 seg_212) (seg_sound 46 45 1 44442710966285 0 8192 1744896 2666520379405 0 seg_213)) (path_append (seg_sound 46 45 1 29306591903757 0 8192 1753088 44442710966285 0 seg_214) (seg_sound 46 45 1 15685220565005 0 8192 1761280 29306591903757 0 seg_215))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
