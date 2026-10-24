module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_080 : seg 46 45 1 5576360722445 0 8192 655360 54185307406349 0 = true := by
  decide +kernel

theorem seg_081 : seg 46 45 1 53756347547661 0 8192 663552 5576360722445 0 = true := by
  decide +kernel

theorem seg_082 : seg 46 45 1 58347013275661 0 8192 671744 53756347547661 0 = true := by
  decide +kernel

theorem seg_083 : seg 46 45 1 27292369682445 0 8192 679936 58347013275661 0 = true := by
  decide +kernel

theorem seg_084 : seg 46 45 1 33452845957133 0 8192 688128 27292369682445 0 = true := by
  decide +kernel

theorem seg_085 : seg 46 45 1 40044664455181 0 8192 696320 33452845957133 0 = true := by
  decide +kernel

theorem seg_086 : seg 46 45 1 68889010503693 0 8192 704512 40044664455181 0 = true := by
  decide +kernel

theorem seg_087 : seg 46 45 1 64063732187149 0 8192 712704 68889010503693 0 = true := by
  decide +kernel

theorem path_chunk_10 : PathOK 46 45 1 655360 (54185307406349, 0) (64063732187149, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 5576360722445 0 8192 655360 54185307406349 0 seg_080) (seg_sound 46 45 1 53756347547661 0 8192 663552 5576360722445 0 seg_081)) (path_append (seg_sound 46 45 1 58347013275661 0 8192 671744 53756347547661 0 seg_082) (seg_sound 46 45 1 27292369682445 0 8192 679936 58347013275661 0 seg_083))) (path_append (path_append (seg_sound 46 45 1 33452845957133 0 8192 688128 27292369682445 0 seg_084) (seg_sound 46 45 1 40044664455181 0 8192 696320 33452845957133 0 seg_085)) (path_append (seg_sound 46 45 1 68889010503693 0 8192 704512 40044664455181 0 seg_086) (seg_sound 46 45 1 64063732187149 0 8192 712704 68889010503693 0 seg_087))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
