module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_120 : seg 46 45 1 29920235356173 0 8192 983040 16922171146253 0 = true := by
  decide +kernel

theorem seg_121 : seg 46 45 1 69304129159181 0 8192 991232 29920235356173 0 = true := by
  decide +kernel

theorem seg_122 : seg 46 45 1 14796044894221 0 8192 999424 69304129159181 0 = true := by
  decide +kernel

theorem seg_123 : seg 46 45 1 56274808995853 0 8192 1007616 14796044894221 0 = true := by
  decide +kernel

theorem seg_124 : seg 46 45 1 39414260563981 0 8192 1015808 56274808995853 0 = true := by
  decide +kernel

theorem seg_125 : seg 46 45 1 53255983857677 0 8192 1024000 39414260563981 0 = true := by
  decide +kernel

theorem seg_126 : seg 46 45 1 15545516687373 0 8192 1032192 53255983857677 0 = true := by
  decide +kernel

theorem seg_127 : seg 46 45 1 13194139533325 0 8192 1040384 15545516687373 0 = true := by
  decide +kernel

theorem path_chunk_15 : PathOK 46 45 1 983040 (16922171146253, 0) (13194139533325, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 29920235356173 0 8192 983040 16922171146253 0 seg_120) (seg_sound 46 45 1 69304129159181 0 8192 991232 29920235356173 0 seg_121)) (path_append (seg_sound 46 45 1 14796044894221 0 8192 999424 69304129159181 0 seg_122) (seg_sound 46 45 1 56274808995853 0 8192 1007616 14796044894221 0 seg_123))) (path_append (path_append (seg_sound 46 45 1 39414260563981 0 8192 1015808 56274808995853 0 seg_124) (seg_sound 46 45 1 53255983857677 0 8192 1024000 39414260563981 0 seg_125)) (path_append (seg_sound 46 45 1 15545516687373 0 8192 1032192 53255983857677 0 seg_126) (seg_sound 46 45 1 13194139533325 0 8192 1040384 15545516687373 0 seg_127))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
