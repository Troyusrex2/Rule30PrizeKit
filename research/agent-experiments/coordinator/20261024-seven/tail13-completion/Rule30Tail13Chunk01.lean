module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_008 : seg 46 45 1 34627519512589 0 8192 65536 30288109371405 0 = true := by
  decide +kernel

theorem seg_009 : seg 46 45 1 6047850823693 0 8192 73728 34627519512589 0 = true := by
  decide +kernel

theorem seg_010 : seg 46 45 1 48296789803021 0 8192 81920 6047850823693 0 = true := by
  decide +kernel

theorem seg_011 : seg 46 45 1 1127428915213 0 8192 90112 48296789803021 0 = true := by
  decide +kernel

theorem seg_012 : seg 46 45 1 55047941521421 0 8192 98304 1127428915213 0 = true := by
  decide +kernel

theorem seg_013 : seg 46 45 1 33018097958925 0 8192 106496 55047941521421 0 = true := by
  decide +kernel

theorem seg_014 : seg 46 45 1 58254671478797 0 8192 114688 33018097958925 0 = true := by
  decide +kernel

theorem seg_015 : seg 46 45 1 34943853920269 0 8192 122880 58254671478797 0 = true := by
  decide +kernel

theorem path_chunk_01 : PathOK 46 45 1 65536 (30288109371405, 0) (34943853920269, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 34627519512589 0 8192 65536 30288109371405 0 seg_008) (seg_sound 46 45 1 6047850823693 0 8192 73728 34627519512589 0 seg_009)) (path_append (seg_sound 46 45 1 48296789803021 0 8192 81920 6047850823693 0 seg_010) (seg_sound 46 45 1 1127428915213 0 8192 90112 48296789803021 0 seg_011))) (path_append (path_append (seg_sound 46 45 1 55047941521421 0 8192 98304 1127428915213 0 seg_012) (seg_sound 46 45 1 33018097958925 0 8192 106496 55047941521421 0 seg_013)) (path_append (seg_sound 46 45 1 58254671478797 0 8192 114688 33018097958925 0 seg_014) (seg_sound 46 45 1 34943853920269 0 8192 122880 58254671478797 0 seg_015))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
