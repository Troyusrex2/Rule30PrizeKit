module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_016 : seg 46 45 1 3927093280781 0 8192 131072 34943853920269 0 = true := by
  decide +kernel

theorem seg_017 : seg 46 45 1 59803661500429 0 8192 139264 3927093280781 0 = true := by
  decide +kernel

theorem seg_018 : seg 46 45 1 31408978395149 0 8192 147456 59803661500429 0 = true := by
  decide +kernel

theorem seg_019 : seg 46 45 1 19046032474125 0 8192 155648 31408978395149 0 = true := by
  decide +kernel

theorem seg_020 : seg 46 45 1 36201625026573 0 8192 163840 19046032474125 0 = true := by
  decide +kernel

theorem seg_021 : seg 46 45 1 2111513296909 0 8192 172032 36201625026573 0 = true := by
  decide +kernel

theorem seg_022 : seg 46 45 1 67239743062029 0 8192 180224 2111513296909 0 = true := by
  decide +kernel

theorem seg_023 : seg 46 45 1 37125697306637 0 8192 188416 67239743062029 0 = true := by
  decide +kernel

theorem path_chunk_02 : PathOK 46 45 1 131072 (34943853920269, 0) (37125697306637, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 3927093280781 0 8192 131072 34943853920269 0 seg_016) (seg_sound 46 45 1 59803661500429 0 8192 139264 3927093280781 0 seg_017)) (path_append (seg_sound 46 45 1 31408978395149 0 8192 147456 59803661500429 0 seg_018) (seg_sound 46 45 1 19046032474125 0 8192 155648 31408978395149 0 seg_019))) (path_append (path_append (seg_sound 46 45 1 36201625026573 0 8192 163840 19046032474125 0 seg_020) (seg_sound 46 45 1 2111513296909 0 8192 172032 36201625026573 0 seg_021)) (path_append (seg_sound 46 45 1 67239743062029 0 8192 180224 2111513296909 0 seg_022) (seg_sound 46 45 1 37125697306637 0 8192 188416 67239743062029 0 seg_023))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
