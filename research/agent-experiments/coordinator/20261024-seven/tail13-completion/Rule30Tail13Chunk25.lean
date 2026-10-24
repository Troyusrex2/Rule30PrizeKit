module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_200 : seg 46 45 1 48371414859789 0 8192 1638400 58325655879693 0 = true := by
  decide +kernel

theorem seg_201 : seg 46 45 1 24189792681997 0 8192 1646592 48371414859789 0 = true := by
  decide +kernel

theorem seg_202 : seg 46 45 1 58742150266893 0 8192 1654784 24189792681997 0 = true := by
  decide +kernel

theorem seg_203 : seg 46 45 1 24766928912397 0 8192 1662976 58742150266893 0 = true := by
  decide +kernel

theorem seg_204 : seg 46 45 1 61095255474189 0 8192 1671168 24766928912397 0 = true := by
  decide +kernel

theorem seg_205 : seg 46 45 1 47861504933901 0 8192 1679360 61095255474189 0 = true := by
  decide +kernel

theorem seg_206 : seg 46 45 1 36814194737165 0 8192 1687552 47861504933901 0 = true := by
  decide +kernel

theorem seg_207 : seg 46 45 1 49787260895245 0 8192 1695744 36814194737165 0 = true := by
  decide +kernel

theorem path_chunk_25 : PathOK 46 45 1 1638400 (58325655879693, 0) (49787260895245, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 48371414859789 0 8192 1638400 58325655879693 0 seg_200) (seg_sound 46 45 1 24189792681997 0 8192 1646592 48371414859789 0 seg_201)) (path_append (seg_sound 46 45 1 58742150266893 0 8192 1654784 24189792681997 0 seg_202) (seg_sound 46 45 1 24766928912397 0 8192 1662976 58742150266893 0 seg_203))) (path_append (path_append (seg_sound 46 45 1 61095255474189 0 8192 1671168 24766928912397 0 seg_204) (seg_sound 46 45 1 47861504933901 0 8192 1679360 61095255474189 0 seg_205)) (path_append (seg_sound 46 45 1 36814194737165 0 8192 1687552 47861504933901 0 seg_206) (seg_sound 46 45 1 49787260895245 0 8192 1695744 36814194737165 0 seg_207))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
