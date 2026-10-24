module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_072 : seg 46 45 1 70361647415309 0 8192 589824 45131516346381 0 = true := by
  decide +kernel

theorem seg_073 : seg 46 45 1 19791746170893 0 8192 598016 70361647415309 0 = true := by
  decide +kernel

theorem seg_074 : seg 46 45 1 19159731666957 0 8192 606208 19791746170893 0 = true := by
  decide +kernel

theorem seg_075 : seg 46 45 1 20368882401293 0 8192 614400 19159731666957 0 = true := by
  decide +kernel

theorem seg_076 : seg 46 45 1 56697208963085 0 8192 622592 20368882401293 0 = true := by
  decide +kernel

theorem seg_077 : seg 46 45 1 52259551445005 0 8192 630784 56697208963085 0 = true := by
  decide +kernel

theorem seg_078 : seg 46 45 1 6027869159437 0 8192 638976 52259551445005 0 = true := by
  decide +kernel

theorem seg_079 : seg 46 45 1 54185307406349 0 8192 647168 6027869159437 0 = true := by
  decide +kernel

theorem path_chunk_09 : PathOK 46 45 1 589824 (45131516346381, 0) (54185307406349, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 70361647415309 0 8192 589824 45131516346381 0 seg_072) (seg_sound 46 45 1 19791746170893 0 8192 598016 70361647415309 0 seg_073)) (path_append (seg_sound 46 45 1 19159731666957 0 8192 606208 19791746170893 0 seg_074) (seg_sound 46 45 1 20368882401293 0 8192 614400 19159731666957 0 seg_075))) (path_append (path_append (seg_sound 46 45 1 56697208963085 0 8192 622592 20368882401293 0 seg_076) (seg_sound 46 45 1 52259551445005 0 8192 630784 56697208963085 0 seg_077)) (path_append (seg_sound 46 45 1 6027869159437 0 8192 638976 52259551445005 0 seg_078) (seg_sound 46 45 1 54185307406349 0 8192 647168 6027869159437 0 seg_079))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
