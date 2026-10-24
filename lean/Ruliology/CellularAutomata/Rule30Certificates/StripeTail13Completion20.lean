module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_160 : seg 46 45 1 113162321933 0 8192 1310720 24876450578445 0 = true := by
  decide +kernel

theorem seg_161 : seg 46 45 1 37985227636749 0 8192 1318912 113162321933 0 = true := by
  decide +kernel

theorem seg_162 : seg 46 45 1 23265720401933 0 8192 1327104 37985227636749 0 = true := by
  decide +kernel

theorem seg_163 : seg 46 45 1 41482941628429 0 8192 1335296 23265720401933 0 = true := by
  decide +kernel

theorem seg_164 : seg 46 45 1 27096294359053 0 8192 1343488 41482941628429 0 = true := by
  decide +kernel

theorem seg_165 : seg 46 45 1 5788005302285 0 8192 1351680 27096294359053 0 = true := by
  decide +kernel

theorem seg_166 : seg 46 45 1 11267729260557 0 8192 1359872 5788005302285 0 = true := by
  decide +kernel

theorem seg_167 : seg 46 45 1 5686536699917 0 8192 1368064 11267729260557 0 = true := by
  decide +kernel

theorem path_chunk_20 : PathOK 46 45 1 1310720 (24876450578445, 0) (5686536699917, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 113162321933 0 8192 1310720 24876450578445 0 seg_160) (seg_sound 46 45 1 37985227636749 0 8192 1318912 113162321933 0 seg_161)) (path_append (seg_sound 46 45 1 23265720401933 0 8192 1327104 37985227636749 0 seg_162) (seg_sound 46 45 1 41482941628429 0 8192 1335296 23265720401933 0 seg_163))) (path_append (path_append (seg_sound 46 45 1 27096294359053 0 8192 1343488 41482941628429 0 seg_164) (seg_sound 46 45 1 5788005302285 0 8192 1351680 27096294359053 0 seg_165)) (path_append (seg_sound 46 45 1 11267729260557 0 8192 1359872 5788005302285 0 seg_166) (seg_sound 46 45 1 5686536699917 0 8192 1368064 11267729260557 0 seg_167))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
