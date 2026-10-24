module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_152 : seg 46 45 1 61943511515149 0 8192 1245184 59115929862157 0 = true := by
  decide +kernel

theorem seg_153 : seg 46 45 1 18314277421069 0 8192 1253376 61943511515149 0 = true := by
  decide +kernel

theorem seg_154 : seg 46 45 1 18232018731021 0 8192 1261568 18314277421069 0 = true := by
  decide +kernel

theorem seg_155 : seg 46 45 1 3360811909133 0 8192 1269760 18232018731021 0 = true := by
  decide +kernel

theorem seg_156 : seg 46 45 1 30480728588301 0 8192 1277952 3360811909133 0 = true := by
  decide +kernel

theorem seg_157 : seg 46 45 1 38000260022285 0 8192 1286144 30480728588301 0 = true := by
  decide +kernel

theorem seg_158 : seg 46 45 1 40696845172749 0 8192 1294336 38000260022285 0 = true := by
  decide +kernel

theorem seg_159 : seg 46 45 1 24876450578445 0 8192 1302528 40696845172749 0 = true := by
  decide +kernel

theorem path_chunk_19 : PathOK 46 45 1 1245184 (59115929862157, 0) (24876450578445, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 61943511515149 0 8192 1245184 59115929862157 0 seg_152) (seg_sound 46 45 1 18314277421069 0 8192 1253376 61943511515149 0 seg_153)) (path_append (seg_sound 46 45 1 18232018731021 0 8192 1261568 18314277421069 0 seg_154) (seg_sound 46 45 1 3360811909133 0 8192 1269760 18232018731021 0 seg_155))) (path_append (path_append (seg_sound 46 45 1 30480728588301 0 8192 1277952 3360811909133 0 seg_156) (seg_sound 46 45 1 38000260022285 0 8192 1286144 30480728588301 0 seg_157)) (path_append (seg_sound 46 45 1 40696845172749 0 8192 1294336 38000260022285 0 seg_158) (seg_sound 46 45 1 24876450578445 0 8192 1302528 40696845172749 0 seg_159))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
