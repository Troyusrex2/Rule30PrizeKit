module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_240 : seg 46 45 1 59864747343885 0 8192 1966080 53498112638989 0 = true := by
  decide +kernel

theorem seg_241 : seg 46 45 1 9363565576205 0 8192 1974272 59864747343885 0 = true := by
  decide +kernel

theorem seg_242 : seg 46 45 1 68380056879117 0 8192 1982464 9363565576205 0 = true := by
  decide +kernel

theorem seg_243 : seg 46 45 1 31827855147021 0 8192 1990656 68380056879117 0 = true := by
  decide +kernel

theorem seg_244 : seg 46 45 1 49808081420301 0 8192 1998848 31827855147021 0 = true := by
  decide +kernel

theorem seg_245 : seg 46 45 1 65470870847501 0 8192 2007040 49808081420301 0 = true := by
  decide +kernel

theorem seg_246 : seg 46 45 1 62979135504397 0 8192 2015232 65470870847501 0 = true := by
  decide +kernel

theorem seg_247 : seg 46 45 1 12524124635149 0 8192 2023424 62979135504397 0 = true := by
  decide +kernel

theorem path_chunk_30 : PathOK 46 45 1 1966080 (53498112638989, 0) (12524124635149, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 59864747343885 0 8192 1966080 53498112638989 0 seg_240) (seg_sound 46 45 1 9363565576205 0 8192 1974272 59864747343885 0 seg_241)) (path_append (seg_sound 46 45 1 68380056879117 0 8192 1982464 9363565576205 0 seg_242) (seg_sound 46 45 1 31827855147021 0 8192 1990656 68380056879117 0 seg_243))) (path_append (path_append (seg_sound 46 45 1 49808081420301 0 8192 1998848 31827855147021 0 seg_244) (seg_sound 46 45 1 65470870847501 0 8192 2007040 49808081420301 0 seg_245)) (path_append (seg_sound 46 45 1 62979135504397 0 8192 2015232 65470870847501 0 seg_246) (seg_sound 46 45 1 12524124635149 0 8192 2023424 62979135504397 0 seg_247))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
