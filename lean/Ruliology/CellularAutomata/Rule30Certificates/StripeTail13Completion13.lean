module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_104 : seg 46 45 1 35864470093837 0 8192 851968 43619687858189 0 = true := by
  decide +kernel

theorem seg_105 : seg 46 45 1 37246493261837 0 8192 860160 35864470093837 0 = true := by
  decide +kernel

theorem seg_106 : seg 46 45 1 58604711313421 0 8192 868352 37246493261837 0 = true := by
  decide +kernel

theorem seg_107 : seg 46 45 1 24079734145037 0 8192 876544 58604711313421 0 = true := by
  decide +kernel

theorem seg_108 : seg 46 45 1 5982235131917 0 8192 884736 24079734145037 0 = true := by
  decide +kernel

theorem seg_109 : seg 46 45 1 3468722962445 0 8192 892928 5982235131917 0 = true := by
  decide +kernel

theorem seg_110 : seg 46 45 1 62240401129485 0 8192 901120 3468722962445 0 = true := by
  decide +kernel

theorem seg_111 : seg 46 45 1 57896159150093 0 8192 909312 62240401129485 0 = true := by
  decide +kernel

theorem path_chunk_13 : PathOK 46 45 1 851968 (43619687858189, 0) (57896159150093, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 35864470093837 0 8192 851968 43619687858189 0 seg_104) (seg_sound 46 45 1 37246493261837 0 8192 860160 35864470093837 0 seg_105)) (path_append (seg_sound 46 45 1 58604711313421 0 8192 868352 37246493261837 0 seg_106) (seg_sound 46 45 1 24079734145037 0 8192 876544 58604711313421 0 seg_107))) (path_append (path_append (seg_sound 46 45 1 5982235131917 0 8192 884736 24079734145037 0 seg_108) (seg_sound 46 45 1 3468722962445 0 8192 892928 5982235131917 0 seg_109)) (path_append (seg_sound 46 45 1 62240401129485 0 8192 901120 3468722962445 0 seg_110) (seg_sound 46 45 1 57896159150093 0 8192 909312 62240401129485 0 seg_111))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
