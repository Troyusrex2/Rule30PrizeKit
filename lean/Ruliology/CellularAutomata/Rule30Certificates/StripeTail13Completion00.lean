module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_000 : seg 46 45 1 4098891972621 0 8192 0 13 0 = true := by
  decide +kernel

theorem seg_001 : seg 46 45 1 40046811938829 0 8192 8192 4098891972621 0 = true := by
  decide +kernel

theorem seg_002 : seg 46 45 1 34123397726221 0 8192 16384 40046811938829 0 = true := by
  decide +kernel

theorem seg_003 : seg 46 45 1 44094281744397 0 8192 24576 34123397726221 0 = true := by
  decide +kernel

theorem seg_004 : seg 46 45 1 62967861215245 0 8192 32768 44094281744397 0 = true := by
  decide +kernel

theorem seg_005 : seg 46 45 1 62825170993165 0 8192 40960 62967861215245 0 = true := by
  decide +kernel

theorem seg_006 : seg 46 45 1 35594424025101 0 8192 49152 62825170993165 0 = true := by
  decide +kernel

theorem seg_007 : seg 46 45 1 30288109371405 0 8192 57344 35594424025101 0 = true := by
  decide +kernel

theorem path_chunk_00 : PathOK 46 45 1 0 (13, 0) (30288109371405, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 4098891972621 0 8192 0 13 0 seg_000) (seg_sound 46 45 1 40046811938829 0 8192 8192 4098891972621 0 seg_001)) (path_append (seg_sound 46 45 1 34123397726221 0 8192 16384 40046811938829 0 seg_002) (seg_sound 46 45 1 44094281744397 0 8192 24576 34123397726221 0 seg_003))) (path_append (path_append (seg_sound 46 45 1 62967861215245 0 8192 32768 44094281744397 0 seg_004) (seg_sound 46 45 1 62825170993165 0 8192 40960 62967861215245 0 seg_005)) (path_append (seg_sound 46 45 1 35594424025101 0 8192 49152 62825170993165 0 seg_006) (seg_sound 46 45 1 30288109371405 0 8192 57344 35594424025101 0 seg_007))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
