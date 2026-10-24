module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_024 : seg 46 45 1 22361092915213 0 8192 196608 37125697306637 0 = true := by
  decide +kernel

theorem seg_025 : seg 46 45 1 31508416954381 0 8192 204800 22361092915213 0 = true := by
  decide +kernel

theorem seg_026 : seg 46 45 1 22630065242125 0 8192 212992 31508416954381 0 = true := by
  decide +kernel

theorem seg_027 : seg 46 45 1 7758858420237 0 8192 221184 22630065242125 0 = true := by
  decide +kernel

theorem seg_028 : seg 46 45 1 8490496032781 0 8192 229376 7758858420237 0 = true := by
  decide +kernel

theorem seg_029 : seg 46 45 1 42398306533389 0 8192 237568 8490496032781 0 = true := by
  decide +kernel

theorem seg_030 : seg 46 45 1 18706612617229 0 8192 245760 42398306533389 0 = true := by
  decide +kernel

theorem seg_031 : seg 46 45 1 29274497089549 0 8192 253952 18706612617229 0 = true := by
  decide +kernel

theorem path_chunk_03 : PathOK 46 45 1 196608 (37125697306637, 0) (29274497089549, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 22361092915213 0 8192 196608 37125697306637 0 seg_024) (seg_sound 46 45 1 31508416954381 0 8192 204800 22361092915213 0 seg_025)) (path_append (seg_sound 46 45 1 22630065242125 0 8192 212992 31508416954381 0 seg_026) (seg_sound 46 45 1 7758858420237 0 8192 221184 22630065242125 0 seg_027))) (path_append (path_append (seg_sound 46 45 1 8490496032781 0 8192 229376 7758858420237 0 seg_028) (seg_sound 46 45 1 42398306533389 0 8192 237568 8490496032781 0 seg_029)) (path_append (seg_sound 46 45 1 18706612617229 0 8192 245760 42398306533389 0 seg_030) (seg_sound 46 45 1 29274497089549 0 8192 253952 18706612617229 0 seg_031))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
