module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_032 : seg 46 45 1 30899487899661 0 8192 262144 29274497089549 0 = true := by
  decide +kernel

theorem seg_033 : seg 46 45 1 24791088103437 0 8192 270336 30899487899661 0 = true := by
  decide +kernel

theorem seg_034 : seg 46 45 1 62848139001869 0 8192 278528 24791088103437 0 = true := by
  decide +kernel

theorem seg_035 : seg 46 45 1 45880988139533 0 8192 286720 62848139001869 0 = true := by
  decide +kernel

theorem seg_036 : seg 46 45 1 22698247847949 0 8192 294912 45880988139533 0 = true := by
  decide +kernel

theorem seg_037 : seg 46 45 1 1389958791181 0 8192 303104 22698247847949 0 = true := by
  decide +kernel

theorem seg_038 : seg 46 45 1 6869682749453 0 8192 311296 1389958791181 0 = true := by
  decide +kernel

theorem seg_039 : seg 46 45 1 36472862277645 0 8192 319488 6869682749453 0 = true := by
  decide +kernel

theorem path_chunk_04 : PathOK 46 45 1 262144 (29274497089549, 0) (36472862277645, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 30899487899661 0 8192 262144 29274497089549 0 seg_032) (seg_sound 46 45 1 24791088103437 0 8192 270336 30899487899661 0 seg_033)) (path_append (seg_sound 46 45 1 62848139001869 0 8192 278528 24791088103437 0 seg_034) (seg_sound 46 45 1 45880988139533 0 8192 286720 62848139001869 0 seg_035))) (path_append (path_append (seg_sound 46 45 1 22698247847949 0 8192 294912 45880988139533 0 seg_036) (seg_sound 46 45 1 1389958791181 0 8192 303104 22698247847949 0 seg_037)) (path_append (seg_sound 46 45 1 6869682749453 0 8192 311296 1389958791181 0 seg_038) (seg_sound 46 45 1 36472862277645 0 8192 319488 6869682749453 0 seg_039))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
