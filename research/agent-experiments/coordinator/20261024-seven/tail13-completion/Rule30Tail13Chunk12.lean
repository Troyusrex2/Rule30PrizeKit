module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_096 : seg 46 45 1 35847290224653 0 8192 786432 36421322670093 0 = true := by
  decide +kernel

theorem seg_097 : seg 46 45 1 51729122983949 0 8192 794624 35847290224653 0 = true := by
  decide +kernel

theorem seg_098 : seg 46 45 1 17218406449165 0 8192 802816 51729122983949 0 = true := by
  decide +kernel

theorem seg_099 : seg 46 45 1 66221953253389 0 8192 811008 17218406449165 0 = true := by
  decide +kernel

theorem seg_100 : seg 46 45 1 4556305989645 0 8192 819200 66221953253389 0 = true := by
  decide +kernel

theorem seg_101 : seg 46 45 1 56915295993869 0 8192 827392 4556305989645 0 = true := by
  decide +kernel

theorem seg_102 : seg 46 45 1 16215531585549 0 8192 835584 56915295993869 0 = true := by
  decide +kernel

theorem seg_103 : seg 46 45 1 43619687858189 0 8192 843776 16215531585549 0 = true := by
  decide +kernel

theorem path_chunk_12 : PathOK 46 45 1 786432 (36421322670093, 0) (43619687858189, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 35847290224653 0 8192 786432 36421322670093 0 seg_096) (seg_sound 46 45 1 51729122983949 0 8192 794624 35847290224653 0 seg_097)) (path_append (seg_sound 46 45 1 17218406449165 0 8192 802816 51729122983949 0 seg_098) (seg_sound 46 45 1 66221953253389 0 8192 811008 17218406449165 0 seg_099))) (path_append (path_append (seg_sound 46 45 1 4556305989645 0 8192 819200 66221953253389 0 seg_100) (seg_sound 46 45 1 56915295993869 0 8192 827392 4556305989645 0 seg_101)) (path_append (seg_sound 46 45 1 16215531585549 0 8192 835584 56915295993869 0 seg_102) (seg_sound 46 45 1 43619687858189 0 8192 843776 16215531585549 0 seg_103))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
