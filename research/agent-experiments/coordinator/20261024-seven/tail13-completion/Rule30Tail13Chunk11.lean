module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_088 : seg 46 45 1 22910848729101 0 8192 720896 64063732187149 0 = true := by
  decide +kernel

theorem seg_089 : seg 46 45 1 2371358818317 0 8192 729088 22910848729101 0 = true := by
  decide +kernel

theorem seg_090 : seg 46 45 1 30876402450445 0 8192 737280 2371358818317 0 = true := by
  decide +kernel

theorem seg_091 : seg 46 45 1 29199335161869 0 8192 745472 30876402450445 0 = true := by
  decide +kernel

theorem seg_092 : seg 46 45 1 57418763468813 0 8192 753664 29199335161869 0 = true := by
  decide +kernel

theorem seg_093 : seg 46 45 1 17659294908429 0 8192 761856 57418763468813 0 = true := by
  decide +kernel

theorem seg_094 : seg 46 45 1 3863205642253 0 8192 770048 17659294908429 0 = true := by
  decide +kernel

theorem seg_095 : seg 46 45 1 36421322670093 0 8192 778240 3863205642253 0 = true := by
  decide +kernel

theorem path_chunk_11 : PathOK 46 45 1 720896 (64063732187149, 0) (36421322670093, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 22910848729101 0 8192 720896 64063732187149 0 seg_088) (seg_sound 46 45 1 2371358818317 0 8192 729088 22910848729101 0 seg_089)) (path_append (seg_sound 46 45 1 30876402450445 0 8192 737280 2371358818317 0 seg_090) (seg_sound 46 45 1 29199335161869 0 8192 745472 30876402450445 0 seg_091))) (path_append (path_append (seg_sound 46 45 1 57418763468813 0 8192 753664 29199335161869 0 seg_092) (seg_sound 46 45 1 17659294908429 0 8192 761856 57418763468813 0 seg_093)) (path_append (seg_sound 46 45 1 3863205642253 0 8192 770048 17659294908429 0 seg_094) (seg_sound 46 45 1 36421322670093 0 8192 778240 3863205642253 0 seg_095))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
