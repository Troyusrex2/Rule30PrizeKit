module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_248 : seg 46 45 1 43114374889485 0 8192 2031616 12524124635149 0 = true := by
  decide +kernel

theorem seg_249 : seg 46 45 1 20925617537037 0 8192 2039808 43114374889485 0 = true := by
  decide +kernel

theorem seg_250 : seg 46 45 1 27990184427533 0 8192 2048000 20925617537037 0 = true := by
  decide +kernel

theorem seg_251 : seg 46 45 1 51876762484749 0 8192 2056192 27990184427533 0 = true := by
  decide +kernel

theorem seg_252 : seg 46 45 1 26220121030669 0 8192 2064384 51876762484749 0 = true := by
  decide +kernel

theorem seg_253 : seg 46 45 1 66450123390989 0 8192 2072576 26220121030669 0 = true := by
  decide +kernel

theorem seg_254 : seg 46 45 1 28739656220685 0 8192 2080768 66450123390989 0 = true := by
  decide +kernel

theorem seg_255 : seg 46 45 1 13 0 8192 2088960 28739656220685 0 = true := by
  decide +kernel

theorem path_chunk_31 : PathOK 46 45 1 2031616 (12524124635149, 0) (13, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 43114374889485 0 8192 2031616 12524124635149 0 seg_248) (seg_sound 46 45 1 20925617537037 0 8192 2039808 43114374889485 0 seg_249)) (path_append (seg_sound 46 45 1 27990184427533 0 8192 2048000 20925617537037 0 seg_250) (seg_sound 46 45 1 51876762484749 0 8192 2056192 27990184427533 0 seg_251))) (path_append (path_append (seg_sound 46 45 1 26220121030669 0 8192 2064384 51876762484749 0 seg_252) (seg_sound 46 45 1 66450123390989 0 8192 2072576 26220121030669 0 seg_253)) (path_append (seg_sound 46 45 1 28739656220685 0 8192 2080768 66450123390989 0 seg_254) (seg_sound 46 45 1 13 0 8192 2088960 28739656220685 0 seg_255))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
