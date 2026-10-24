module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_192 : seg 46 45 1 2449624530957 0 8192 1572864 51127290691597 0 = true := by
  decide +kernel

theorem seg_193 : seg 46 45 1 48293149147149 0 8192 1581056 2449624530957 0 = true := by
  decide +kernel

theorem seg_194 : seg 46 45 1 588293079053 0 8192 1589248 48293149147149 0 = true := by
  decide +kernel

theorem seg_195 : seg 46 45 1 9459665469453 0 8192 1597440 588293079053 0 = true := by
  decide +kernel

theorem seg_196 : seg 46 45 1 12940082151437 0 8192 1605632 9459665469453 0 = true := by
  decide +kernel

theorem seg_197 : seg 46 45 1 68872484945933 0 8192 1613824 12940082151437 0 = true := by
  decide +kernel

theorem seg_198 : seg 46 45 1 47139296116749 0 8192 1622016 68872484945933 0 = true := by
  decide +kernel

theorem seg_199 : seg 46 45 1 58325655879693 0 8192 1630208 47139296116749 0 = true := by
  decide +kernel

theorem path_chunk_24 : PathOK 46 45 1 1572864 (51127290691597, 0) (58325655879693, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 2449624530957 0 8192 1572864 51127290691597 0 seg_192) (seg_sound 46 45 1 48293149147149 0 8192 1581056 2449624530957 0 seg_193)) (path_append (seg_sound 46 45 1 588293079053 0 8192 1589248 48293149147149 0 seg_194) (seg_sound 46 45 1 9459665469453 0 8192 1597440 588293079053 0 seg_195))) (path_append (path_append (seg_sound 46 45 1 12940082151437 0 8192 1605632 9459665469453 0 seg_196) (seg_sound 46 45 1 68872484945933 0 8192 1613824 12940082151437 0 seg_197)) (path_append (seg_sound 46 45 1 47139296116749 0 8192 1622016 68872484945933 0 seg_198) (seg_sound 46 45 1 58325655879693 0 8192 1630208 47139296116749 0 seg_199))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
