module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_216 : seg 46 45 1 62493267329037 0 8192 1769472 15685220565005 0 = true := by
  decide +kernel

theorem seg_217 : seg 46 45 1 24361591373837 0 8192 1777664 62493267329037 0 = true := by
  decide +kernel

theorem seg_218 : seg 46 45 1 26478355939341 0 8192 1785856 24361591373837 0 = true := by
  decide +kernel

theorem seg_219 : seg 46 45 1 42393474695181 0 8192 1794048 26478355939341 0 = true := by
  decide +kernel

theorem seg_220 : seg 46 45 1 61816809979917 0 8192 1802240 42393474695181 0 = true := by
  decide +kernel

theorem seg_221 : seg 46 45 1 13261248397325 0 8192 1810432 61816809979917 0 = true := by
  decide +kernel

theorem seg_222 : seg 46 45 1 17057345175565 0 8192 1818624 13261248397325 0 = true := by
  decide +kernel

theorem seg_223 : seg 46 45 1 67207648247821 0 8192 1826816 17057345175565 0 = true := by
  decide +kernel

theorem path_chunk_27 : PathOK 46 45 1 1769472 (15685220565005, 0) (67207648247821, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 62493267329037 0 8192 1769472 15685220565005 0 seg_216) (seg_sound 46 45 1 24361591373837 0 8192 1777664 62493267329037 0 seg_217)) (path_append (seg_sound 46 45 1 26478355939341 0 8192 1785856 24361591373837 0 seg_218) (seg_sound 46 45 1 42393474695181 0 8192 1794048 26478355939341 0 seg_219))) (path_append (path_append (seg_sound 46 45 1 61816809979917 0 8192 1802240 42393474695181 0 seg_220) (seg_sound 46 45 1 13261248397325 0 8192 1810432 61816809979917 0 seg_221)) (path_append (seg_sound 46 45 1 17057345175565 0 8192 1818624 13261248397325 0 seg_222) (seg_sound 46 45 1 67207648247821 0 8192 1826816 17057345175565 0 seg_223))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
