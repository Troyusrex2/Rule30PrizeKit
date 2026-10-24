module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_224 : seg 46 45 1 66633615802381 0 8192 1835008 67207648247821 0 = true := by
  decide +kernel

theorem seg_225 : seg 46 45 1 3350611361805 0 8192 1843200 66633615802381 0 = true := by
  decide +kernel

theorem seg_226 : seg 46 45 1 30412545982477 0 8192 1851392 3350611361805 0 = true := by
  decide +kernel

theorem seg_227 : seg 46 45 1 35435627675661 0 8192 1859584 30412545982477 0 = true := by
  decide +kernel

theorem seg_228 : seg 46 45 1 61730910633997 0 8192 1867776 35435627675661 0 = true := by
  decide +kernel

theorem seg_229 : seg 46 45 1 8536784371725 0 8192 1875968 61730910633997 0 = true := by
  decide +kernel

theorem seg_230 : seg 46 45 1 11817485074445 0 8192 1884160 8536784371725 0 = true := by
  decide +kernel

theorem seg_231 : seg 46 45 1 56813827391501 0 8192 1892352 11817485074445 0 = true := by
  decide +kernel

theorem path_chunk_28 : PathOK 46 45 1 1835008 (67207648247821, 0) (56813827391501, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 66633615802381 0 8192 1835008 67207648247821 0 seg_224) (seg_sound 46 45 1 3350611361805 0 8192 1843200 66633615802381 0 seg_225)) (path_append (seg_sound 46 45 1 30412545982477 0 8192 1851392 3350611361805 0 seg_226) (seg_sound 46 45 1 35435627675661 0 8192 1859584 30412545982477 0 seg_227))) (path_append (path_append (seg_sound 46 45 1 61730910633997 0 8192 1867776 35435627675661 0 seg_228) (seg_sound 46 45 1 8536784371725 0 8192 1875968 61730910633997 0 seg_229)) (path_append (seg_sound 46 45 1 11817485074445 0 8192 1884160 8536784371725 0 seg_230) (seg_sound 46 45 1 56813827391501 0 8192 1892352 11817485074445 0 seg_231))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
