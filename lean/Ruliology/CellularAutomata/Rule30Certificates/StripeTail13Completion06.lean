module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_048 : seg 46 45 1 13135503163405 0 8192 393216 33157147525133 0 = true := by
  decide +kernel

theorem seg_049 : seg 46 45 1 23107460923405 0 8192 401408 13135503163405 0 = true := by
  decide +kernel

theorem seg_050 : seg 46 45 1 50238115020813 0 8192 409600 23107460923405 0 = true := by
  decide +kernel

theorem seg_051 : seg 46 45 1 7088843522061 0 8192 417792 50238115020813 0 = true := by
  decide +kernel

theorem seg_052 : seg 46 45 1 67950023278605 0 8192 425984 7088843522061 0 = true := by
  decide +kernel

theorem seg_053 : seg 46 45 1 1149440622605 0 8192 434176 67950023278605 0 = true := by
  decide +kernel

theorem seg_054 : seg 46 45 1 21747449462797 0 8192 442368 1149440622605 0 = true := by
  decide +kernel

theorem seg_055 : seg 46 45 1 35064113004557 0 8192 450560 21747449462797 0 = true := by
  decide +kernel

theorem path_chunk_06 : PathOK 46 45 1 393216 (33157147525133, 0) (35064113004557, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 13135503163405 0 8192 393216 33157147525133 0 seg_048) (seg_sound 46 45 1 23107460923405 0 8192 401408 13135503163405 0 seg_049)) (path_append (seg_sound 46 45 1 50238115020813 0 8192 409600 23107460923405 0 seg_050) (seg_sound 46 45 1 7088843522061 0 8192 417792 50238115020813 0 seg_051))) (path_append (path_append (seg_sound 46 45 1 67950023278605 0 8192 425984 7088843522061 0 seg_052) (seg_sound 46 45 1 1149440622605 0 8192 434176 67950023278605 0 seg_053)) (path_append (seg_sound 46 45 1 21747449462797 0 8192 442368 1149440622605 0 seg_054) (seg_sound 46 45 1 35064113004557 0 8192 450560 21747449462797 0 seg_055))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
