module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_064 : seg 46 45 1 59624229175309 0 8192 524288 46729244180493 0 = true := by
  decide +kernel

theorem seg_065 : seg 46 45 1 52691195658253 0 8192 532480 59624229175309 0 = true := by
  decide +kernel

theorem seg_066 : seg 46 45 1 57762897723405 0 8192 540672 52691195658253 0 = true := by
  decide +kernel

theorem seg_067 : seg 46 45 1 22653805002765 0 8192 548864 57762897723405 0 = true := by
  decide +kernel

theorem seg_068 : seg 46 45 1 70114686795789 0 8192 557056 22653805002765 0 = true := by
  decide +kernel

theorem seg_069 : seg 46 45 1 64474438434829 0 8192 565248 70114686795789 0 = true := by
  decide +kernel

theorem seg_070 : seg 46 45 1 25149063561229 0 8192 573440 64474438434829 0 = true := by
  decide +kernel

theorem seg_071 : seg 46 45 1 45131516346381 0 8192 581632 25149063561229 0 = true := by
  decide +kernel

theorem path_chunk_08 : PathOK 46 45 1 524288 (46729244180493, 0) (45131516346381, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 59624229175309 0 8192 524288 46729244180493 0 seg_064) (seg_sound 46 45 1 52691195658253 0 8192 532480 59624229175309 0 seg_065)) (path_append (seg_sound 46 45 1 57762897723405 0 8192 540672 52691195658253 0 seg_066) (seg_sound 46 45 1 22653805002765 0 8192 548864 57762897723405 0 seg_067))) (path_append (path_append (seg_sound 46 45 1 70114686795789 0 8192 557056 22653805002765 0 seg_068) (seg_sound 46 45 1 64474438434829 0 8192 565248 70114686795789 0 seg_069)) (path_append (seg_sound 46 45 1 25149063561229 0 8192 573440 64474438434829 0 seg_070) (seg_sound 46 45 1 45131516346381 0 8192 581632 25149063561229 0 seg_071))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
