module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_056 : seg 46 45 1 7380246986765 0 8192 458752 35064113004557 0 = true := by
  decide +kernel

theorem seg_057 : seg 46 45 1 57759257067533 0 8192 466944 7380246986765 0 = true := by
  decide +kernel

theorem seg_058 : seg 46 45 1 36236521635853 0 8192 475136 57759257067533 0 = true := by
  decide +kernel

theorem seg_059 : seg 46 45 1 64521146204173 0 8192 483328 36236521635853 0 = true := by
  decide +kernel

theorem seg_060 : seg 46 45 1 48760109400077 0 8192 491520 64521146204173 0 = true := by
  decide +kernel

theorem seg_061 : seg 46 45 1 68099390832653 0 8192 499712 48760109400077 0 = true := by
  decide +kernel

theorem seg_062 : seg 46 45 1 18294295756813 0 8192 507904 68099390832653 0 = true := by
  decide +kernel

theorem seg_063 : seg 46 45 1 46729244180493 0 8192 516096 18294295756813 0 = true := by
  decide +kernel

theorem path_chunk_07 : PathOK 46 45 1 458752 (35064113004557, 0) (46729244180493, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 7380246986765 0 8192 458752 35064113004557 0 seg_056) (seg_sound 46 45 1 57759257067533 0 8192 466944 7380246986765 0 seg_057)) (path_append (seg_sound 46 45 1 36236521635853 0 8192 475136 57759257067533 0 seg_058) (seg_sound 46 45 1 64521146204173 0 8192 483328 36236521635853 0 seg_059))) (path_append (path_append (seg_sound 46 45 1 48760109400077 0 8192 491520 64521146204173 0 seg_060) (seg_sound 46 45 1 68099390832653 0 8192 499712 48760109400077 0 seg_061)) (path_append (seg_sound 46 45 1 18294295756813 0 8192 507904 68099390832653 0 seg_062) (seg_sound 46 45 1 46729244180493 0 8192 516096 18294295756813 0 seg_063))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
