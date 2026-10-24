module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_040 : seg 46 45 1 27618132885517 0 8192 327680 36472862277645 0 = true := by
  decide +kernel

theorem seg_041 : seg 46 45 1 55388435120141 0 8192 335872 27618132885517 0 = true := by
  decide +kernel

theorem seg_042 : seg 46 45 1 17373025271821 0 8192 344064 55388435120141 0 = true := by
  decide +kernel

theorem seg_043 : seg 46 45 1 55415815536653 0 8192 352256 17373025271821 0 = true := by
  decide +kernel

theorem seg_044 : seg 46 45 1 20825642106893 0 8192 360448 55415815536653 0 = true := by
  decide +kernel

theorem seg_045 : seg 46 45 1 41401874120717 0 8192 368640 20825642106893 0 = true := by
  decide +kernel

theorem seg_046 : seg 46 45 1 55093575548941 0 8192 376832 41401874120717 0 = true := by
  decide +kernel

theorem seg_047 : seg 46 45 1 33157147525133 0 8192 385024 55093575548941 0 = true := by
  decide +kernel

theorem path_chunk_05 : PathOK 46 45 1 327680 (36472862277645, 0) (33157147525133, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 27618132885517 0 8192 327680 36472862277645 0 seg_040) (seg_sound 46 45 1 55388435120141 0 8192 335872 27618132885517 0 seg_041)) (path_append (seg_sound 46 45 1 17373025271821 0 8192 344064 55388435120141 0 seg_042) (seg_sound 46 45 1 55415815536653 0 8192 352256 17373025271821 0 seg_043))) (path_append (path_append (seg_sound 46 45 1 20825642106893 0 8192 360448 55415815536653 0 seg_044) (seg_sound 46 45 1 41401874120717 0 8192 368640 20825642106893 0 seg_045)) (path_append (seg_sound 46 45 1 55093575548941 0 8192 376832 41401874120717 0 seg_046) (seg_sound 46 45 1 33157147525133 0 8192 385024 55093575548941 0 seg_047))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
