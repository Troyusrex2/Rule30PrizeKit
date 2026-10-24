module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_232 : seg 46 45 1 13874237538317 0 8192 1900544 56813827391501 0 = true := by
  decide +kernel

theorem seg_233 : seg 46 45 1 50440632795149 0 8192 1908736 13874237538317 0 = true := by
  decide +kernel

theorem seg_234 : seg 46 45 1 1430106669069 0 8192 1916928 50440632795149 0 = true := by
  decide +kernel

theorem seg_235 : seg 46 45 1 37273873678349 0 8192 1925120 1430106669069 0 = true := by
  decide +kernel

theorem seg_236 : seg 46 45 1 36768560709645 0 8192 1933312 37273873678349 0 = true := by
  decide +kernel

theorem seg_237 : seg 46 45 1 60643327606797 0 8192 1941504 36768560709645 0 = true := by
  decide +kernel

theorem seg_238 : seg 46 45 1 31454075551757 0 8192 1949696 60643327606797 0 = true := by
  decide +kernel

theorem seg_239 : seg 46 45 1 53498112638989 0 8192 1957888 31454075551757 0 = true := by
  decide +kernel

theorem path_chunk_29 : PathOK 46 45 1 1900544 (56813827391501, 0) (53498112638989, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 13874237538317 0 8192 1900544 56813827391501 0 seg_232) (seg_sound 46 45 1 50440632795149 0 8192 1908736 13874237538317 0 seg_233)) (path_append (seg_sound 46 45 1 1430106669069 0 8192 1916928 50440632795149 0 seg_234) (seg_sound 46 45 1 37273873678349 0 8192 1925120 1430106669069 0 seg_235))) (path_append (path_append (seg_sound 46 45 1 36768560709645 0 8192 1933312 37273873678349 0 seg_236) (seg_sound 46 45 1 60643327606797 0 8192 1941504 36768560709645 0 seg_237)) (path_append (seg_sound 46 45 1 31454075551757 0 8192 1949696 60643327606797 0 seg_238) (seg_sound 46 45 1 53498112638989 0 8192 1957888 31454075551757 0 seg_239))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
