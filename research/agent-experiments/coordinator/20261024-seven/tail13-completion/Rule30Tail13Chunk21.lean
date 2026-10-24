module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-! One exact segment of the complete (13,0) front-window certificate.
Every Boolean computation is replayed by the Lean kernel. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Tail13Completion
open Rule30ZeroBoundaryStripeFront

theorem seg_168 : seg 46 45 1 67200551485453 0 8192 1376256 5686536699917 0 = true := by
  decide +kernel

theorem seg_169 : seg 46 45 1 15806016520205 0 8192 1384448 67200551485453 0 = true := by
  decide +kernel

theorem seg_170 : seg 46 45 1 65751536893965 0 8192 1392640 15806016520205 0 = true := by
  decide +kernel

theorem seg_171 : seg 46 45 1 33425582981133 0 8192 1400832 65751536893965 0 = true := by
  decide +kernel

theorem seg_172 : seg 46 45 1 69204153729037 0 8192 1409024 33425582981133 0 = true := by
  decide +kernel

theorem seg_173 : seg 46 45 1 54596013654029 0 8192 1417216 69204153729037 0 = true := by
  decide +kernel

theorem seg_174 : seg 46 45 1 68287715082253 0 8192 1425408 54596013654029 0 = true := by
  decide +kernel

theorem seg_175 : seg 46 45 1 46351287058445 0 8192 1433600 68287715082253 0 = true := by
  decide +kernel

theorem path_chunk_21 : PathOK 46 45 1 1376256 (5686536699917, 0) (46351287058445, 0) 65536 :=
  (path_append (path_append (path_append (seg_sound 46 45 1 67200551485453 0 8192 1376256 5686536699917 0 seg_168) (seg_sound 46 45 1 15806016520205 0 8192 1384448 67200551485453 0 seg_169)) (path_append (seg_sound 46 45 1 65751536893965 0 8192 1392640 15806016520205 0 seg_170) (seg_sound 46 45 1 33425582981133 0 8192 1400832 65751536893965 0 seg_171))) (path_append (path_append (seg_sound 46 45 1 69204153729037 0 8192 1409024 33425582981133 0 seg_172) (seg_sound 46 45 1 54596013654029 0 8192 1417216 69204153729037 0 seg_173)) (path_append (seg_sound 46 45 1 68287715082253 0 8192 1425408 54596013654029 0 seg_174) (seg_sound 46 45 1 46351287058445 0 8192 1433600 68287715082253 0 seg_175))))

end Ruliology.CellularAutomata.Rule30Tail13Completion
