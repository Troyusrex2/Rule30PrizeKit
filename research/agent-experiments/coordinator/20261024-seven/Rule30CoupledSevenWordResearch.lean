import Rule30CoupledWordCertificateResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30CoupledSevenWordResearch
open Ruliology.CellularAutomata.Rule30PeriodTwoSideways (u)
open Rule30CoupledWordCertificateResearch

def word : List Bool := [true,false,true,true,false,true,false]

theorem seven_check : check word=true := by decide +kernel

theorem no_free_1011010 (R : Nat → Bool) (s : Nat) :
    (List.range 7).map (fun i => !u R (s+i)) ≠ word :=
  forbidden_of_check (by decide) seven_check R s

end Rule30CoupledSevenWordResearch
