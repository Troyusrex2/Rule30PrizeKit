import Rule30GoldenBudgetDFSResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenBudgetDFSPilotResearch
open Rule30GoldenBudgetResearch (count)
open Rule30GoldenBudgetDFSResearch (check no_golden_of_check)

theorem check2 : check 2 17 = true := by decide +kernel

theorem minimum_three (s : Nat → Bool) (hg : Rule30GoldenDFAResearch.Golden s) :
    3 ≤ count s 17 := by
  have hn : ¬ count s 17 ≤ 2 := fun hb => no_golden_of_check check2 s hb hg
  omega

end Rule30GoldenBudgetDFSPilotResearch
