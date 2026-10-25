import Rule30GoldenBudgetDAG4Part0005Research

namespace Rule30GoldenBudgetDAG4Research
open Rule30GoldenCompactBudgetResearch
open Rule30GoldenBudgetResearch (count)

theorem checked : check 4 50=true := Rule30GoldenBudgetDAG4Part0005Research.node_716

theorem minimum_count (s : Nat → Bool) (hg : Rule30GoldenDFAResearch.Golden s) :
    5 ≤ count s 50 := by
  have hn : ¬ count s 50 ≤ 4 := fun hb => no_golden_of_check checked s hb hg
  omega

theorem no_golden_budget (s : Nat → Bool) (h : ∀ K, count s K ≤ 4) :
    ¬ Rule30GoldenDFAResearch.Golden s := no_golden_of_check checked s (h 50)

end Rule30GoldenBudgetDAG4Research
