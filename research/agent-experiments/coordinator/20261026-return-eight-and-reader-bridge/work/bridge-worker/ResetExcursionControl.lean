import PrizeSafetyBridge

/-! A finite actual-white counterexample to decoding the parent segment from
one complete newest-column excursion between three-white resets. This is not
an all-time collision: the two newest traces subsequently separate. -/
namespace ResetExcursionControl
open CedarSafetySoundness CedarSafety

def a : List Bool :=
  [true,false,false,false,false,true,false,false,false,false,false,false]
def b : List Bool :=
  [true,false,false,false,false,true,true,false,false,false,false,false]
def code : List Bool := [false,false,false,true,false,true,false,false]
def trace8 (xs : List Bool) : List Bool :=
  (List.range 8).map (fun t => newest (evolution t xs))

theorem one_excursion_counterexample :
    a.take 3 = [true,false,false] ∧ b.take 3 = [true,false,false] ∧
    Rule30ColumnReaderResearch.run 0 (a.zip b) = 15 ∧
    trace8 a = code ∧ trace8 b = code ∧
    (evolution 6 a).drop 9 = [false,false,false] ∧
    (evolution 6 b).drop 9 = [false,false,false] ∧
    (evolution 2 a).getD 10 false ≠ (evolution 2 b).getD 10 false := by
  decide +kernel

end ResetExcursionControl
