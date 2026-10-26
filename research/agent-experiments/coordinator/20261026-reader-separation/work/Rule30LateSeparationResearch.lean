module
public import Rule30ColumnReaderResearch

/-! An exact finite counterexample to a three-times-width observation bound.
The trajectory is at fixed right-edge depth, not the prize's fixed center.
It supports, rather than refutes, separation inside the reader's sink. -/
@[expose] public section
namespace Rule30LateSeparationResearch
open Rule30ColumnReaderResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def observations : Nat → List Symbol → List Symbol
  | 0,_ => []
  | n+1,ss => lastPair zero ss :: observations n (stepWord ss)

def initialPair : List Symbol := (List.range 22).map
  (fun j => (Nat.testBit 1393025 j,Nat.testBit 956974 j))

theorem example_length : initialPair.length=22 := by decide +kernel

theorem example_sink : run 0 initialPair=15 := by decide +kernel

/-- The first 72 observations agree; observation 72 differs. -/
theorem example_first_difference :
    (observations 73 initialPair).map (fun s => s.1==s.2)=
      List.replicate 72 true ++ [false] := by decide +kernel

end Rule30LateSeparationResearch
