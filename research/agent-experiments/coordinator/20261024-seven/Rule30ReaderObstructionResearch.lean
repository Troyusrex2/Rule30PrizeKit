import Ruliology.CellularAutomata.Rule30StripeMeeting

/-! Exact obstruction to the proposed generic 4*width trace-prefix reader.
This does not refute the seed-coupled problem, edge separation, or Problem 1.
The update and moving-frame rows are the official catalog definitions. -/

namespace Rule30ReaderObstructionResearch

open Ruliology.CellularAutomata.Rule30StripeMeeting

def tracePrefix (a c n : Nat) : List Bool :=
  (List.range n).map (fun t => (phiRows a t).testBit (c+t))

def SeedLow (a : Nat) : Prop :=
  a.testBit 0 = true ∧ a.testBit 1 = a.testBit 2

theorem pair48_49_classes :
    32 ≤ (48 : Nat) ∧ 48 < 64 ∧ 32 ≤ (49 : Nat) ∧ 49 < 64 ∧
    (48 : Nat).testBit 0 = false ∧ SeedLow 49 := by unfold SeedLow; decide +kernel

theorem pair48_49_equal27 : tracePrefix 48 3 27 = tracePrefix 49 3 27 := by decide +kernel

theorem pair48_49_equal25 : tracePrefix 48 3 (4*6+1) = tracePrefix 49 3 (4*6+1) := by
  decide +kernel

theorem pair48_49_first_difference :
    (phiRows 48 27).testBit (3+27) ≠ (phiRows 49 27).testBit (3+27) := by
  decide +kernel

/-- The two rows have the same width and the same known observation index.
Even a reader specialized to these parameters cannot classify every row. -/
theorem no_four_width_generic_reader :
    ¬ ∃ R : List Bool → Bool, ∀ a : Nat, 32 ≤ a → a < 64 →
      (a.testBit 0 = false → R (tracePrefix a 3 (4*6+1)) = false) ∧
      (SeedLow a → R (tracePrefix a 3 (4*6+1)) = true) := by
  rintro ⟨R, h⟩
  have ha := (h 48 (by decide) (by decide)).1 (by decide)
  have hb := (h 49 (by decide) (by decide)).2 (by unfold SeedLow; decide +kernel)
  rw [pair48_49_equal25] at ha
  rw [ha] at hb
  cases hb

def rule (l c r : Bool) : Bool := xor l (c || r)

theorem coupled_difference (al ac ar bl bc br : Bool) :
    xor (rule al ac ar) (rule bl bc br) =
      xor (xor al bl) (xor ((!ar) && xor ac bc) ((!bc) && xor ar br)) := by
  cases al <;> cases ac <;> cases ar <;> cases bl <;> cases bc <;> cases br <;> rfl

theorem center_successor_does_not_determine_right :
    rule false false false = rule true false true ∧ (false : Bool) ≠ true := by
  decide +kernel

end Rule30ReaderObstructionResearch
