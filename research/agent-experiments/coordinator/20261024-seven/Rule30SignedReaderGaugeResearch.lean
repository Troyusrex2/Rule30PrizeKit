import Rule30GoldenCompactBudgetResearch

/-! A signed weighted DFA's terminal energy can be absorbed exactly into
its transition costs. This justifies fixing terminal variables to zero in
the synthesis LP without restricting the family. It does NOT apply to
families requiring nonnegative transition costs, including the first neural
prefix-only model. No Rule 30 charge or rank is asserted in this module.
-/
namespace Rule30SignedReaderGaugeResearch

def energy (T : Nat -> Nat -> Nat) (C : Nat -> Nat -> Int) (D : Nat -> Int)
    (p : Nat) : List Nat -> Int
  | [] => D p
  | a::word => C p a+energy T C D (T p a) word

def gaugeCost (T : Nat -> Nat -> Nat) (C : Nat -> Nat -> Int) (D : Nat -> Int)
    (p a : Nat) : Int := C p a+D (T p a)-D p

theorem gauge_energy (T : Nat -> Nat -> Nat) (C : Nat -> Nat -> Int) (D : Nat -> Int)
    (word : List Nat) : forall p,
    energy T (gaugeCost T C D) (fun _ => 0) p word=energy T C D p word-D p := by
  induction word with
  | nil => intro p; simp [energy]
  | cons a word ih =>
    intro p
    rw [energy,energy,ih]
    simp only [gaugeCost]
    omega

theorem initial_energy_preserved (T : Nat -> Nat -> Nat)
    (C : Nat -> Nat -> Int) (D : Nat -> Int) (h0 : D 0=0) (word : List Nat) :
    energy T (gaugeCost T C D) (fun _ => 0) 0 word=energy T C D 0 word := by
  rw [gauge_energy,h0]
  omega

end Rule30SignedReaderGaugeResearch
