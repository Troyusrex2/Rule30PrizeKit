import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes

/-! A two-transition obstruction to nonnegative letter-count potentials on
paired reconstruction anti-diagonals, even with a free-run-dependent weight.
The two transitions have zero even-coordinate output and a golden free
prefix. This rejects only this potential family, not arbitrary ranks. -/

namespace Rule30DecoderRankObstructionResearch
open Ruliology.CellularAutomata
open Rule30ZeroBoundary (recon)
open Rule30ZeroBoundaryLanes (AD)

def free (k : Nat) : Bool := k%2 == 1
def head (t : Nat) : Bool := if t%2 = 0 then true else free (t/2)

theorem golden_no00 (k : Nat) : free k || free (k+1) = true := by
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · simp only [free, hk, show (k+1)%2 = 1 by omega]; decide
  · simp only [free, hk, show (k+1)%2 = 0 by omega]; decide

theorem golden_no11111 (k : Nat) : ∃ j, j < 5 ∧ free (k+j) = false := by
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · refine ⟨0,by decide,?_⟩
    simp only [Nat.add_zero, free, hk]; decide
  · refine ⟨1,by decide,?_⟩
    simp only [free, show (k+1)%2 = 0 by omega]; decide

def word (k : Nat) : List Nat := (List.range k).map fun i =>
  ((AD head k 0 k).getD i false).toNat +
    2*((AD head (k-1) 0 (k-1)).getD i false).toNat

theorem diagonal_words : word 2 = [2,1] ∧ word 4 = [3,2,1,0] ∧
    word 6 = [2,1,2,1,0,0] := by decide +kernel

theorem initial_even_bits : recon head 2 0 = true ∧
    recon head 4 0 = false ∧ recon head 6 0 = false := by decide +kernel

def mass (w : Nat → Nat → Nat) (run : Nat) (xs : List Nat) : Nat :=
  xs.foldr (fun a z => w run a + z) 0

/-- The free-one step from 0 to 01 would require nonincrease; the free-zero
step from 01 to 010 would require a strict decrease. Both have zero even
output. No nonnegative natural letter weights can satisfy both inequalities. -/
theorem no_letter_potential (w : Nat → Nat → Nat)
    (h01 : mass w 1 (word 4) ≤ mass w 0 (word 2))
    (h010 : mass w 0 (word 6)+1 ≤ mass w 1 (word 4)) : False := by
  rw [diagonal_words.1, diagonal_words.2.1] at h01
  rw [diagonal_words.2.1, diagonal_words.2.2] at h010
  simp only [mass, List.foldr, Nat.add_zero] at h01 h010
  omega

end Rule30DecoderRankObstructionResearch
