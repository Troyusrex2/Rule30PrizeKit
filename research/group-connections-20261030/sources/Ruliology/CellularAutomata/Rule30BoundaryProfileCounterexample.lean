module
public import Ruliology.CellularAutomata.Rule30Prize
/-!
# Why temporal-profile decoding needs the finite white spatial boundary

Two explicit infinite spatial pasts have the same final profile, of dyadic
period8 and not periods1,2,4, but different immediate predecessors. Every
profile has period8 and the literal right-diagonal Rule30 recurrence holds.
There is no white profile anywhere in either past. This is NOT a countermodel
to white-root predecessor uniqueness, to a finite-seed theorem, or to a prize.
The finite presentation is checked; arbitrary past depth follows by iteration.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30BoundaryProfileCounterexample
open Rule30Jen

abbrev State := Fin 13
def code (i : State) : Nat := ([21, 21, 154, 149, 86, 89, 101, 21, 150, 153, 85, 85, 170] : List Nat).getD i.val 0
def older (i : State) : State := ([1, 2, 3, 4, 5, 6, 3, 8, 9, 10, 11, 12, 11] : List State).getD i.val 0
def word (w t : Nat) : Bool := w.testBit (t%8)
def walk (i : State) : Nat → State
  | 0 => i
  | k+1 => older (walk i k)
def past (i : State) (k t : Nat) : Bool := word (code (walk i k)) t
def startA : State := 0
def startB : State := 7

theorem local_certificate : ∀ i : State, ∀ t : Fin 8,
    word (code i) (t.val+1)=xor (word (code i) t.val)
      (word (code (older i)) t.val || word (code (older (older i))) t.val) := by decide +kernel

theorem period_eight (i : State) (k t : Nat) : past i k (t+8)=past i k t := by
  simp [past,word]

/-- The exact sideways recurrence at every depth and every time. -/
theorem recurrence (i : State) (k t : Nat) :
    past i k (t+1)=xor (past i k t) (past i (k+1) t || past i (k+2) t) := by
  have h := local_certificate (walk i k) ⟨t%8,Nat.mod_lt t (by decide)⟩
  simpa [past,walk,word,Nat.add_mod] using h

theorem no_white_profile (i : State) (k : Nat) : ∃ t, past i k t=true := by
  have h : ∀ i : State, ∃ t : Fin 8, word (code i) t.val=true := by decide +kernel
  obtain ⟨t,ht⟩ := h (walk i k)
  exact ⟨t.val,ht⟩

theorem same_final : ∀ t, past startA 0 t=past startB 0 t := by
  intro t
  rfl

theorem different_predecessor : past startA 1 ≠ past startB 1 := by
  intro h
  have ht := congrFun h 0
  have hn : past startA 1 0 ≠ past startB 1 0 := by decide +kernel
  exact hn ht

theorem final_not_period_one : ¬ (∀ t, past startA 0 (t+1)=past startA 0 t) := by
  intro h
  have ht := h 0
  have hn : past startA 0 1 ≠ past startA 0 0 := by decide +kernel
  exact hn ht

theorem final_not_period_two : ¬ (∀ t, past startA 0 (t+2)=past startA 0 t) := by
  intro h
  have ht := h 4
  have hn : past startA 0 6 ≠ past startA 0 4 := by decide +kernel
  exact hn ht

theorem final_not_period_four : ¬ (∀ t, past startA 0 (t+4)=past startA 0 t) := by
  intro h
  have ht := h 2
  have hn : past startA 0 6 ≠ past startA 0 2 := by decide +kernel
  exact hn ht

/-- Infinite temporal-profile pasts need not have unique predecessors, even
when their common final profile is nonconstant and nonalternating. -/
theorem two_infinite_pasts_same_nonalt_final :
    ∃ A B : Nat → Nat → Bool,
      (∀ k t, A k (t+8)=A k t ∧ B k (t+8)=B k t) ∧
      (∀ k t, A k (t+1)=xor (A k t) (A (k+1) t || A (k+2) t)) ∧
      (∀ k t, B k (t+1)=xor (B k t) (B (k+1) t || B (k+2) t)) ∧
      (∀ t, A 0 t=B 0 t) ∧ A 1 ≠ B 1 ∧
      ¬ (∀ t, A 0 (t+1)=A 0 t) ∧ ¬ (∀ t, A 0 (t+2)=A 0 t) ∧
      ¬ (∀ t, A 0 (t+4)=A 0 t) ∧
      (∀ k, ∃ t, A k t=true) ∧ (∀ k, ∃ t, B k t=true) := by
  exact ⟨past startA,past startB,
    fun k t => ⟨period_eight startA k t,period_eight startB k t⟩,
    recurrence startA,recurrence startB,same_final,different_predecessor,
    final_not_period_one,final_not_period_two,final_not_period_four,
    no_white_profile startA,no_white_profile startB⟩

end Ruliology.CellularAutomata.Rule30BoundaryProfileCounterexample
