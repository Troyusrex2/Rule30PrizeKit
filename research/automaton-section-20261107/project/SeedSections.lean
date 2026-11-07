module
public import SeedAutomaton

/-! The actual center-conditioned sections still carry the whole negative
half-row. Their complexity is unbounded even on the fixed zero input.
This rules out a bounded lossless section catalogue, not an aperiodicity
argument concerning the single parity bit actually observed at the center. -/
@[expose] public section
namespace SeedSections
open SeedAutomaton SeedAutomaton.St
open Ruliology.CellularAutomata Rule30Jen Rule30Diagonals

def core (n : Nat) : List St := rounds n (List.replicate (n+1) C)

theorem rounds_add (a b : Nat) (w : List St) :
    rounds (a+b) w=rounds b (rounds a w) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change dual false (rounds (a+b) w)=dual false (rounds b (rounds a w))
    rw [ih]

theorem section_read (n k : Nat) (w : List St) :
    wordAct (rounds n w) zero k=wordAct w zero (n+k) := by
  rw [word_zero_read,word_zero_read,rounds_add]

/-- Every output coordinate, in the official physical singleton frame. -/
theorem core_row (n k : Nat) :
    wordAct (core n) zero k=cell (n+1) (-(k:Int)) := by
  unfold core
  rw [section_read,word_replicate]
  have h := congrFun (power_seed (n+1)) (n+1+k)
  rw [power_cons_true] at h
  have idx : n+1+k=(n+k)+1 := by omega
  rw [idx] at h
  change power C zero (n+1) (n+k)=R ((n+k)+1) (n+1) at h
  unfold R at h
  rw [show ((n+1:Nat):Int)-((n+k+1:Nat):Int)= -(k:Int) by omega] at h
  exact h

theorem core_edge (n : Nat) : wordAct (core n) zero (n+1)=true := by
  rw [core_row,cell_left_edge]

theorem core_white (n k : Nat) (h : n+1<k) : wordAct (core n) zero k=false := by
  rw [core_row]
  exact cell_eq_false_of_lt _ _ (by omega)

/-- Distinct actual sections disagree on the same fixed input 000... . -/
theorem core_distinct (n m : Nat) (h : n<m) :
    wordAct (core n) zero ≠ wordAct (core m) zero := by
  intro eq
  have e := congrFun eq (m+1)
  rw [core_white n (m+1) (by omega),core_edge] at e
  cases e

theorem act_support (s : St) (x : Stream) (W : Nat)
    (white : ∀ k,W≤k → x k=false) (k : Nat) (h : W+2≤k) :
    act s x k=false := by
  obtain ⟨j,rfl⟩ : ∃ j,k=j+2 := ⟨k-2,by omega⟩
  rw [act_local,white (j+2) (by omega),white (j+1) (by omega),white j (by omega)]
  rfl

theorem word_support (w : List St) (x : Stream) (W : Nat)
    (white : ∀ k,W≤k → x k=false) :
    ∀ k,W+2*w.length≤k → wordAct w x k=false := by
  induction w generalizing x W with
  | nil => exact white
  | cons s w ih =>
    intro k hk
    exact ih (act s x) (W+2) (act_support s x W white) k
      (by simp only [List.length_cons] at hk; omega)

/-- A lower bound for POSITIVE state words representing this zero-input
output. This is not a bound for arbitrary algorithms or words with inverses. -/
theorem representative_length (n : Nat) (w : List St)
    (rep : wordAct w zero=wordAct (core n) zero) : n+1<2*w.length := by
  apply Classical.byContradiction
  intro h
  have white := word_support w zero 0 (fun _ _ => rfl) (n+1) (by omega)
  rw [rep,core_edge] at white
  cases white

/-- Even this ACTUAL family has no fixed positive-word representation cap. -/
theorem no_uniform_positive_cap :
    ¬ (∃ K,∀ n,∃ w : List St,w.length≤K ∧ wordAct w zero=wordAct (core n) zero) := by
  rintro ⟨K,cap⟩
  obtain ⟨w,len,rep⟩ := cap (2*K)
  have h := representative_length (2*K) w rep
  omega

#print axioms SeedSections.core_row
#print axioms SeedSections.no_uniform_positive_cap
end SeedSections
