module
public import Ruliology.CellularAutomata.Rule30Prize

/-! A boundary diagnostic, not a counterexample for white-boundary Actual.
On a spatial six-cycle the exact interior equations admit initial subset
support followed by subset loss, although Common holds for every time.
The two actual backgrounds merge after two updates. -/
@[expose] public section
namespace Rule30CyclicSubsetObstructionResearch
set_option maxHeartbeats 4000000

abbrev Row := Fin 6 → Bool
def bits (n : Nat) : Row := fun j => n.testBit j.val
def older1 (j : Fin 6) : Fin 6 := j+5
def older2 (j : Fin 6) : Fin 6 := j+4
def newer (j : Fin 6) : Fin 6 := j+1

def actualStep (a : Row) : Row := fun j =>
  xor (a j) (a (older1 j) || a (older2 j))

def modeStep (a b h : Row) : Row := fun j =>
  xor (h j) (xor ((!b (older2 j)) && h (older1 j))
    ((!a (older1 j)) && h (older2 j)))

def Common (a b h : Row) : Prop := ∀ j : Fin 6,
  (xor (a j) (b j) && h (newer j)) = (h j && xor (a (newer j)) (b (newer j)))
def Subset (a b h : Row) : Prop := ∀ j : Fin 6, (h j && xor (a j) (b j))=h j
instance (a b h : Row) : Decidable (Common a b h) := by unfold Common; infer_instance
instance (a b h : Row) : Decidable (Subset a b h) := by unfold Subset; infer_instance

def wordA : Nat → Nat
  | 0 => 58 | 1 => 5 | 2 => 27 | 3 => 36 | 4 => 63 | _ => 0
def wordB : Nat → Nat
  | 0 => 23 | 1 => 40 | 2 => 27 | 3 => 36 | 4 => 63 | _ => 0
def wordH : Nat → Nat
  | 0 => 12 | 1 => 12 | 2 => 36 | 3 => 36 | _ => 63
def A (t : Nat) : Row := bits (wordA t)
def B (t : Nat) : Row := bits (wordB t)
def H (t : Nat) : Row := bits (wordH t)

theorem words_tail (t : Nat) : wordA (t+5)=0 ∧ wordB (t+5)=0 ∧ wordH (t+5)=63 := by
  exact ⟨rfl,rfl,rfl⟩

theorem finite_actual : ∀ (t : Fin 5) (j : Fin 6),
    A (t.val+1) j = actualStep (A t.val) j ∧
    B (t.val+1) j = actualStep (B t.val) j := by decide +kernel

theorem finite_mode : ∀ (t : Fin 5) (j : Fin 6),
    H (t.val+1) j = modeStep (A t.val) (B t.val) (H t.val) j := by decide +kernel

theorem finite_common : ∀ t : Fin 5, Common (A t.val) (B t.val) (H t.val) := by
  decide +kernel

theorem tail_checks :
    (∀ j : Fin 6, bits 0 j=actualStep (bits 0) j) ∧
    (∀ j : Fin 6, bits 63 j=modeStep (bits 0) (bits 0) (bits 63) j) ∧
    Common (bits 0) (bits 0) (bits 63) := by decide +kernel

theorem actual_all_time : ∀ (t : Nat) (j : Fin 6),
    A (t+1) j=actualStep (A t) j ∧ B (t+1) j=actualStep (B t) j := by
  intro t j
  by_cases small : t<5
  · exact finite_actual ⟨t,small⟩ j
  · obtain ⟨u,rfl⟩ : ∃ u, t=u+5 := ⟨t-5,by omega⟩
    simp only [A,B,show u+5+1=(u+1)+5 by omega,(words_tail u).1,
      (words_tail u).2.1,(words_tail (u+1)).1,(words_tail (u+1)).2.1]
    exact ⟨tail_checks.1 j,tail_checks.1 j⟩

theorem mode_all_time : ∀ (t : Nat) (j : Fin 6),
    H (t+1) j=modeStep (A t) (B t) (H t) j := by
  intro t j
  by_cases small : t<5
  · exact finite_mode ⟨t,small⟩ j
  · obtain ⟨u,rfl⟩ : ∃ u, t=u+5 := ⟨t-5,by omega⟩
    simp only [A,B,H,show u+5+1=(u+1)+5 by omega,(words_tail u).1,
      (words_tail u).2.1,(words_tail u).2.2,(words_tail (u+1)).2.2]
    exact tail_checks.2.1 j

theorem common_all_time : ∀ t : Nat, Common (A t) (B t) (H t) := by
  intro t
  by_cases small : t<5
  · exact finite_common ⟨t,small⟩
  · obtain ⟨u,rfl⟩ : ∃ u, t=u+5 := ⟨t-5,by omega⟩
    simp only [A,B,H,(words_tail u).1,(words_tail u).2.1,(words_tail u).2.2]
    exact tail_checks.2.2

theorem initially_subset : Subset (A 0) (B 0) (H 0) := by decide +kernel
theorem subset_lost_at_two : ¬ Subset (A 2) (B 2) (H 2) := by decide +kernel
theorem backgrounds_coalesce (t : Nat) : A (t+2)=B (t+2) := by
  cases t with
  | zero => rfl
  | succ t =>
    cases t with
    | zero => rfl
    | succ t =>
      cases t with
      | zero => rfl
      | succ t => rfl
theorem white_boundary_fails : A 1 0≠A 0 0 := by decide +kernel

/-- Exact all-time cyclic dynamics. The white-boundary equations at depths
zero and one are absent here, and must not be dropped from Actual. -/
theorem cyclic_subset_preservation_fails :
    (∀ t j, A (t+1) j=actualStep (A t) j ∧ B (t+1) j=actualStep (B t) j) ∧
    (∀ t j, H (t+1) j=modeStep (A t) (B t) (H t) j) ∧
    (∀ t, Common (A t) (B t) (H t)) ∧
    Subset (A 0) (B 0) (H 0) ∧ ¬Subset (A 2) (B 2) (H 2) :=
  ⟨actual_all_time,mode_all_time,common_all_time,initially_subset,subset_lost_at_two⟩

end Rule30CyclicSubsetObstructionResearch
