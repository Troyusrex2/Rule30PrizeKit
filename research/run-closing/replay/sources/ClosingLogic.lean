module
public import Ruliology.CellularAutomata.Rule30Prize

/-! Two generic logical checks for the inverse-closing program.
These are NOT Rule30 nonperiodicity theorems. -/
@[expose] public section
namespace ClosingLogic

def Live (w : List Bool) : Prop := w.all (fun b => !b)=true

theorem false_child_live (w : List Bool) (h : Live w) : Live (w++[false]) := by
  simpa [Live,List.all_append] using h

theorem true_child_dead (w : List Bool) : ¬Live (w++[true]) := by
  simp [Live,List.all_append]

theorem zero_path_live (n : Nat) : Live (List.replicate n false) := by
  simp [Live]

/-- Exactly one of the two one-bit choices kills at EVERY live node,
yet a live prefix exists at EVERY depth. Positive-fraction local killing
alone cannot establish universal extinction. -/
theorem local_kill_not_universal_extinction :
    (∀ w, Live w → Live (w++[false]) ∧ ¬Live (w++[true])) ∧
    (∀ n, Live (List.replicate n false)) :=
  ⟨fun w h => ⟨false_child_live w h,true_child_dead w⟩,zero_path_live⟩

abbrev Vec := Nat → Bool
def add (a b : Vec) : Vec := fun t => xor (a t) (b t)
def shift (v : Vec) : Vec := fun t => v (t+1)
def linearNext (u v : Vec) : Vec × Vec := (v,add (add (shift v) v) u)
def linearPrev (v w : Vec) : Vec × Vec := (add (add (shift v) v) w,v)

theorem add_cancel (a b : Vec) : add a (add a b)=b := by
  funext t
  unfold add
  cases a t <;> cases b t <;> rfl

/-- The inverse-frame Rule150 damage update is exactly reversible. -/
theorem linear_inverse (u v : Vec) :
    linearPrev (linearNext u v).1 (linearNext u v).2=(u,v) := by
  simp only [linearNext,linearPrev,add_cancel]

theorem linear_zero_reflect (u v : Vec) :
    linearNext u v=(fun _ => false,fun _ => false) →
      u=(fun _ => false) ∧ v=(fun _ => false) := by
  intro h
  have he := congrArg (fun p : Vec × Vec => linearPrev p.1 p.2) h
  rw [linear_inverse] at he
  change (u,v)=(fun _ => false,fun _ => false) at he
  exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩

def linearIterate : Nat → Vec × Vec → Vec × Vec
  | 0,p => p
  | n+1,p => linearNext (linearIterate n p).1 (linearIterate n p).2

/-- No finite nonzero two-column damage state can close in the linear
model. The result is all-n and does not depend on a simulation horizon. -/
theorem linear_no_finite_closing (n : Nat) (u v : Vec) :
    linearIterate n (u,v)=(fun _ => false,fun _ => false) →
      u=(fun _ => false) ∧ v=(fun _ => false) := by
  induction n with
  | zero => intro h;exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩
  | succ n ih =>
    intro h
    have he := linear_zero_reflect _ _ h
    apply ih
    exact Prod.ext he.1 he.2

end ClosingLogic
