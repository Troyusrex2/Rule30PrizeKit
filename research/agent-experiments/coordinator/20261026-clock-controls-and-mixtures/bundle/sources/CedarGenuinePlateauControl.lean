import CedarSafetySoundness

/-! A fixed literal finite-white clock plateau. No safety, height bound,
minimality, or arbitrary plateau classification is asserted. -/
namespace CedarGenuinePlateauControl
open CedarSafetySoundness
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def older : List Bool := [true,true,false,true,true,false,false,true,false]
def birth : List Bool := older ++ [false]
def child (a : Bool) : List Bool := birth ++ [a]
def tr (xs : List Bool) (t : Nat) : Bool := (evolution t xs).getLastD false

theorem birth_certificate :
    evolution 16 older=older ∧
    evolution 16 birth=older ++ [true] ∧
    evolution 32 birth=birth := by
  decide +kernel

theorem birth_anti16_finite : ∀ t : Fin 16,
    tr birth (t.val+16)=!(tr birth t.val) := by
  decide +kernel

theorem children_return32 : ∀ a : Bool,
    evolution 32 (child a)=child a := by
  decide +kernel

theorem children_nonreturn16 : ∀ a : Bool,
    evolution 16 (child a)≠child a := by
  decide +kernel

/-- The same two defect values hold for each choice of the new initial bit. -/
theorem children_defect_witnesses : ∀ a : Bool,
    xor (tr (child a) 16) (tr (child a) 0)=true ∧
    xor (tr (child a) 17) (tr (child a) 1)=false := by
  decide +kernel

theorem children_not_anti16 (a : Bool) :
    ¬ ∀ t : Nat, tr (child a) (t+16)=!(tr (child a) t) := by
  have bad : ∀ a : Bool, tr (child a) 17≠!(tr (child a) 1) := by
    decide +kernel
  intro h
  exact bad a (h 1)

theorem children_not_periodic16 (a : Bool) :
    ¬ ∀ t : Nat, tr (child a) (t+16)=tr (child a) t := by
  have bad : ∀ a : Bool, tr (child a) 16≠tr (child a) 0 := by
    decide +kernel
  intro h
  exact bad a (h 0)

end CedarGenuinePlateauControl
