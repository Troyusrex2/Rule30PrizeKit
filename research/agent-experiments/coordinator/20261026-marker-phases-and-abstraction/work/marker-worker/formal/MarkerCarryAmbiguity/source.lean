import CedarMarkerReturnTwo
import CedarSafetyBridge

/-! Actual finite-white ambiguity of marker/carry observations. These
results refute deterministic state closure, not arbitrary invariants or
relational abstractions, and not a Safe-versus-nonreturn separator. -/
namespace MarkerCarryAmbiguity
open CedarSafetySoundness CedarMarkerReturnTwo CedarSafety CedarSafetyBridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Includes the terminal top carry, so the complete row has length |xs|+1. -/
def carries (p r s : Bool) : List Bool → List Bool
  | [] => [carry p r s]
  | v::vs => carry p r s :: carries v p r vs

def fullCarry (xs : List Bool) : List Bool := carries false false false xs
def topCarry (xs : List Bool) : Bool := (fullCarry xs).getLastD false

structure View where
  markers0 : List Bool
  markers1 : List Bool
  carries0 : List Bool
  carries1 : List Bool
deriving DecidableEq

def view (xs : List Bool) : View := ⟨marked xs,marked (F xs),fullCarry xs,fullCarry (F xs)⟩

structure ShortView where
  markers0 : List Bool
  markers1 : List Bool
  carries0 : List Bool
  top0 : Bool
  top1 : Bool
deriving DecidableEq

def shortView (xs : List Bool) : ShortView :=
  ⟨marked xs,marked (F xs),fullCarry xs,topCarry xs,topCarry (F xs)⟩

def safeX : List Bool := [true,true,true,true,false,false]
def safeY : List Bool := [true,true,true,true,true,false]

theorem safe_same_orbit : evolution 4 safeX=safeY ∧ Safe safeX ∧ Safe safeY := by
  refine ⟨by decide +kernel,?_,?_⟩
  · exact ((safe_return_iff_accepted safeX).mpr (by decide +kernel)).1
  · exact ((safe_return_iff_accepted safeY).mpr (by decide +kernel)).1

theorem short_view_equal : shortView safeX=shortView safeY := by decide +kernel

theorem future_marker_differs : marked (F (F safeX))≠marked (F (F safeY)) := by decide +kernel

/-- Even on all-time Safe words, two marker rows, the full current carry
row, and both top carries do not determine the following marker row. -/
theorem no_short_view_marker_update : ¬ ∃ update : ShortView → List Bool,
    ∀ xs, Safe xs → update (shortView xs)=marked (F (F xs)) := by
  rintro ⟨update,hu⟩
  have hx := hu safeX safe_same_orbit.2.1
  have hy := hu safeY safe_same_orbit.2.2
  rw [short_view_equal] at hx
  exact future_marker_differs (hx.symm.trans hy)

def alternating (v : Bool) : Nat → List Bool
  | 0 => []
  | n+1 => v :: alternating (!v) n

theorem scan_alternating (n : Nat) (p r s v : Bool)
    (h0 : (p || r)=true) (h1 : (v || p)=true) :
    marks p r s (alternating v n)=List.replicate n false ∧
      carries p r s (alternating v n)=List.replicate (n+1) true := by
  have localFact : ∀ p r s : Bool, (p || r)=true →
      marker p r s=false ∧ carry p r s=true := by decide +kernel
  induction n generalizing p r s v with
  | zero =>
      change []=[] ∧ [carry p r s]=[true]
      exact ⟨rfl,by rw [(localFact p r s h0).2]⟩
  | succ n ih =>
      have hn : ((!v) || v)=true := by cases v <;> rfl
      obtain ⟨hm,hc⟩ := ih v p r (!v) h1 hn
      simp only [alternating,marks,carries,List.replicate_succ]
      rw [(localFact p r s h0).1,(localFact p r s h0).2,hm,hc]
      exact ⟨rfl,rfl⟩

theorem change_alternating (n : Nat) (p r v : Bool)
    (h0 : (p || r)=true) (h1 : (v || p)=true) :
    change p r (alternating v n)=alternating (!v) n := by
  induction n generalizing p r v with
  | zero => rfl
  | succ n ih =>
      have hn : ((!v) || v)=true := by cases v <;> rfl
      have ht := ih v p (!v) h1 hn
      have hx : xor v true=(!v) := by cases v <;> rfl
      simp only [alternating,change,h0,hx,ht]

/-- Both phases are genuine white-anchored words, at every suffix length. -/
def family (v : Bool) (n : Nat) : List Bool :=
  [true,false,false,true] ++ alternating v n

theorem family_step (v : Bool) (n : Nat) :
    F (family v n)=[true,true,true,true]++alternating (!v) n := by
  change [true,true,true,true]++change true false (alternating v n)=_
  rw [change_alternating n true false v rfl (by cases v <;> rfl)]

theorem family_step_two (v : Bool) (n : Nat) :
    F (F (family v n))=[true,false,false,false]++alternating v n := by
  rw [family_step]
  change [true,false,false,false]++change true true (alternating (!v) n)=_
  rw [change_alternating n true true (!v) rfl (by cases v <;> rfl),Bool.not_not]

theorem family_markers (v : Bool) (n : Nat) :
    marked (family v n)=[false,false,false,true]++List.replicate n false := by
  change [false,false,false,true]++marks true false false (alternating v n)=_
  rw [(scan_alternating n true false false v rfl (by cases v <;> rfl)).1]

theorem family_carries (v : Bool) (n : Nat) :
    fullCarry (family v n)=[false,true,true,true]++List.replicate (n+1) true := by
  change [false,true,true,true]++carries true false false (alternating v n)=_
  rw [(scan_alternating n true false false v rfl (by cases v <;> rfl)).2]

theorem family_next_markers (v : Bool) (n : Nat) :
    marked (F (family v n))=[false,false,false,false]++List.replicate n false := by
  rw [family_step]
  change [false,false,false,false]++marks true true true (alternating (!v) n)=_
  rw [(scan_alternating n true true true (!v) rfl (by cases v <;> rfl)).1]

theorem family_next_carries (v : Bool) (n : Nat) :
    fullCarry (F (family v n))=[false,true,true,true]++List.replicate (n+1) true := by
  rw [family_step]
  change [false,true,true,true]++carries true true true (alternating (!v) n)=_
  rw [(scan_alternating n true true true (!v) rfl (by cases v <;> rfl)).2]

/-- Retaining BOTH complete carry rows still hides the alternating phase. -/
theorem full_view_family_equal (n : Nat) : view (family false n)=view (family true n) := by
  simp only [view,family_markers,family_next_markers,family_carries,family_next_carries]

theorem future_carry_exposes_phase (v : Bool) (n : Nat) :
    (fullCarry (F (F (family v (n+1))))).getD 5 false=v := by
  rw [family_step_two]
  cases n <;> cases v <;> rfl

theorem future_full_view_differs (n : Nat) :
    view (F (family false (n+1)))≠view (F (family true (n+1))) := by
  intro h
  have hc := congrArg (fun s : View => s.carries1.getD 5 false) h
  change (fullCarry (F (F (family false (n+1))))).getD 5 false=
    (fullCarry (F (F (family true (n+1))))).getD 5 false at hc
  rw [future_carry_exposes_phase,future_carry_exposes_phase] at hc
  contradiction

theorem anchored_nonreturn_pair :
    evolution 8 (family false 3)≠family false 3 ∧
      evolution 8 (family true 3)≠family true 3 := by decide +kernel

/-- This remains a deterministic-closure obstruction, not a prohibition
on sound relational abstractions or invariants carried by the view. -/
theorem no_full_view_update_on_nonreturn : ¬ ∃ update : View → View,
    ∀ xs, evolution 8 xs≠xs → update (view xs)=view (F xs) := by
  rintro ⟨update,hu⟩
  have hx := hu (family false 3) anchored_nonreturn_pair.1
  have hy := hu (family true 3) anchored_nonreturn_pair.2
  rw [full_view_family_equal] at hx
  exact future_full_view_differs 2 (hx.symm.trans hy)

end MarkerCarryAmbiguity
