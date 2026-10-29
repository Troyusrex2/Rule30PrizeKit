module
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Realization
public import EndpointTransport

/-! Uniform endpoint interaction growth alone cannot prove seed aperiodicity:
Rule210 has the same endpoint-control property and an eventually white center.
The center theorem is reused from the official kit, not a new discovery. -/
@[expose] public section
namespace EndpointCountermodel
open Ruliology.CellularAutomata Rule30Jen Rule30Realization
open EndpointTransport (rectangle rectangle_translate)

def localRule (g : Bool → Bool → Bool) (l c r : Bool) : Bool := xor l (g c r)

def fillFor (g : Bool → Bool → Bool) (a b : Bool) : List Bool → Nat → Bool
  | [],0 => a
  | [],_+1 => b
  | y::ys,0 => localRule g y (fillFor g a b ys 0) (fillFor g a b ys 1)
  | _::ys,i+1 => fillFor g a b ys i

theorem left_inverse (g : Bool → Bool → Bool) (y a b : Bool) :
    localRule g (localRule g y a b) a b=y := by
  exact xor_xor_cancel y (g a b)

theorem fill_step (g : Bool → Bool → Bool) (a b : Bool) (ys : List Bool)
    (i : Nat) (h : i<ys.length) :
    localRule g (fillFor g a b ys i) (fillFor g a b ys (i+1))
      (fillFor g a b ys (i+2))=ys[i] := by
  induction ys generalizing i with
  | nil => simp at h
  | cons y ys ih =>
    cases i with
    | zero => simp only [fillFor,List.getElem_cons_zero];exact left_inverse _ _ _ _
    | succ i => simpa only [fillFor,List.getElem_cons_succ] using ih i (by simpa using h)

theorem fill_right0 (g : Bool → Bool → Bool) (a b : Bool) (ys : List Bool) :
    fillFor g a b ys ys.length=a := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simpa only [List.length_cons,fillFor] using ih

theorem fill_right1 (g : Bool → Bool → Bool) (a b : Bool) (ys : List Bool) :
    fillFor g a b ys (ys.length+1)=b := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simpa only [List.length_cons,fillFor] using ih

def EndpointComplete (g : Bool → Bool → Bool) : Prop :=
  ∀ (ys : List Bool) (f : Bool → (Fin ys.length → Bool) → Bool → Bool),
    rectangle (fun l r => f
      (localRule g l (fillFor g false false ys 0) (fillFor g false false ys 1))
      (fun i => localRule g (fillFor g false false ys i.val)
        (fillFor g false false ys (i.val+1)) (fillFor g false false ys (i.val+2)))
      (localRule g (fillFor g false false ys ys.length)
        (fillFor g false false ys (ys.length+1)) r))=
    rectangle (fun l r => f l (fun i => ys[i]) r)

theorem endpoint_complete (g : Bool → Bool → Bool) (hg : ∀ r, g false r=r) :
    EndpointComplete g := by
  intro ys f
  have hm : (fun i : Fin ys.length => localRule g (fillFor g false false ys i.val)
      (fillFor g false false ys (i.val+1)) (fillFor g false false ys (i.val+2)))=
      (fun i : Fin ys.length => ys[i]) := by
    funext i
    exact fill_step g false false ys i.val i.isLt
  rw [hm,fill_right0,fill_right1]
  simp only [localRule,hg,Bool.false_xor]
  exact rectangle_translate (fun l r => f l (fun i => ys[i]) r)
    (g (fillFor g false false ys 0) (fillFor g false false ys 1))

/-- All-width endpoint control coexists with a periodic single-seed center. -/
theorem endpoint_complete_periodic_center :
    ∃ g : Bool → Bool → Bool,
      EndpointComplete g ∧ EventuallyPeriodic (fun t => run g t 0) := by
  refine ⟨g210,endpoint_complete g210 ?_,1,1,by decide,?_⟩
  · intro r
    cases r <;> rfl
  · intro t ht
    obtain ⟨s,rfl⟩ : ∃ s, t=s+1 := ⟨t-1,by omega⟩
    change run g210 (s+1+1) 0=run g210 (s+1) 0
    rw [center210,center210]

theorem endpoint_control_does_not_imply_seed_aperiodicity :
    ¬ (∀ g : Bool → Bool → Bool,
      EndpointComplete g → ¬ EventuallyPeriodic (fun t => run g t 0)) := by
  intro h
  obtain ⟨g,hg,hp⟩ := endpoint_complete_periodic_center
  exact h g hg hp

end EndpointCountermodel
