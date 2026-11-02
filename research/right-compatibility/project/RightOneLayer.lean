module
public import Ruliology.CellularAutomata.Rule30Jen
public import Ruliology.CellularAutomata.Rule30Prize
@[expose] public section
namespace RightOneLayer
open Ruliology.CellularAutomata.Rule30Jen

/-- The value forced in the first right column when the center is white. -/
def forced (c ell : Nat → Bool) (t : Nat) : Bool := xor (ell t) (c (t+1))

/-- Exact one-right-column compatibility. A black right cell forces its successor;
at a white right cell a free farther-right input can choose either successor. -/
def Compatible (c ell : Nat → Bool) : Prop :=
  ∃ r : Nat → Bool, (∀ t,c (t+1)=rule (ell t) (c t) (r t)) ∧
    (∀ t,r t=true → r (t+1)= !c t)

def Conditions (c ell : Nat → Bool) : Prop :=
  (∀ t,c t=true → ell t= !c (t+1)) ∧
  (∀ t,c t=false → c (t+1)=false → forced c ell t=true → forced c ell (t+1)=true) ∧
  (∀ t,c t=false → c (t+1)=true → c (t+2)=false →
    forced c ell t=true → forced c ell (t+2)=false)

theorem coupling_forces {c ell r : Nat → Bool}
    (hc : ∀ t,c (t+1)=rule (ell t) (c t) (r t)) (t : Nat) (ht : c t=false) :
    r t=forced c ell t := by
  have h:=hc t
  rw [ht] at h
  unfold forced
  rw [h]
  cases ell t <;> cases r t <;> rfl

theorem necessary {c ell : Nat → Bool} (h : Compatible c ell) : Conditions c ell := by
  obtain ⟨r,hc,hr⟩:=h
  refine ⟨?_,?_,?_⟩
  · intro t ht
    have he:=hc t
    rw [ht] at he
    rw [he]
    cases ell t <;> cases r t <;> rfl
  · intro t h0 h1 hf
    have hrt : r t=true := by rw [coupling_forces hc t h0,hf]
    have hrt1:=hr t hrt
    rw [h0,coupling_forces hc (t+1) h1] at hrt1
    exact hrt1
  · intro t h0 h1 h2 hf
    have hrt : r t=true := by rw [coupling_forces hc t h0,hf]
    have hrt1 : r (t+1)=true := by simpa [h0] using hr t hrt
    have hrt2:=hr (t+1) hrt1
    rw [show t+1+1=t+2 by omega,h1,coupling_forces hc (t+2) h2] at hrt2
    exact hrt2

def witness (c ell : Nat → Bool) : Nat → Bool
  | 0 => if c 0 then false else forced c ell 0
  | t+1 => if c (t+1) then (!c t && forced c ell t) else forced c ell (t+1)

theorem witness_white (c ell : Nat → Bool) (t : Nat) (ht : c t=false) :
    witness c ell t=forced c ell t := by
  cases t <;> simp [witness,ht]

theorem witness_couples {c ell : Nat → Bool} (hp : ∀ t,c t=true → ell t= !c (t+1)) :
    ∀ t,c (t+1)=rule (ell t) (c t) (witness c ell t) := by
  intro t
  cases hc : c t with
  | false =>
    rw [witness_white c ell t hc]
    unfold forced
    cases ell t <;> cases c (t+1) <;> rfl
  | true =>
    rw [hp t hc]
    cases c (t+1) <;> cases witness c ell t <;> rfl

theorem witness_step {c ell : Nat → Bool} (h : Conditions c ell) :
    ∀ t,witness c ell t=true → witness c ell (t+1)= !c t := by
  intro t hr
  cases hc : c t with
  | false =>
    have hf : forced c ell t=true := by rwa [witness_white c ell t hc] at hr
    cases hn : c (t+1) with
    | false =>
      rw [witness_white c ell (t+1) hn]
      exact h.2.1 t hc hn hf
    | true => simp [witness,hc,hn,hf]
  | true =>
    cases t with
    | zero => simp [witness,hc] at hr
    | succ t =>
      have hh : c t=false ∧ forced c ell t=true := by
        simpa [witness,hc] using hr
      cases hn : c (t+1+1) with
      | true => simp [witness,hc,hn]
      | false =>
        rw [witness_white c ell (t+1+1) hn]
        exact h.2.2 t hh.1 hc hn hh.2

theorem sufficient {c ell : Nat → Bool} (h : Conditions c ell) : Compatible c ell :=
  ⟨witness c ell,witness_couples h.1,witness_step h⟩

/-- A finite list of local temporal conditions is exact for ONE right column.
It does not assert an infinite right extension, or a finite right origin. -/
theorem compatible_iff (c ell : Nat → Bool) : Compatible c ell ↔ Conditions c ell :=
  ⟨necessary,sufficient⟩

theorem compatible_iff_free_outer (c ell : Nat → Bool) : Compatible c ell ↔
    ∃ r b : Nat → Bool,
      (∀ t,c (t+1)=rule (ell t) (c t) (r t)) ∧
      (∀ t,r (t+1)=rule (c t) (r t) (b t)) := by
  constructor
  · rintro ⟨r,hc,hr⟩
    refine ⟨r,(fun t=>xor (c t) (r (t+1))),hc,?_⟩
    intro t
    dsimp only
    cases ht : r t with
    | false => cases c t <;> cases r (t+1) <;> rfl
    | true => rw [hr t ht]; cases c t <;> rfl
  · rintro ⟨r,b,hc,hr⟩
    refine ⟨r,hc,?_⟩
    intro t ht
    rw [hr t,ht]
    cases c t <;> cases b t <;> rfl

#print axioms compatible_iff
#print axioms compatible_iff_free_outer
end RightOneLayer
