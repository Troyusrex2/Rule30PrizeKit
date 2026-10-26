import RootEventHeight

/-! All-time span-one white height forces isolated temporal transitions once
the genuine no11011 property is supplied. No return completeness is assumed. -/
namespace HeightOneLogic
open RootEventHeight
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def WH (b : Nat → Bool) (t : Nat) : Int := height (fun s => !b s) t
def SpanOne (b : Nat → Bool) : Prop := ∃ lo : Int, ∀ t, lo ≤ WH b t ∧ WH b t ≤ lo+1
def Periodic (b : Nat → Bool) (P : Nat) : Prop := ∀ t, b (t+P)=b t
def No11011 (b : Nat → Bool) : Prop := ∀ t,
  ¬ (b t=true ∧ b (t+1)=true ∧ b (t+2)=false ∧ b (t+3)=true ∧ b (t+4)=true)
def D (b : Nat → Bool) (t : Nat) : Bool := xor (b t) (b (t+1))

theorem sign_add (t s : Nat) : sign (t+s)=sign t*sign s := by
  simp [sign,pow_add]

theorem white_height_step (b : Nat → Bool) (t : Nat) :
    WH b (t+1)=WH b t+sign t*bit (!b t) := height_succ _ _

theorem height_shift_period (b : Nat → Bool) (P : Nat) (he : Even P)
    (hp : Periodic b P) (t : Nat) : WH b (P+t)=WH b P+WH b t := by
  induction t with
  | zero => simp [WH,height_zero]
  | succ t ih =>
      rw [show P+(t+1)=(P+t)+1 by omega,white_height_step,ih,white_height_step]
      rw [sign_add,sign_even P he]
      have h := hp t
      rw [Nat.add_comm t P] at h
      rw [h]
      ring

theorem span_one_of_closed_period (b : Nat → Bool) (P : Nat)
    (hP : 0<P) (he : Even P) (hp : Periodic b P) (hc : WH b P=0)
    (hr : ∃ lo : Int, ∀ t, t≤P → lo≤WH b t ∧ WH b t≤lo+1) : SpanOne b := by
  obtain ⟨lo,hr⟩ := hr
  refine ⟨lo,?_⟩
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      by_cases ht : t≤P
      · exact hr t ht
      · have ht' : t-P<t := by omega
        have hw := height_shift_period b P he hp (t-P)
        rw [show P+(t-P)=t by omega,hc,zero_add] at hw
        rw [hw]
        exact ih (t-P) ht'

theorem no010 (b : Nat → Bool) (hs : SpanOne b) (t : Nat) :
    ¬ (b t=false ∧ b (t+1)=true ∧ b (t+2)=false) := by
  rintro ⟨h0,h1,h2⟩
  obtain ⟨lo,hl⟩ := hs
  have a := hl t
  have c := hl (t+3)
  have hheight : WH b (t+3)=WH b t+2*sign t := by
    rw [show t+3=(t+2)+1 by omega,white_height_step,
      show t+2=(t+1)+1 by omega,white_height_step,white_height_step]
    rw [show t+1+1=t+2 by omega]
    simp [h0,h1,h2,bit,sign_succ]
    ring
  rcases sign_cases t with ht|ht <;> rw [ht] at hheight <;> omega

theorem no101 (b : Nat → Bool) (hs : SpanOne b) (hn : No11011 b)
    (P : Nat) (hP : 0<P) (hp : Periodic b P) (t : Nat) :
    ¬ (b t=true ∧ b (t+1)=false ∧ b (t+2)=true) := by
  rintro ⟨h0,h1,h2⟩
  let s := t+P-1
  have e0 : b (s+1)=true := by
    rw [show s+1=t+P by simp only [s];omega,hp t];exact h0
  have e1 : b (s+2)=false := by
    rw [show s+2=(t+1)+P by simp only [s];omega,hp (t+1)];exact h1
  have e2 : b (s+3)=true := by
    rw [show s+3=(t+2)+P by simp only [s];omega,hp (t+2)];exact h2
  have before : b s=true := by
    cases hb : b s with
    | true => rfl
    | false => exact False.elim (no010 b hs s ⟨hb,e0,e1⟩)
  have after : b (s+4)=true := by
    cases hb : b (s+4) with
    | true => rfl
    | false =>
        exact False.elim (no010 b hs (s+2) ⟨e1,by simpa [Nat.add_assoc] using e2,
          by simpa [Nat.add_assoc] using hb⟩)
  exact hn s ⟨before,e0,e1,e2,after⟩

theorem isolated_derivative (b : Nat → Bool) (hs : SpanOne b) (hn : No11011 b)
    (P : Nat) (hP : 0<P) (hp : Periodic b P) (t : Nat) :
    ¬ (D b t=true ∧ D b (t+1)=true) := by
  have h0 := no010 b hs t
  have h1 := no101 b hs hn P hP hp t
  have localFact : ∀ x y z : Bool, xor x y=true → xor y z=true →
      (x=false ∧ y=true ∧ z=false) ∨ (x=true ∧ y=false ∧ z=true) := by decide +kernel
  rintro ⟨e0,e1⟩
  change xor (b t) (b (t+1))=true at e0
  change xor (b (t+1)) (b (t+1+1))=true at e1
  rw [show t+1+1=t+2 by omega] at e1
  rcases localFact _ _ _ e0 e1 with h|h
  · exact h0 h
  · exact h1 h

theorem twin_local : ∀ a u v w an un : Bool,
    (an || un)=false → xor a an=(u || v) → xor u un=(v || w) →
    a=(a || u) ∧ u=(a || u) := by decide +kernel

theorem isolated_forces_twins (b a u v w : Nat → Bool)
    (hb : ∀ t, D b t=(a t || u t))
    (ha : ∀ t, xor (a t) (a (t+1))=(u t || v t))
    (hu : ∀ t, xor (u t) (u (t+1))=(v t || w t))
    (hi : ∀ t, ¬ (D b t=true ∧ D b (t+1)=true)) :
    (∀ t, a t=D b t) ∧ (∀ t, u t=D b t) := by
  have both (t : Nat) : a t=D b t ∧ u t=D b t := by
    cases hd : D b t with
    | false =>
        have h := hb t
        rw [hd] at h
        have localFact : ∀ x y : Bool, (x || y)=false → x=false ∧ y=false := by decide +kernel
        exact localFact _ _ h.symm
    | true =>
        have hz : D b (t+1)=false := by
          cases hz : D b (t+1) with
          | false => rfl
          | true => exact False.elim (hi t ⟨hd,hz⟩)
        have hnext : (a (t+1) || u (t+1))=false := (hb (t+1)).symm.trans hz
        have h := twin_local (a t) (u t) (v t) (w t) (a (t+1)) (u (t+1)) hnext (ha t) (hu t)
        rw [← hb t] at h
        simpa only [hd] using h
  exact ⟨fun t => (both t).1,fun t => (both t).2⟩

end HeightOneLogic

