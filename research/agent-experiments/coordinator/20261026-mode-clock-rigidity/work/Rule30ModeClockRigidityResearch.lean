module
public import Rule30ClockModeResearch

/-! A clock-preservation theorem for the lower readout when its driver
flips at a smaller clock. It does not invert the observation or assert
that the hidden mode is an actual profile. -/
@[expose] public section
namespace Rule30ModeClockRigidityResearch
open Rule30CommonPastResearch
open Rule30ClockJetResearch
open Rule30ClockModeResearch
set_option maxHeartbeats 4000000

theorem shifted_mode_step (a b k : Bool) :
    xor (xor a (!(xor k true))) (xor b (!k))=xor (xor a b) true := by
  cases a <;> cases b <;> cases k <;> rfl

theorem mode_mask_gate (q k l v : Bool)
    (hs : ((xor q v) || (!(xor k true) && !l))=(q || (!k && !l)))
    (hv : v=true) : q=k ∧ l=false := by
  subst v
  cases q <;> cases k <;> cases l <;> simp_all

theorem mode_mask_gate_free (q k l r v : Bool)
    (hs : ((xor q v) || (!(xor k true) && !r))=(q || (!k && !l)))
    (hv : v=true) : q=k ∧ (k=false → l=false) := by
  subst v
  cases q <;> cases k <;> cases l <;> cases r <;> simp_all

theorem two_gate_flat (q0 q1 q2 k0 k1 k2 l0 l1 m0 m1 n0 : Bool)
    (h0 : q0=k0) (h2 : q2=k2) (hl : l0=false)
    (hq0 : q1=xor q0 (!k0)) (hq1 : q2=xor q1 (!k1))
    (hk0 : k1=xor k0 (l0 || m0))
    (hk1 : k2=xor k1 (l1 || m1))
    (hl0 : l1=xor l0 (m0 || n0)) : k1=k0 ∧ k2=k1 := by
  have ha : q1=true := by
    rw [hq0,h0];cases k0 <;> rfl
  have hb : k2=k1 := by
    rw [←h2,hq1,ha];cases k1 <;> rfl
  have gate : ∀ b c d : Bool, b=xor b (c || d) → c=false ∧ d=false := by decide
  have hz := gate k1 l1 m1 (by rw [←hk1,hb])
  have hm : m0=false := by
    have he := hl0
    rw [hl,hz.1] at he
    have gate0 : ∀ b c : Bool, false=xor false (b || c) → b=false := by decide
    exact gate0 m0 n0 he
  have hc : k1=k0 := by
    simpa only [hl,hm,Bool.false_or,Bool.xor_false] using hk0
  exact ⟨hc,hb⟩

theorem two_gate_down (q0 q1 q2 k0 k1 k2 l0 l1 m0 m1 n0 : Bool)
    (h0 : q0=k0) (h2 : q2=k2) (hl : k0=false → l0=false)
    (hq0 : q1=xor q0 (!k0)) (hq1 : q2=xor q1 (!k1))
    (hk0 : k1=xor k0 (l0 || m0))
    (hk1 : k2=xor k1 (l1 || m1))
    (hl0 : l1=xor l0 (m0 || n0)) :
    (k1=true → k0=true) ∧ k2=k1 := by
  have ha : q1=true := by rw [hq0,h0];cases k0 <;> rfl
  have hb : k2=k1 := by rw [←h2,hq1,ha];cases k1 <;> rfl
  refine ⟨?_,hb⟩
  intro h1
  cases hx : k0 with
  | true => rfl
  | false =>
    have hf := (two_gate_flat _ _ _ _ _ _ _ _ _ _ _ h0 h2 (hl hx)
      hq0 hq1 hk0 hk1 hl0).1
    rw [h1,hx] at hf
    cases hf

/-- A repeating readout would prevent the antiperiodic driver from ever
rising after time one. No period premise on q or l is used. -/
theorem mode_readout_no_half_clock (q k l m n : Nat → Bool) (R : Nat)
    (hq : ∀ t, q (t+1)=xor (q t) (!k t))
    (hk : ∀ t, k (t+1)=xor (k t) (l t || m t))
    (hl : ∀ t, l (t+1)=xor (l t) (m t || n t))
    (hka : ∀ t, k (t+R)=xor (k t) true) :
    ¬(∀ t, (q (t+R) || (!k (t+R) && !l (t+R)))=
      (q t || (!k t && !l t))) := by
  intro ho
  let v := fun t => xor (q (t+R)) (q t)
  have vs : ∀ t, v (t+1)=xor (v t) true := by
    intro t;unfold v
    rw [show t+1+R=(t+R)+1 by omega,hq (t+R),hq t,hka t]
    exact shifted_mode_step _ _ _
  have gate : ∀ t, v t=true → q t=k t ∧ (k t=false → l t=false) := by
    intro t hv
    have hs := ho t
    rw [hka t] at hs
    have he : q (t+R)=xor (q t) (v t) :=
      Rule30OrClockObserverResearch.xor_recover _ _ _ rfl
    rw [he] at hs
    exact mode_mask_gate_free _ _ _ _ _ hs hv
  have local_down : ∀ t, v t=true →
      (k (t+1)=true → k t=true) ∧ k (t+1+1)=k (t+1) := by
    intro t hv
    have hv2 : v (t+1+1)=true := by
      rw [vs (t+1),vs t,hv];rfl
    have ga := gate t hv
    have gb := gate (t+1+1) hv2
    exact two_gate_down _ _ _ _ _ _ _ _ _ _ _ ga.1 gb.1 ga.2
      (hq t) (hq (t+1)) (hk t) (hk (t+1)) (hl t)
  have no_rise : ∀ t, k (t+1)=false → k (t+1+1)=false := by
    intro t hf
    cases hv : v t with
    | false =>
      have hn : v (t+1)=true := by rw [vs t,hv];rfl
      have down := (local_down (t+1) hn).1
      have gate0 : ∀ b c : Bool, (c=true → b=true) → b=false → c=false := by decide
      exact gate0 _ _ down hf
    | true => rw [(local_down t hv).2];exact hf
  have hz : ∃ s, k (s+1)=false := by
    cases hx : k 1 with
    | false => exact ⟨0,hx⟩
    | true =>
      refine ⟨R,?_⟩
      simpa [hx,Nat.add_comm] using hka 1
  obtain ⟨s,hs⟩ := hz
  have future : ∀ i, k (s+1+i)=false := by
    intro i
    induction i with
    | zero => exact hs
    | succ i ih =>
      rw [show s+1+(i+1)=(s+i)+1+1 by omega]
      apply no_rise (s+i)
      simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ih
  have hf := hka (s+1)
  rw [future R,hs] at hf
  have hn : (false : Bool)≠xor false true := by decide
  exact hn hf

theorem actual_lower_readout_no_half_clock (a : Nat → Nat → Bool) (ha : Actual a)
    (j R : Nat)
    (hh : ∀ t, a (t+2*R) (j+4)=xor (a t (j+4)) true)
    (hk : ∀ t, a (t+R) (j+3)=xor (a t (j+3)) true) :
    ¬(∀ t, lowerReadout (fun s => a s (j+5)) (fun s => a s (j+4)) (2*R) (t+R)=
      lowerReadout (fun s => a s (j+5)) (fun s => a s (j+4)) (2*R) t) := by
  have hk2 : ∀ t, a (t+2*R) (j+3)=a t (j+3) := by
    intro t
    rw [show t+2*R=(t+R)+R by omega,hk (t+R),hk t]
    cases a t (j+3) <;> rfl
  have gs : ∀ t, a (t+1) (j+5)=xor (a t (j+5)) (a t (j+4) || a t (j+3)) :=
    fun t => ha t (j+5)
  have hs : ∀ t, a (t+1) (j+4)=xor (a t (j+4)) (a t (j+3) || a t (j+2)) :=
    fun t => ha t (j+4)
  have readout := lower_readout_eq (fun s => a s (j+5)) (fun s => a s (j+4))
    (fun s => a s (j+3)) (fun s => a s (j+2)) (2*R) gs hs hh hk2
  have qs := shift_difference_step (fun s => a s (j+5)) (fun s => a s (j+4))
    (fun s => a s (j+3)) (2*R) gs hh hk2
  intro ho
  apply mode_readout_no_half_clock (delta (fun s => a s (j+5)) (2*R))
    (fun s => a s (j+3)) (fun s => a s (j+2)) (fun s => a s (j+1))
    (fun s => a s j) R qs (fun t => ha t (j+3)) (fun t => ha t (j+2)) hk
  intro t
  rw [←readout (t+R),←readout t]
  exact ho t

end Rule30ModeClockRigidityResearch
