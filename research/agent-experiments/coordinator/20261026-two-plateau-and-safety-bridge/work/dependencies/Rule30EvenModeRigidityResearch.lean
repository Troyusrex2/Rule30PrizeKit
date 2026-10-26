module
public import Rule30ClockModeResearch

/-! A constant lower readout is impossible at every even plateau clock.
This is a local clock-rigidity theorem, not a general mode inverse. -/
@[expose] public section
namespace Rule30EvenModeRigidityResearch
open Rule30CommonPastResearch
open Rule30ClockJetResearch
open Rule30ClockModeResearch
set_option maxHeartbeats 4000000

theorem support_gate (q k l m n : Bool)
    (h0 : (q || (!k && !l))=true)
    (h1 : (xor q (!k) || (!(xor k (l || m)) && !n))=true) :
    (k || l)=k := by
  cases q <;> cases k <;> cases l <;> cases m <;> cases n <;> simp_all

theorem constant_readout_driver (q k l m : Nat → Bool)
    (hq : ∀ t, q (t+1)=xor (q t) (!k t))
    (hk : ∀ t, k (t+1)=xor (k t) (l t || m t))
    (ho : ∀ t, (q t || (!k t && !l t))=true) :
    ∀ t, (k t || l t)=k t := by
  intro t
  have h1 := ho (t+1)
  rw [hq t,hk t] at h1
  exact support_gate _ _ _ _ _ (ho t) h1

theorem paired_flip (h q k : Bool) :
    xor (xor h k) (xor q (!k))=xor (xor h q) true := by
  cases h <;> cases q <;> cases k <;> rfl

theorem even_flip_return (z : Nat → Bool)
    (hs : ∀ t, z (t+1)=xor (z t) true) (n : Nat) :
    ∀ t, z (t+2*n)=z t := by
  have hs2 : ∀ t, z (t+2)=z t := by
    intro t
    rw [show t+2=(t+1)+1 by omega,hs (t+1),hs t]
    cases z t <;> rfl
  induction n with
  | zero => intro t;simp
  | succ n ih =>
    intro t
    rw [Nat.mul_succ,show t+(2*n+2)=(t+2*n)+2 by omega,hs2,ih]

theorem even_constant_mode_impossible (q h k l m : Nat → Bool) (n : Nat)
    (hq : ∀ t, q (t+1)=xor (q t) (!k t))
    (hh : ∀ t, h (t+1)=xor (h t) (k t || l t))
    (hk : ∀ t, k (t+1)=xor (k t) (l t || m t))
    (hqp : ∀ t, q (t+2*n)=q t)
    (hhp : ∀ t, h (t+2*n)=xor (h t) true)
    (ho : ∀ t, (q t || (!k t && !l t))=true) : False := by
  have hi := constant_readout_driver q k l m hq hk ho
  let z := fun t => xor (h t) (q t)
  have hz : ∀ t, z (t+1)=xor (z t) true := by
    intro t;unfold z
    rw [hh t,hq t,hi t]
    exact paired_flip _ _ _
  have he : z (2*n)=z 0 := by
    simpa only [Nat.zero_add] using even_flip_return z hz n 0
  have hh0 : h (2*n)=xor (h 0) true := by simpa only [Nat.zero_add] using hhp 0
  have hq0 : q (2*n)=q 0 := by simpa only [Nat.zero_add] using hqp 0
  have hf : z (2*n)=xor (z 0) true := by
    unfold z;rw [hh0,hq0]
    cases h 0 <;> cases q 0 <;> rfl
  rw [he] at hf
  have hn : ∀ b : Bool, b ≠ xor b true := by
    intro b;cases b <;> decide
  exact hn (z 0) hf

theorem actual_even_plateau_readout (a : Nat → Nat → Bool) (ha : Actual a) (j n : Nat)
    (hh : ∀ t, a (t+2*n) (j+3)=xor (a t (j+3)) true)
    (hk : ∀ t, a (t+2*n) (j+2)=a t (j+2))
    (hg : ∀ t, a (t+2*(2*n)) (j+4)=a t (j+4)) :
    ¬(∀ t, lowerReadout (fun s => a s (j+4)) (fun s => a s (j+3)) (2*n) t=true) := by
  intro ho
  have data := actual_lower_observer_data a ha (j+1) (2*n) hh hk hg
  apply even_constant_mode_impossible (fun t => delta (fun s => a s (j+4)) (2*n) t)
    (fun t => a t (j+3)) (fun t => a t (j+2)) (fun t => a t (j+1)) (fun t => a t j) n
    data.1 (fun t => ha t (j+3)) (fun t => ha t (j+2)) data.2.2 hh
  intro t;rw [←data.2.1 t];exact ho t

theorem actual_even_plateau_or_nonconstant (a : Nat → Nat → Bool) (ha : Actual a) (j n : Nat)
    (hh : ∀ t, a (t+2*n) (j+3)=xor (a t (j+3)) true)
    (hk : ∀ t, a (t+2*n) (j+2)=a t (j+2))
    (hg : ∀ t, a (t+2*(2*n)) (j+4)=a t (j+4)) :
    ¬(∃ b : Bool, ∀ t, (a t (j+4) || a t (j+3))=b) := by
  intro ⟨b,hb⟩
  apply actual_even_plateau_readout a ha j n hh hk hg
  intro t
  simp only [lowerReadout,delta,orTrace,hb]
  cases b <;> rfl

theorem periodic_or_with_anti_mask (g h : Nat → Bool) (P : Nat)
    (hh : ∀ t, h (t+P)=xor (h t) true)
    (hr : ∀ t, (g (t+P) || h (t+P))=(g t || h t)) :
    ∀ t, (g t || h t)=true := by
  intro t
  have he := hr t
  rw [hh t] at he
  have gate : ∀ (g0 h0 g1 : Bool),
      (g1 || xor h0 true)=(g0 || h0) → (g0 || h0)=true := by
    intro g0 h0 g1 hx
    cases g0 <;> cases h0 <;> cases g1 <;> simp_all
  exact gate _ _ _ he

theorem actual_even_plateau_or_no_half_period (a : Nat → Nat → Bool) (ha : Actual a) (j n : Nat)
    (hh : ∀ t, a (t+2*n) (j+3)=xor (a t (j+3)) true)
    (hk : ∀ t, a (t+2*n) (j+2)=a t (j+2))
    (hg : ∀ t, a (t+2*(2*n)) (j+4)=a t (j+4)) :
    ¬(∀ t, (a (t+2*n) (j+4) || a (t+2*n) (j+3))=
      (a t (j+4) || a t (j+3))) := by
  intro hr
  exact actual_even_plateau_or_nonconstant a ha j n hh hk hg
    ⟨true,periodic_or_with_anti_mask _ _ (2*n) hh hr⟩

/-- A constant saturated OR trace supplies the double-period premise itself. -/
theorem constant_or_forces_double_period (g h k : Nat → Bool) (P : Nat)
    (gs : ∀ t, g (t+1)=xor (g t) (h t || k t))
    (hh : ∀ t, h (t+P)=xor (h t) true)
    (hk : ∀ t, k (t+P)=k t)
    (hr : ∀ t, (g t || h t)=true) :
    ∀ t, g (t+2*P)=g t := by
  obtain ⟨e,_,he⟩ := plateau_or_double g h k P gs hh hk
  have hh2 : ∀ t, h (t+2*P)=h t := by
    intro t
    rw [show t+2*P=(t+P)+P by omega,hh (t+P),hh t]
    cases h t <;> rfl
  have hz : ∃ s, h s=false := by
    cases hx : h 0 with
    | false => exact ⟨0,hx⟩
    | true =>
      refine ⟨P,?_⟩
      have ht := hh 0
      simpa [hx] using ht
  obtain ⟨s,hs⟩ := hz
  have ga : g s=true := by simpa only [hs,Bool.or_false] using hr s
  have gb : g (s+2*P)=true := by
    simpa only [hh2 s,hs,Bool.or_false] using hr (s+2*P)
  have hf := he s
  rw [ga,gb] at hf
  have gate : ∀ e : Bool, true=xor true e → e=false := by decide
  have he0 := gate e hf
  intro t
  simpa only [he0,Bool.xor_false] using he t

/-- No assumption about the newer profile's period or finite white ancestry. -/
theorem actual_even_plateau_or_clock_rigidity
    (a : Nat → Nat → Bool) (ha : Actual a) (j n : Nat)
    (hh : ∀ t, a (t+2*n) (j+3)=xor (a t (j+3)) true)
    (hk : ∀ t, a (t+2*n) (j+2)=a t (j+2)) :
    ¬(∀ t, (a (t+2*n) (j+4) || a (t+2*n) (j+3))=
      (a t (j+4) || a t (j+3))) := by
  intro hr
  have hc := periodic_or_with_anti_mask (fun t => a t (j+4))
    (fun t => a t (j+3)) (2*n) hh hr
  have hg := constant_or_forces_double_period (fun t => a t (j+4))
    (fun t => a t (j+3)) (fun t => a t (j+2)) (2*n)
    (fun t => ha t (j+4)) hh hk hc
  exact actual_even_plateau_or_no_half_period a ha j n hh hk hg hr

end Rule30EvenModeRigidityResearch
