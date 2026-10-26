module
public import Rule30ClockJetResearch

/-! A lower-clock observable in the plateau case. The hidden mode is a
linear accumulator of a complemented actual profile. It is not asserted
to be an actual row or to belong to the original observer's input class. -/
@[expose] public section
namespace Rule30ClockModeResearch
open Rule30ClockJetResearch
open Rule30CommonPastResearch
set_option maxHeartbeats 4000000

def lowerReadout (g h : Nat → Bool) (P t : Nat) : Bool :=
  !(xor (delta (orTrace g h) P (t+1)) (delta (orTrace g h) P t))

theorem lower_gate (q h k l : Bool) :
    (!(!q && xor (xor h (k || l)) h))=(q || (!k && !l)) := by
  cases q <;> cases h <;> cases k <;> cases l <;> rfl

theorem lower_readout_eq (g h k l : Nat → Bool) (P : Nat)
    (gs : ∀ t, g (t+1)=xor (g t) (h t || k t))
    (hs : ∀ t, h (t+1)=xor (h t) (k t || l t))
    (hh : ∀ t, h (t+P)=xor (h t) true) (hk : ∀ t, k (t+P)=k t) :
    ∀ t, lowerReadout g h P t=(delta g P t || (!k t && !l t)) := by
  intro t
  rw [lowerReadout,shift_or_difference g h k l P gs hs hh hk t,hs t]
  exact lower_gate _ _ _ _

theorem mode_periodic (g : Nat → Bool) (P : Nat)
    (hg : ∀ t, g (t+2*P)=g t) : ∀ t, delta g P (t+P)=delta g P t := by
  intro t;unfold delta
  rw [show t+P+P=t+2*P by omega,hg t]
  exact Bool.xor_comm _ _

theorem actual_lower_observer_data (a : Nat → Nat → Bool) (ha : Actual a) (j P : Nat)
    (hh : ∀ t, a (t+P) (j+2)=xor (a t (j+2)) true)
    (hk : ∀ t, a (t+P) (j+1)=a t (j+1))
    (hg : ∀ t, a (t+2*P) (j+3)=a t (j+3)) :
    (∀ t, delta (fun s => a s (j+3)) P (t+1)=
      xor (delta (fun s => a s (j+3)) P t) (!a t (j+1))) ∧
    (∀ t, lowerReadout (fun s => a s (j+3)) (fun s => a s (j+2)) P t=
      (delta (fun s => a s (j+3)) P t || (!a t (j+1) && !a t j))) ∧
    (∀ t, delta (fun s => a s (j+3)) P (t+P)=delta (fun s => a s (j+3)) P t) := by
  have gs : ∀ t, a (t+1) (j+3)=xor (a t (j+3)) (a t (j+2) || a t (j+1)) := fun t => ha t (j+3)
  have hs : ∀ t, a (t+1) (j+2)=xor (a t (j+2)) (a t (j+1) || a t j) := fun t => ha t (j+2)
  exact ⟨shift_difference_step _ _ _ P gs hh hk,
    lower_readout_eq _ _ _ _ P gs hs hh hk,mode_periodic _ P hg⟩

theorem complemented_driver_recovered (q k : Nat → Bool)
    (hs : ∀ t, q (t+1)=xor (q t) (!k t)) :
    ∀ t, k t= !(xor (q (t+1)) (q t)) := by
  intro t;rw [hs t]
  cases q t <;> cases k t <;> rfl

theorem older_recovered_of_modes_equal (q r k l : Nat → Bool)
    (hq : ∀ t, q (t+1)=xor (q t) (!k t))
    (hr : ∀ t, r (t+1)=xor (r t) (!l t)) (he : ∀ t, q t=r t) :
    ∀ t, k t=l t := by
  intro t
  rw [complemented_driver_recovered q k hq t,
      complemented_driver_recovered r l hr t,he (t+1),he t]

def xsum : Nat → (Nat → Bool) → Bool
  | 0,_ => false
  | n+1,f => xor (f 0) (xsum n (fun t => f (t+1)))

theorem xor_grid (a b c d : Bool) :
    xor (xor a b) (xor c d)=xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem xsum_xor (n : Nat) (f g : Nat → Bool) :
    xsum n (fun t => xor (f t) (g t))=xor (xsum n f) (xsum n g) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [xsum,ih];exact xor_grid _ _ _ _

theorem xsum_not (n : Nat) (f : Nat → Bool) :
    xsum n (fun t => !f t)=xor (xsum n f) (xsum n (fun _ => true)) := by
  have he : (fun t => !f t)=(fun t => xor (f t) true) := by
    funext t;cases f t <;> rfl
  rw [he,xsum_xor]

theorem xsum_difference (n : Nat) (f : Nat → Bool) :
    xsum n (fun t => xor (f (t+1)) (f t))=xor (f n) (f 0) := by
  induction n generalizing f with
  | zero => simp only [xsum];cases f 0 <;> rfl
  | succ n ih =>
    rw [xsum,show (fun t => xor (f (t+1+1)) (f (t+1)))=
      (fun t => xor ((fun s => f (s+1)) (t+1)) ((fun s => f (s+1)) t)) by rfl,ih (fun s => f (s+1))]
    cases f 0 <;> cases f 1 <;> cases f (n+1) <;> rfl

theorem derived_readout_parity (r : Nat → Bool) (P : Nat)
    (hr : ∀ t, r (t+2*P)=r t) :
    xsum P (fun t => !(xor (delta r P (t+1)) (delta r P t)))=
      xsum P (fun _ => true) := by
  have hp : delta r P P=delta r P 0 := by
    simpa only [Nat.zero_add] using mode_periodic r P hr 0
  rw [xsum_not,xsum_difference,hp]
  cases delta r P 0 <;> cases xsum P (fun _ => true) <;> rfl

theorem xsum_true_even (n : Nat) : xsum (2*n) (fun _ => true)=false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega]
    simp only [xsum,ih];rfl

theorem lower_readout_parity (g h : Nat → Bool) (P : Nat)
    (hg : ∀ t, g (t+2*P)=g t) (hh : ∀ t, h (t+P)=xor (h t) true) :
    xsum P (lowerReadout g h P)=xsum P (fun _ => true) := by
  have hh2 : ∀ t, h (t+2*P)=h t := by
    intro t
    have ht := hh (t+P)
    rw [show t+P+P=t+2*P by omega,hh t] at ht
    rw [ht];cases h t <;> rfl
  exact derived_readout_parity (orTrace g h) P (by intro t;unfold orTrace;rw [hg t,hh2 t])

end Rule30ClockModeResearch
