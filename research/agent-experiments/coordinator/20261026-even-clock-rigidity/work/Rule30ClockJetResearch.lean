module
public import Rule30OrClockObserverResearch

/-! Exact time-shift identities for the plateau case of the OR observer.
The hidden mode is a xor accumulator of the complemented older profile;
it is not asserted to be an Actual row. These identities do not invert it. -/
@[expose] public section
namespace Rule30ClockJetResearch
open Rule30CommonPastResearch
open Rule30OrClockObserverResearch (shift_flag)
set_option maxHeartbeats 4000000

def delta (f : Nat → Bool) (P t : Nat) : Bool := xor (f (t+P)) (f t)
def orTrace (g h : Nat → Bool) (t : Nat) : Bool := g t || h t
theorem gate_delta (x y h k : Bool) :
    xor (xor x ((xor h true) || k)) (xor y (h || k))=xor (xor x y) (!k) := by
  cases x <;> cases y <;> cases h <;> cases k <;> rfl
theorem mask_delta (x y h : Bool) :
    xor (x || (xor h true)) (y || h)=xor (!y) (h && xor x y) := by
  cases x <;> cases y <;> cases h <;> rfl
theorem masked_step (g h k l q : Bool) :
    xor (xor (!(xor g (h || k))) ((xor h (k || l)) && xor q (!k)))
        (xor (!g) (h && q))=(!q && xor (xor h (k || l)) h) := by
  cases g <;> cases h <;> cases k <;> cases l <;> cases q <;> rfl
theorem delta_telescope (x y z e : Bool) (h : xor z y=xor (xor y x) e) : z=xor x e := by
  cases x <;> cases y <;> cases z <;> cases e <;> simp_all

theorem shift_difference_step (g h k : Nat → Bool) (P : Nat)
    (hs : ∀ t, g (t+1)=xor (g t) (h t || k t))
    (hh : ∀ t, h (t+P)=xor (h t) true) (hk : ∀ t, k (t+P)=k t) :
    ∀ t, delta g P (t+1)=xor (delta g P t) (!k t) := by
  intro t
  unfold delta
  rw [show t+1+P=(t+P)+1 by omega,hs (t+P),hs t,hh t,hk t]
  exact gate_delta _ _ _ _
theorem shift_or_mask (g h : Nat → Bool) (P : Nat)
    (hh : ∀ t, h (t+P)=xor (h t) true) :
    ∀ t, delta (orTrace g h) P t=xor (!g t) (h t && delta g P t) := by
  intro t
  unfold delta orTrace
  rw [hh t]
  exact mask_delta _ _ _
theorem shift_or_difference (g h k l : Nat → Bool) (P : Nat)
    (gs : ∀ t, g (t+1)=xor (g t) (h t || k t))
    (hs : ∀ t, h (t+1)=xor (h t) (k t || l t))
    (hh : ∀ t, h (t+P)=xor (h t) true) (hk : ∀ t, k (t+P)=k t) :
    ∀ t, xor (delta (orTrace g h) P (t+1)) (delta (orTrace g h) P t)=
      (!delta g P t && xor (h (t+1)) (h t)) := by
  intro t
  rw [shift_or_mask g h P hh (t+1),shift_or_mask g h P hh t,
    shift_difference_step g h k P gs hh hk t,gs t,hs t]
  exact masked_step _ _ _ _ _

/-- The mode's flip flag over P is the newer profile's flag over 2P. -/
theorem plateau_or_double (g h k : Nat → Bool) (P : Nat)
    (gs : ∀ t, g (t+1)=xor (g t) (h t || k t))
    (hh : ∀ t, h (t+P)=xor (h t) true) (hk : ∀ t, k (t+P)=k t) :
    ∃ e : Bool, (∀ t, delta g P (t+P)=xor (delta g P t) e) ∧
      (∀ t, g (t+2*P)=xor (g t) e) := by
  have qs := shift_difference_step g h k P gs hh hk
  have kp : ∀ t, (!k (t+P))=(!k t) := by intro t;rw [hk t]
  have flag := shift_flag (delta g P) (fun t => !k t) P qs kp
  refine ⟨xor (delta g P P) (delta g P 0),flag,?_⟩
  intro t
  have hf := flag t
  unfold delta at hf
  rw [show t+P+P=t+2*P by omega] at hf
  exact delta_telescope _ _ _ _ hf

theorem actual_plateau_jet (a : Nat → Nat → Bool) (ha : Actual a) (j P : Nat)
    (hh : ∀ t, a (t+P) (j+2)=xor (a t (j+2)) true)
    (hk : ∀ t, a (t+P) (j+1)=a t (j+1)) :
    (∀ t, delta (fun s => a s (j+3)) P (t+1)=
      xor (delta (fun s => a s (j+3)) P t) (!a t (j+1))) ∧
    (∀ t, xor (delta (orTrace (fun s => a s (j+3)) (fun s => a s (j+2))) P (t+1))
        (delta (orTrace (fun s => a s (j+3)) (fun s => a s (j+2))) P t)=
      (!delta (fun s => a s (j+3)) P t && xor (a (t+1) (j+2)) (a t (j+2)))) := by
  have gs : ∀ t, a (t+1) (j+3)=xor (a t (j+3)) (a t (j+2) || a t (j+1)) := fun t => ha t (j+3)
  have hs : ∀ t, a (t+1) (j+2)=xor (a t (j+2)) (a t (j+1) || a t j) := fun t => ha t (j+2)
  exact ⟨shift_difference_step _ _ _ P gs hh hk,shift_or_difference _ _ _ _ P gs hs hh hk⟩

end Rule30ClockJetResearch
