module
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Realization

/-! Infinitely many spatial reset factors do not alone force temporal rank.
The alternating ether is infinite, so this does NOT refute a seed-specific
or genuinely left-finite ancestry claim. -/
@[expose] public section
namespace ResetCountermodel
open Ruliology.CellularAutomata Rule30Jen Rule30Realization

def transfer (b : Bool) (s : Bool × Bool) : Bool × Bool :=
  (xor b (s.1 || s.2),s.1)

def reset0101 (s : Bool × Bool) : Bool × Bool :=
  transfer true (transfer false (transfer true (transfer false s)))

theorem reset0101_constant (s : Bool × Bool) : reset0101 s=(false,true) := by
  rcases s with ⟨p,q⟩
  cases p <;> cases q <;> rfl

def ether (p : Int) : Bool := decide (p%2=0)

theorem ether_fixed (p : Int) : rule (ether (p-1)) (ether p) (ether (p+1))=ether p := by
  have hp : p%2=0 ∨ p%2=1 := by omega
  rcases hp with hp|hp
  · have hl : (p-1)%2=1 := by omega
    have hr : (p+1)%2=1 := by omega
    simp [ether,rule,hp,hl,hr]
  · have hl : (p-1)%2=0 := by omega
    have hr : (p+1)%2=0 := by omega
    simp [ether,rule,hp,hl,hr]

theorem evol_ether (t : Nat) (p : Int) : evol ether t p=ether p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
    change rule (evol ether t (p-1)) (evol ether t p) (evol ether t (p+1))=ether p
    rw [ih,ih,ih]
    exact ether_fixed p

theorem repeated_reset_word (k : Int) :
    ether (2*k+1)=false ∧ ether (2*k+2)=true ∧
    ether (2*k+3)=false ∧ ether (2*k+4)=true := by
  have h1 : (2*k+1)%2=1 := by omega
  have h2 : (2*k+2)%2=0 := by omega
  have h3 : (2*k+3)%2=1 := by omega
  have h4 : (2*k+4)%2=0 := by omega
  simp [ether,h1,h2,h3,h4]

/-- Exact reset factors occur on actual next rows at every time, but the
center trace is constant. The missing finite-seed hypothesis is essential. -/
theorem resets_every_time_constant_center :
    (∀ t : Nat, ∀ k : Int,
      evol ether (t+1) (2*k+1)=false ∧ evol ether (t+1) (2*k+2)=true ∧
      evol ether (t+1) (2*k+3)=false ∧ evol ether (t+1) (2*k+4)=true) ∧
    (∀ t : Nat, evol ether t 0=true) := by
  constructor
  · intro t k
    simpa only [evol_ether] using repeated_reset_word k
  · intro t
    rw [evol_ether]
    rfl

theorem ether_is_not_left_finite :
    ¬ ∃ B : Int, ∀ p, p<B → ether p=false := by
  intro ⟨B,h⟩
  let p : Int := 2*(min B 0)-2
  have hp : p<B := by dsimp [p];omega
  have he : ether p=true := by
    have hz : p%2=0 := by dsimp [p];omega
    simp [ether,hz]
  have hh := h p hp
  rw [he] at hh
  cases hh

theorem evol_cone {x y : Int → Bool} (t : Nat) (p : Int)
    (h : ∀ q, p-(t:Int)≤q → q≤p+(t:Int) → x q=y q) :
    evol x t p=evol y t p := by
  induction t generalizing p with
  | zero => exact h p (by omega) (by omega)
  | succ t ih =>
    change rule (evol x t (p-1)) (evol x t p) (evol x t (p+1))=
      rule (evol y t (p-1)) (evol y t p) (evol y t (p+1))
    rw [ih (p-1) (by intro q hq hq';apply h q <;> omega),
      ih p (by intro q hq hq';apply h q <;> omega),
      ih (p+1) (by intro q hq hq';apply h q <;> omega)]

def truncated (R : Nat) (p : Int) : Bool :=
  if -(R:Int)≤p ∧ p≤(R:Int) then ether p else false

theorem evol_truncated (R t : Nat) (p : Int)
    (hl : -(R:Int)≤p-(t:Int)) (hr : p+(t:Int)≤(R:Int)) :
    evol (truncated R) t p=ether p := by
  calc
    _ = evol ether t p := by
      apply evol_cone
      intro q hq hq'
      unfold truncated
      rw [ite_eq_left (show -(R:Int)≤q ∧ q≤(R:Int) by constructor <;> omega)]
    _ = _ := evol_ether t p

/-- Even finite-support legal starts can exhibit arbitrarily many disjoint
reset words through any prescribed finite horizon while the center prefix
has rank one. This says nothing about their infinite-time center traces or
the fixed singleton seed. -/
theorem finite_prefix_reset_counterfamily (T K : Nat) :
    ∃ x : Int → Bool,
      (∃ R : Nat, ∀ p, p < -(R:Int) ∨ (R:Int)<p → x p=false) ∧
      (∀ t : Nat, t≤T → evol x t 0=true) ∧
      (∀ t : Nat, t≤T → ∀ k : Nat, k<K →
        evol x (t+1) (4*(k:Int)+1)=false ∧ evol x (t+1) (4*(k:Int)+2)=true ∧
        evol x (t+1) (4*(k:Int)+3)=false ∧ evol x (t+1) (4*(k:Int)+4)=true) := by
  let R := T+4*K+6
  refine ⟨truncated R,?_,?_,?_⟩
  · refine ⟨R,?_⟩
    intro p hp
    unfold truncated
    rw [ite_eq_right (by omega)]
  · intro t ht
    rw [evol_truncated R t 0 (by dsimp [R];omega) (by dsimp [R];omega)]
    rfl
  · intro t ht k hk
    have obs (p : Int) (hp : 1≤p) (hp' : p≤4*(K:Int)+4) :
        evol (truncated R) (t+1) p=ether p :=
      evol_truncated R (t+1) p (by dsimp [R];omega) (by dsimp [R];omega)
    rw [obs (4*(k:Int)+1) (by omega) (by omega),
      obs (4*(k:Int)+2) (by omega) (by omega),
      obs (4*(k:Int)+3) (by omega) (by omega),
      obs (4*(k:Int)+4) (by omega) (by omega)]
    have h1 : (4*(k:Int)+1)%2=1 := by omega
    have h2 : (4*(k:Int)+2)%2=0 := by omega
    have h3 : (4*(k:Int)+3)%2=1 := by omega
    have h4 : (4*(k:Int)+4)%2=0 := by omega
    simp [ether,h1,h2,h3,h4]

end ResetCountermodel
