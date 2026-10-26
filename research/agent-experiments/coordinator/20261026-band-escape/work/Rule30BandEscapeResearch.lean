module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
Every nonzero right-edge-frame divided-difference field over an older
canonical background visits arbitrarily large depths after every time.
The second coefficient background is arbitrary; neither W nor initial
subset is assumed. This rules out eventual confinement to any fixed band.
It does not force a black value at the moving center depth U+t and does
not prove any Rule30 prize statement.
-/

@[expose] public section
namespace Rule30BandEscapeResearch
open Ruliology.CellularAutomata
open Rule30Diagonals (R R_periodic)

def step (a b h : Nat → Bool) : Nat → Bool
  | 0 => h 0
  | 1 => xor (h 1) (h 0)
  | j+2 => xor (xor (h (j+2)) ((!b j) && h (j+1))) ((!a (j+1)) && h j)

def Evolution (a b h : Nat → Nat → Bool) : Prop :=
  ∀ t j, h (t+1) j=step (a t) (b t) (h t) j

def canonical (U t j : Nat) : Bool := R j (U+t)

theorem R_periodic_mul (j q t : Nat) : R j (t+q*2^j)=R j t := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul,show t+(q*2^j+2^j)=(t+q*2^j)+2^j by omega,R_periodic,ih]

theorem R_dyadic_return (E j k : Nat) (hj : j ≤ E) : R j (2^E+k)=R j k := by
  have hp : 2^E=2^(E-j)*2^j := by
    rw [← Nat.pow_add,Nat.sub_add_cancel hj]
  rw [show 2^E+k=k+2^(E-j)*2^j by omega,R_periodic_mul]

theorem R_white (k j : Nat) (hj : 2*k < j) : R j k=false := by
  apply Rule30Jen.cell_eq_false_of_lt
  omega

theorem step_zero (a b h : Nat → Bool) (hz : ∀ j, step a b h j=false) :
    ∀ j, h j=false := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    cases j with
    | zero => exact hz 0
    | succ j =>
      cases j with
      | zero => simpa [step,ih 0 (by omega)] using hz 1
      | succ j => simpa [step,ih j (by omega),ih (j+1) (by omega)] using hz (j+2)

theorem zero_of_later_zero (a b h : Nat → Nat → Bool) (hh : Evolution a b h) (t : Nat) :
    (∀ j, h t j=false) → ∀ j, h 0 j=false := by
  induction t with
  | zero => exact fun hz => hz
  | succ t ih =>
    intro hz
    apply ih
    apply step_zero (a t) (b t) (h t)
    intro j
    rw [← hh t j]
    exact hz j

/-- Peel two cells backward through a white part of the older background. -/
theorem peel (a b h : Nat → Nat → Bool) (hh : Evolution a b h) (k L : Nat)
    (ha : ∀ j, 2*k < j → j ≤ L → a k j=false)
    (hb : ∀ j, L ≤ j → h k j=false)
    (hn : ∀ j, 2*(k+1) ≤ j → h (k+1) j=false) :
    ∀ j, 2*k ≤ j → h k j=false := by
  have key : ∀ n : Nat, ∀ j, L-j=n → 2*k ≤ j → h k j=false := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro j hj hk
      by_cases hlarge : L ≤ j
      · exact hb j hlarge
      · have h1 := ih (L-(j+1)) (by omega) (j+1) rfl (by omega)
        have h2 := ih (L-(j+2)) (by omega) (j+2) rfl (by omega)
        have hm := hh k (j+2)
        rw [hn (j+2) (by omega)] at hm
        simpa [step,h1,h2,ha (j+1) (by omega) (by omega)] using hm.symm
  intro j hj
  exact key (L-j) j rfl hj

/-- At a dyadic return, a finite window of band confinement forces h=0. -/
theorem window_forces_zero (U E L K tau : Nat) (he : L ≤ E) (ht : U+tau=2^E)
    (hk : L ≤ 2*K)
    (b h : Nat → Nat → Bool) (hh : Evolution (canonical U) b h)
    (hb : ∀ k, k ≤ K → ∀ j, L ≤ j → h (tau+k) j=false) :
    ∀ j, h 0 j=false := by
  let A : Nat → Nat → Bool := fun k j => R j (2^E+k)
  let B : Nat → Nat → Bool := fun k j => b (tau+k) j
  let H : Nat → Nat → Bool := fun k j => h (tau+k) j
  have hH : Evolution A B H := by
    intro k j
    have hm := hh (tau+k) j
    have ht' : U+(tau+k)=2^E+k := by omega
    change h ((tau+k)+1) j=step (fun j => R j (U+(tau+k))) (b (tau+k)) (h (tau+k)) j at hm
    rw [ht'] at hm
    simpa only [H,A,B,Nat.add_assoc] using hm
  have white : ∀ k j, 2*k < j → j ≤ L → A k j=false := by
    intro k j hj hjL
    change R j (2^E+k)=false
    rw [R_dyadic_return E j k (by omega)]
    exact R_white k j hj
  have back : ∀ n : Nat, n ≤ K → ∀ j, 2*(K-n) ≤ j → H (K-n) j=false := by
    intro n
    induction n with
    | zero =>
      intro _ j hj
      exact hb K (by omega) j (by omega)
    | succ n ih =>
      intro hn
      apply peel A B H hH (K-(n+1)) L
      · exact white (K-(n+1))
      · intro j hj
        exact hb (K-(n+1)) (by omega) j hj
      · intro j hj
        have heq : K-n=(K-(n+1))+1 := by omega
        simpa only [heq] using ih (by omega) j (by omega)
  have hz : ∀ j, h tau j=false := by
    intro j
    simpa [H] using back K (by omega) j (by omega)
  exact zero_of_later_zero (canonical U) b h hh tau hz

theorem small_pow (n : Nat) : n < 2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- No W, no second-background recurrence and no initial subset premise. -/
theorem no_eventually_bounded_band (U : Nat) (b h : Nat → Nat → Bool)
    (hh : Evolution (canonical U) b h) (hne : ∃ j, h 0 j=true) :
    ¬ ∃ T L : Nat, ∀ t, T ≤ t → ∀ j, L ≤ j → h t j=false := by
  rintro ⟨T,L,hb⟩
  let E := U+T+L+1
  let tau := 2^E-U
  have hp := small_pow E
  have hreset : U+tau=2^E := by dsimp [E,tau] at *; omega
  have htau : T ≤ tau := by dsimp [E,tau] at *; omega
  have hz := window_forces_zero U E L L tau (by dsimp [E]; omega) hreset (by omega) b h hh
    (fun k _ j hj => hb (tau+k) (by omega) j hj)
  obtain ⟨j,hj⟩ := hne
  rw [hz j] at hj
  cases hj

/-- An explicit finite escape window after any chosen dyadic return. -/
theorem escapes_near_reset (U E L tau : Nat) (he : L ≤ E) (ht : U+tau=2^E)
    (b h : Nat → Nat → Bool) (hh : Evolution (canonical U) b h)
    (hne : ∃ j, h 0 j=true) :
    ∃ k, k ≤ (L+1)/2 ∧ ∃ j, L ≤ j ∧ h (tau+k) j=true := by
  apply Classical.byContradiction
  intro hn
  have hb : ∀ k, k ≤ (L+1)/2 → ∀ j, L ≤ j → h (tau+k) j=false := by
    intro k hk j hj
    cases hc : h (tau+k) j with
    | false => rfl
    | true => exact False.elim (hn ⟨k,hk,j,hj,hc⟩)
  have hz := window_forces_zero U E L ((L+1)/2) tau he ht (by omega) b h hh hb
  obtain ⟨j,hj⟩ := hne
  rw [hz j] at hj
  cases hj

theorem arbitrarily_deep_after_any_time (U : Nat) (b h : Nat → Nat → Bool)
    (hh : Evolution (canonical U) b h) (hne : ∃ j, h 0 j=true) (T L : Nat) :
    ∃ t, T ≤ t ∧ ∃ j, L ≤ j ∧ h t j=true := by
  apply Classical.byContradiction
  intro hn
  apply no_eventually_bounded_band U b h hh hne
  refine ⟨T,L,?_⟩
  intro t ht j hj
  cases hc : h t j with
  | false => rfl
  | true => exact False.elim (hn ⟨t,ht,j,hj,hc⟩)

end Rule30BandEscapeResearch
