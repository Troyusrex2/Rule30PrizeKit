import Ruliology.CellularAutomata.Rule30PeriodTwoSideways
import Ruliology.CellularAutomata.Rule30Ether

/-! A finite mathematical right seed disproves the constant-one critical
charge even with arbitrary additive slack. This does not refute the target
with a larger coefficient and does not solve CQ01. All coordinates use the
official Psi, zero-boundary evolution, and counting definitions. -/

namespace Rule30CriticalChargeOneCoreResearch
open Ruliology.CellularAutomata
open Rule30Ether Rule30PeriodTwoCoupled Rule30PeriodTwoSideways
open Rule30ZeroBoundary

def free (R : Nat -> Bool) (k : Nat) : Bool := zrow (Psi R) (2*k+1) 1

def zeros (s : Nat -> Bool) : Nat -> Nat
  | 0 => 0
  | n+1 => zeros s n+(!s n).toNat

def blackCount (L : Nat -> Bool) : Nat -> Nat
  | 0 => 0
  | n+1 => blackCount L n+(L n).toNat

def CriticalCharge (C B : Nat) (R : Nat -> Bool) : Prop := forall n,
  5*zeros (free R) n <= n+B+C*blackCount (Psi R) (2*n+1)

def wall : List Bool :=
  [true, false, true, true, false, true, false, true, true, false, false, false, false]

def right : Nat → Bool := config 3 1 6 wall
def stream (s : Nat) : Bool := s % 2 == 1
def left (d : Nat) : Bool := if d = 0 then false else ether (3+6*d) 1

theorem right_finite : FinSupp right := by
  refine ⟨19, fun p hp => ?_⟩
  exact config_finite 3 1 6 wall p (by omega)

theorem wall_member : (1,wall) ∈ wallStates := by decide +kernel

theorem driver_ether (t : Nat) : altCol t = ether 3 (t+1) := by
  have h : t%4=0 ∨ t%4=1 ∨ t%4=2 ∨ t%4=3 := by omega
  rcases h with h|h|h|h
  all_goals
    have h2 : t%2 = (t%4)%2 := by omega
    have h4 : (t+1)%4 = (t%4+1)%4 := by omega
    simp [altCol,ether,etherTable,h2,h4,h]

theorem right_col1 (t : Nat) : drv altCol right t 1 = ether 4 (t+1) := by
  have h0 : ∀ n, 0≤n → drv altCol right n 0 = ether 3 (n+1) := by
    intro n _
    rw [drv_col0,driver_ether]
  have he : ∀ p, 1≤p → p≤6 → drv altCol right 0 p = ether (3+p) (0+1) := by
    intro p hp1 hp6
    rw [drv_init _ _ p hp1]
    simp [right,config,hp1,hp6]
  have hw : ((0+1)%4,rowOf (drv altCol right) 0 6 13) ∈ wallStates := by decide +kernel
  have inv := trap_invariant (drv_isR30 altCol right) 3 1 6 0 (by decide) h0 he hw t
  simpa using inv.1 1 (by decide)

theorem free_stream (s : Nat) : free right s = stream s := by
  rw [free,Psi_free]
  rw [right_col1]
  have h : s%2=0 ∨ s%2=1 := Nat.mod_two_eq_zero_or_one s
  rcases h with h|h
  all_goals
    have ht : (2*s+1+1)%4 = if s%2=0 then 2 else 0 := by split <;> omega
    simp [stream,ether,etherTable,ht,h]

theorem boundary_rule (t : Nat) :
    ether 9 (t+1) = xor (ether 15 t) (ether 9 t || false) := by
  rw [ether_rule]
  change xor (ether 15 t) (ether 9 t || ether 10 t) = _
  have h : t%4=0 ∨ t%4=1 ∨ t%4=2 ∨ t%4=3 := by omega
  rcases h with h|h|h|h <;> simp [ether,etherTable,h]

theorem left_evolution (t d : Nat) :
    zrow left t d = if d=0 then false else ether (3+6*d) (t+1) := by
  induction t generalizing d with
  | zero => simp [zrow,left]
  | succ t ih =>
    cases d with
    | zero => rw [zrow_wall]; rfl
    | succ k =>
      rw [zrow_succ,ih,ih,ih]
      by_cases hk : k=0
      · subst k
        simpa using (boundary_rule (t+1)).symm
      · simp only [Nat.succ_ne_zero,↓reduceIte,hk]
        have hl : 3+6*(k+2) = (3+6*(k+1))+6 := by omega
        have hr : ether (3+6*k) (t+1) = ether ((3+6*(k+1))+1) (t+1) :=
          ether_congr (by omega) rfl
        rw [hl,hr]
        exact (ether_rule (3+6*(k+1)) (t+1)).symm

theorem left_inX : InX left := by
  intro s
  rw [left_evolution]
  have h : (2*s+1)%4=1 ∨ (2*s+1)%4=3 := by omega
  rcases h with h|h <;> simp [ether,etherTable,h]

theorem left_free (s : Nat) : zrow left (2*s+1) 1 = stream s := by
  rw [left_evolution]
  have h : s%2=0 ∨ s%2=1 := Nat.mod_two_eq_zero_or_one s
  rcases h with h|h
  all_goals
    have ht : (2*s+1+1)%4 = if s%2=0 then 2 else 0 := by split <;> omega
    simp [stream,ether,etherTable,ht,h]

theorem theta_left : Theta stream = left := by
  have h := Theta_unique left_inX left_free
  funext d
  have hd := congrFun h d
  simpa [zrow,left] using hd.symm

theorem psi_left : Psi right = left := by
  have hf : (fun s => !u right s) = stream := by
    funext s
    simpa only [free,Psi_free,u] using free_stream s
  unfold Psi
  rw [hf,theta_left]

theorem black_seven (n : Nat) (hn : 1≤n) : blackCount left (n+7) = blackCount left n+3 := by
  have h : n%7=0 ∨ n%7=1 ∨ n%7=2 ∨ n%7=3 ∨ n%7=4 ∨ n%7=5 ∨ n%7=6 := by omega
  have h0 : n≠0 := by omega
  rcases h with h|h|h|h|h|h|h
  all_goals
    simp [blackCount,left,ether,etherTable,h0,Nat.add_mod,Nat.mul_mod,h]

theorem black_chunks (k : Nat) : blackCount left (7*k+1) = 3*k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    rw [show 7*(k+1)+1=(7*k+1)+7 by omega,black_seven _ (by omega),ih]
    omega

theorem zeros_two (n : Nat) : zeros stream (n+2) = zeros stream n+1 := by
  have h : n%2=0 ∨ n%2=1 := Nat.mod_two_eq_zero_or_one n
  rcases h with h|h <;> simp [zeros,stream,Nat.add_mod,h]

theorem zeros_even (k : Nat) : zeros stream (2*k) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2*(k+1)=2*k+2 by omega,zeros_two,ih]

theorem coupled_scale_counts (k : Nat) :
    zeros (free right) (14*k) = 7*k ∧
      blackCount (Psi right) (2*(14*k)+1) = 12*k := by
  rw [show free right=stream from funext free_stream,psi_left]
  constructor
  · have h := zeros_even (7*k)
    rwa [show 2*(7*k)=14*k by omega] at h
  · have h := black_chunks (4*k)
    rwa [show 7*(4*k)+1=2*(14*k)+1 by omega,show 3*(4*k)=12*k by omega] at h

theorem unit_critical_charge_false (B : Nat) : ¬ CriticalCharge 1 B right := by
  intro hc
  have hf : free right = stream := funext free_stream
  have hh := hc (14*(B+1))
  rw [hf,psi_left] at hh
  have hz := zeros_even (7*(B+1))
  have hb := black_chunks (4*(B+1))
  have he1 : 2*(7*(B+1))=14*(B+1) := by omega
  have he2 : 7*(4*(B+1))+1=2*(14*(B+1))+1 := by omega
  rw [he1] at hz
  rw [he2] at hb
  rw [hz,hb] at hh
  omega

theorem minimum_integer_coefficient {C B : Nat} (hc : CriticalCharge C B right) : 2≤C := by
  by_cases hC : 2≤C
  · exact hC
  have hC1 : C≤1 := by omega
  apply False.elim
  apply unit_critical_charge_false B
  intro n
  have h := hc n
  have hm := Nat.mul_le_mul_right (blackCount (Psi right) (2*n+1)) hC1
  change 5*zeros (free right) n ≤
    n+B+1*blackCount (Psi right) (2*n+1)
  omega

end Rule30CriticalChargeOneCoreResearch
