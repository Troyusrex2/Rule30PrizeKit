import Rule30RoundTwoChargeTwoThetaResearch

/-! The wiki agent's W1 is now handled by an exact finite entry certificate,
the official invariant trap, and an all-depth reconstruction table. This
refutes coefficient two for every additive allowance, not CQ01 or Problem1. -/
namespace Rule30RoundTwoChargeTwoResearch
open Ruliology.CellularAutomata
open Rule30RoundTwoChargeTwoEntryResearch (right stream free_stream)
open Rule30RoundTwoChargeTwoThetaResearch (left psi_left)
open Rule30CriticalChargeOneCoreResearch (free zeros blackCount CriticalCharge)

theorem left_period (d : Nat) (hd : 12≤d) : left (d+14)=left d := by
  have hs : Rule30RoundTwoChargeTwoThetaResearch.spaceAt (d+14)=
      Rule30RoundTwoChargeTwoThetaResearch.spaceAt d := by
    unfold Rule30RoundTwoChargeTwoThetaResearch.spaceAt
    split <;> split <;> omega
  unfold left Rule30RoundTwoChargeTwoThetaResearch.model
  rw [hs]

theorem black_fourteen (n : Nat) (hn : 12≤n) :
    blackCount left (n+14)=blackCount left n+5 := by
  have all : ∀ j, blackCount left (12+j+14)=blackCount left (12+j)+5 := by
    intro j
    induction j with
    | zero => decide +kernel
    | succ j ih =>
      change blackCount left ((12+j+14)+1)=blackCount left ((12+j)+1)+5
      have hc : blackCount left ((12+j)+1)=blackCount left (12+j)+(left (12+j)).toNat := rfl
      rw [blackCount,ih,hc,left_period (12+j) (by omega)]
      omega
  have hh := all (n-12)
  simpa only [show 12+(n-12)=n by omega] using hh

theorem black_chunks (k : Nat) : blackCount left (13+14*k)=7+5*k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    rw [show 13+14*(k+1)=(13+14*k)+14 by omega,black_fourteen _ (by omega),ih]
    omega

theorem zeros_two (n : Nat) (hn : 2≤n) : zeros stream (n+2)=zeros stream n+1 := by
  have hp : n%2=0 ∨ n%2=1 := Nat.mod_two_eq_zero_or_one n
  rcases hp with hp|hp
  all_goals
    simp [zeros,stream,show ¬n<2 by omega,show ¬n+1<2 by omega,Nat.add_mod,hp]

theorem zeros_even (k : Nat) : zeros stream (2*k+2)=k+1 := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    rw [show 2*(k+1)+2=(2*k+2)+2 by omega,zeros_two _ (by omega),ih]

theorem coupled_scale_counts (k : Nat) :
    zeros (free right) (14*k+6)=7*k+3 ∧
    blackCount (Rule30PeriodTwoSideways.Psi right) (2*(14*k+6)+1)=10*k+7 := by
  rw [show free right=stream from funext free_stream,psi_left]
  constructor
  · have h := zeros_even (7*k+2)
    simpa only [show 2*(7*k+2)+2=14*k+6 by omega,show 7*k+2+1=7*k+3 by omega] using h
  · have h := black_chunks (2*k)
    simpa only [show 13+14*(2*k)=2*(14*k+6)+1 by omega,show 7+5*(2*k)=10*k+7 by omega] using h

theorem coefficient_two_false (B : Nat) : ¬ CriticalCharge 2 B right := by
  intro hc
  have h := hc (14*(B+6)+6)
  have counts := coupled_scale_counts (B+6)
  rw [counts.1,counts.2] at h
  omega

theorem minimum_integer_coefficient {C B : Nat} (hc : CriticalCharge C B right) : 3≤C := by
  by_cases good : 3≤C
  · exact good
  have hC : C≤2 := by omega
  apply False.elim
  apply coefficient_two_false B
  intro n
  have h := hc n
  have hm := Nat.mul_le_mul_right (blackCount (Rule30PeriodTwoSideways.Psi right) (2*n+1)) hC
  change 5*zeros (free right) n≤n+B+2*blackCount (Rule30PeriodTwoSideways.Psi right) (2*n+1)
  omega

end Rule30RoundTwoChargeTwoResearch
