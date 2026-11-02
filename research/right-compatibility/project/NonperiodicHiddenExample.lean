module
public import BlockHiddenPair
@[expose] public section
namespace NonperiodicHiddenExample
open Ruliology.CellularAutomata Rule30DrivenLeft Rule30DrivenMaskTransport
open PeriodicHiddenPair (driver)

def powers (t : Nat) : Bool := (List.range (t+1)).any (fun k => 2^k == t)

theorem power_true (k : Nat) : powers (2^k)=true := by
  apply List.any_eq_true.mpr
  refine ⟨k,List.mem_range.mpr ?_,?_⟩
  · have h : k<2^k := Nat.lt_two_pow_self
    omega
  · simp

theorem between_false (k t : Nat) (hlo : 2^k<t) (hhi : t<2^(k+1)) : powers t=false := by
  cases he : powers t with
  | false => rfl
  | true =>
    obtain ⟨j,hj,hpow⟩:=List.any_eq_true.mp he
    have hp : 2^j=t := by simpa using hpow
    have cases : j≤k ∨ k+1≤j := by omega
    rcases cases with h|h
    · have hn:=Nat.pow_le_pow_right (by decide : 0<2) h
      omega
    · have hn:=Nat.pow_le_pow_right (by decide : 0<2) h
      omega

theorem powers_not_periodic : ¬Rule30Jen.EventuallyPeriodic powers := by
  rintro ⟨T,P,hP,hper⟩
  have hg : T+P<2^(T+P) := Nat.lt_two_pow_self
  have key:=hper (2^(T+P)) (by omega)
  have hf:=between_false (T+P) (2^(T+P)+P) (by omega) (by
    rw [Nat.pow_succ]
    omega)
  rw [hf,power_true] at key
  cases key

/-- An explicit aperiodic common upstream history, still NOT a finite-origin claim. -/
theorem example_common_columns_not_periodic (b : Bool) (n : Nat) :
    ¬Rule30Jen.EventuallyPeriodic (fun t =>
      L (effective driver) (BlockHiddenPair.start powers b) t (-((n+7 : Nat) : Int))) :=
  BlockHiddenPair.deeper_not_periodic powers powers_not_periodic b n

theorem example_pinned (b : Bool) : EffectiveConsistent driver (BlockHiddenPair.start powers b) :=
  BlockHiddenPair.pinned_forever powers b

theorem example_distinct (t : Nat) : ∃ k : Nat,0<k ∧ k<6 ∧
    L (effective driver) (BlockHiddenPair.start powers false) t (-(k : Int)) ≠
    L (effective driver) (BlockHiddenPair.start powers true) t (-(k : Int)) :=
  BlockHiddenPair.distinct_forever powers t

#print axioms powers_not_periodic
#print axioms example_common_columns_not_periodic
#print axioms example_pinned
#print axioms example_distinct
end NonperiodicHiddenExample
