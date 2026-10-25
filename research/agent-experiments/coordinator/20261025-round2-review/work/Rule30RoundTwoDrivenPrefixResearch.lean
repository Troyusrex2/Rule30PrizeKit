import Ruliology.CellularAutomata.Rule30Ether
import Ruliology.CellularAutomata.Rule30PeriodTwoCoupled

/-! A finite light-cone trace certificate for the exact official driven
right half. The checker is Boolean, but its soundness is proved here and
its concrete use is evaluated by the Lean kernel. -/
namespace Rule30RoundTwoDrivenPrefixResearch
open Ruliology.CellularAutomata
open Rule30Ether Rule30PeriodTwoCoupled

def entry (rows : List (List Bool)) (t p : Nat) : Bool :=
  (rows.getD t []).getD p false

def checkTrace (c R : Nat → Bool) (rows : List (List Bool)) (N T : Nat) : Bool :=
  ((List.range N).all fun p => entry rows 0 p == (if p=0 then c 0 else R p)) &&
  ((List.range T).all fun t => (List.range (N-(t+1))).all fun p =>
    entry rows (t+1) p == (if p=0 then c (t+1) else
      Rule30Jen.rule (entry rows t (p-1)) (entry rows t p) (entry rows t (p+1))))

theorem trace_sound (c R : Nat → Bool) (rows : List (List Bool)) (N T : Nat)
    (hc : checkTrace c R rows N T = true) :
    ∀ t, t≤T → ∀ p, p<N-t → drv c R t p = entry rows t p := by
  have parts := Bool.and_eq_true_iff.mp hc
  have init : ∀ p, p<N → entry rows 0 p = (if p=0 then c 0 else R p) := by
    intro p hp
    exact beq_iff_eq.mp (List.all_eq_true.mp parts.1 p (List.mem_range.mpr hp))
  have step : ∀ t, t<T → ∀ p, p<N-(t+1) →
      entry rows (t+1) p = (if p=0 then c (t+1) else
        Rule30Jen.rule (entry rows t (p-1)) (entry rows t p) (entry rows t (p+1))) := by
    intro t ht p hp
    exact beq_iff_eq.mp (List.all_eq_true.mp
      (List.all_eq_true.mp parts.2 t (List.mem_range.mpr ht)) p (List.mem_range.mpr hp))
  intro t
  induction t with
  | zero =>
    intro _ p hp
    rw [init p (by omega)]
    rfl
  | succ t ih =>
    intro ht p hp
    rw [step t (by omega) p hp]
    cases p with
    | zero => exact drv_col0 c R (t+1)
    | succ p =>
      simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte]
      rw [drv,ih (by omega) p (by omega),ih (by omega) (p+1) (by omega),
        ih (by omega) (p+2) (by omega)]
      rfl

end Rule30RoundTwoDrivenPrefixResearch
