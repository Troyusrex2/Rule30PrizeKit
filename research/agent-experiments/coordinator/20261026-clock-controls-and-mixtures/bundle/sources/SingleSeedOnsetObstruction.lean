import Ruliology.CellularAutomata.Rule30Diagonals
import Ruliology.CellularAutomata.Rule30Window

/-! A genuine single-seed obstruction to entering the left-diagonal clock
by center-crossing time. This does not challenge eventual periodicity. -/
namespace SingleSeedOnsetObstruction
open Ruliology.CellularAutomata Rule30Jen Rule30Diagonals Rule30Window
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem diagonal_as_packed (K t i : Nat) (ht : t ≤ K) :
    D i t = (row K t).testBit (K-t+i) := by
  have h := row_testBit K t ht (K-t+i)
  simpa only [D,show ((K-t+i:Nat):Int)-(K:Int)=(i:Int)-(t:Int) by omega] using h.symm

/-- Finite prefix agreement propagates for every future time. This is the
closed left-diagonal recurrence, not a finite-cone-to-infinite-clock step. -/
theorem prefix_future (T U n : Nat)
    (h : ∀ i, i ≤ n → D i T=D i U) :
    ∀ s i, i ≤ n → D i (T+s)=D i (U+s) := by
  intro s
  induction s with
  | zero => intro i hi; simpa using h i hi
  | succ s ih =>
    intro i hi
    cases i with
    | zero => rw [D_zero,D_zero]
    | succ i =>
      cases i with
      | zero =>
        rw [show T+(s+1)=(T+s)+1 by omega,
          show U+(s+1)=(U+s)+1 by omega,D_one,D_one]
      | succ i =>
        rw [show T+(s+1)=(T+s)+1 by omega,
          show U+(s+1)=(U+s)+1 by omega,D_step,D_step,
          ih i (by omega),ih (i+1) (by omega),ih (i+2) (by omega)]

theorem cycle_certificate : ∀ i : Fin 33,
    (row 44 36).testBit (8+i.val)=(row 44 44).testBit i.val := by
  decide +kernel

theorem prefix_cycle : ∀ i, i ≤ 32 → D i 36=D i 44 := by
  intro i hi
  rw [diagonal_as_packed 44 36 i (by decide),
    diagonal_as_packed 44 44 i (by decide)]
  simpa using cycle_certificate ⟨i,by omega⟩

theorem diagonal32_periodic (t : Nat) (ht : 36 ≤ t) : D 32 (t+8)=D 32 t := by
  have h := prefix_future 36 44 32 prefix_cycle (t-36) 32 (by omega)
  rw [show 36+(t-36)=t by omega,show 44+(t-36)=t+8 by omega] at h
  exact h.symm

theorem diagonal32_period_multiple (k t : Nat) (ht : 36 ≤ t) :
    D 32 (t+8*k)=D 32 t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,show t+(8*k+8)=(t+8*k)+8 by omega,
      diagonal32_periodic _ (by omega),ih]

theorem phase_values : D 32 32=false ∧ D 32 40=true := by
  rw [diagonal_as_packed 44 32 32 (by decide),
    diagonal_as_packed 44 40 32 (by decide)]
  decide +kernel

/-- The index-32 diagonal has not entered even the supplied 2^32 clock
when it first reaches the physical center. -/
theorem center_crossing_onset_fails : D 32 (32+2^32)≠D 32 32 := by
  rw [show (32:Nat)+2^32=40+8*536870911 by decide,
    diagonal32_period_multiple 536870911 40 (by decide),phase_values.1,phase_values.2]
  decide

theorem no_center_crossing_uniform_onset :
    ¬ (∀ i t : Nat, 1 ≤ i → i ≤ t → D i (t+2^i)=D i t) := by
  intro h
  exact center_crossing_onset_fails (h 32 32 (by decide) (by decide))

end SingleSeedOnsetObstruction
