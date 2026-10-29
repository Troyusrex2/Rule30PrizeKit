module
public import Ruliology.CellularAutomata.Rule30RightPeriods
public import Ruliology.CellularAutomata.Rule30RightProfiles

/-! Single-cell specialization of the contributed 101 shift law.
This is not a generic finite-initial-code period-nonloss theorem. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30RightProfileSeed
open Rule30Diagonals Rule30RightPeriods
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

/-- Once the base exponent is at least2, the single-cell doubling block1101
must continue with0. The intervening0 already follows from no_three. -/
theorem no_11011_period {j E : Nat} (hj : 1≤j) (hE : 2≤E)
    (h0 : Per j (2^E)) (h1 : ¬ Per (j+1) (2^E))
    (h2 : ¬ Per (j+2) (2^(E+1))) (h4 : ¬ Per (j+4) (2^(E+2))) :
    Per (j+5) (2^(E+3)) := by
  let q := 2^(E+1)
  have double : 2*q=2^(E+2) := by
    dsimp [q]
    rw [show E+2=(E+1)+1 by omega,Nat.pow_succ]
    omega
  have four : 4*q=2^(E+3) := by
    have power : 2^(E+3)=2^(E+1)*4 := by
      calc
        2^(E+3)=2^((E+1)+2) := rfl
        _ = 2^(E+1)*2^2 := Nat.pow_add 2 (E+1) 2
        _ = 2^(E+1)*4 := rfl
    change 4*2^(E+1)=2^(E+3)
    rw [power]
    exact Nat.mul_comm _ _
  have half : q/2=2^E := by simp [q,Nat.pow_succ]
  have q8 : q%8=0 := by
    obtain ⟨k,hk⟩ : ∃ k, E=k+2 := ⟨E-2,by omega⟩
    dsimp [q]
    rw [hk,show k+2+1=k+3 by omega,Nat.pow_add]
    simp
  have dp : Per (j+1) q := per_step h0
  have bp : Per (j+3) (2*q) := by
    rw [double]
    exact no_three hj h0 h1 h2
  have da : ∀ t, R (j+1) (t+q/2)=!R (j+1) t := by
    intro t
    rw [half]
    exact antiperiod h0 h1 t
  have aa : ∀ t, R (j+2) (t+q)=!R (j+2) t := antiperiod dp h2
  have ca : ∀ t, R (j+4) (t+2*q)=!R (j+4) t := by
    intro t
    rw [double]
    exact antiperiod (no_three hj h0 h1 h2) h4 t
  have eta := Rule30RightProfiles.eta_false_of_antiperiod q q8 (R (j+1)) da
  have shift := Rule30RightProfiles.shift_law q (by omega)
    (R (j+1)) (R (j+2)) (R (j+3)) (R (j+4)) (R (j+5))
    dp aa bp ca (fun t => R_step (j+1) t) (fun t => R_step (j+3) t)
  intro t
  have h := shift t
  rw [eta,Bool.xor_false,four] at h
  exact h

/-- A statement directly about least period exponents of the actual single
cell. The `11011` pattern is excluded beyond the small-clock exception. -/
theorem exponent_1101_forces_stay {j E : Nat} (hj : 1≤j) (hE : 2≤E)
    (h0 : IsE j E) (h1 : IsE (j+1) (E+1)) (h2 : IsE (j+2) (E+2))
    (h4 : IsE (j+4) (E+3)) : IsE (j+5) (E+3) := by
  have hp := no_11011_period hj hE h0.1 (h1.2 E (by omega))
    (h2.2 (E+1) (by omega)) (h4.2 (E+2) (by omega))
  refine ⟨hp,?_⟩
  intro k hk hper
  have older : Per (j+4) (2^k) := per_mono_all (j:=j+4) hper (j+4) (by omega)
  exact h4.2 k hk older

theorem no_11011_exponents {j E : Nat} (hj : 1≤j) (hE : 2≤E)
    (h0 : IsE j E) (h1 : IsE (j+1) (E+1)) (h2 : IsE (j+2) (E+2))
    (h4 : IsE (j+4) (E+3)) : ¬ IsE (j+5) (E+4) := by
  intro last
  have eq := (exponent_1101_forces_stay hj hE h0 h1 h2 h4).unique last
  omega

end Ruliology.CellularAutomata.Rule30RightProfileSeed
