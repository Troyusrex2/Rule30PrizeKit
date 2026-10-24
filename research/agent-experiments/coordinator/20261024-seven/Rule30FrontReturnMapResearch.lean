import Rule30FrontLiftResearch

/-! A reusable sparse certificate rule. A finite return map on upper windows
replaces a long higher-width orbit check. The only extra witness checks are
the lower cycle's exceptional residues in the return map's finite orbit.
Existence of such a successful return map is an explicit hypothesis. -/

namespace Rule30FrontReturnMapResearch
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront
open Rule30FrontLiftResearch

def iter (J : Nat → Nat) : Nat → Nat → Nat
  | 0, u => u
  | n+1, u => J (iter J n u)

theorem iter_lt {J : Nat → Nat} {N u : Nat}
    (hJ : ∀ v, v < N → J v < N) (hu : u < N) (j : Nat) :
    iter J j u < N := by
  induction j with
  | zero => exact hu
  | succ j ih => exact hJ _ ih

theorem block_orbit {K L p N u : Nat} {J embed : Nat → Nat}
    (hJ : ∀ v, v < N → J v < N) (hu : u < N)
    (hstep : ∀ v, v < N → orb K L (embed v,p) = (embed (J v),p))
    (j : Nat) :
    orb K (L*j) (embed u,p) = (embed (iter J j u),p) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Nat.mul_succ, orb_add, ih]
    exact hstep _ (iter_lt hJ hu j)

theorem period_return {K L p N u q : Nat} {J embed : Nat → Nat}
    (hJ : ∀ v, v < N → J v < N) (hu : u < N)
    (hstep : ∀ v, v < N → orb K L (embed v,p) = (embed (J v),p))
    (hcycle : iter J q u = u) :
    orb K (L*q) (embed u,p) = (embed u,p) := by
  rw [block_orbit hJ hu hstep q, hcycle]

theorem exceptional_residues {K S L p N u q : Nat}
    {J embed : Nat → Nat} {E : Nat → Prop}
    (hL : 0 < L) (hLe : L%2 = 0)
    (hJ : ∀ v, v < N → J v < N) (hu : u < N)
    (hstep : ∀ v, v < N → orb K L (embed v,p) = (embed (J v),p))
    (hchecks : ∀ j, j < q → ∀ e, e < L → e%2 = 1-p → E e →
      sig (S+1) (L*j+e) (orb K e (embed (iter J j u),p)).1 = true)
    (r : Nat) (hr : r < L*q) (hp : r%2 = 1-p) (he : E (r%L)) :
    sig (S+1) r (orb K r (embed u,p)).1 = true := by
  let j := r/L
  let e := r%L
  have hj : j < q := by dsimp [j]; exact (Nat.div_lt_iff_lt_mul hL).mpr (by simpa [Nat.mul_comm] using hr)
  have hel : e < L := Nat.mod_lt r hL
  have hm : e%2 = r%2 := Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hLe)
  have hd : r = L*j+e := (Nat.div_add_mod r L).symm
  have hs := hchecks j hj e hel (hm.trans hp) he
  rw [hd, orb_add, block_orbit hJ hu hstep j]
  exact hs

/-- The lower cycle may have exceptional residues. Check them only on the
finite upper return-map orbit. This theorem assumes, rather than asserts,
the needed finite return-map cycle and the exceptional white witnesses. -/
theorem return_map_cycle_lift
    {Klo Khi Slo Shi B p L N u q : Nat}
    {J embed : Nat → Nat} {E : Nat → Prop}
    (hK : Slo+1 ≤ Klo) (hwidth : Klo ≤ Khi) (hS : Slo ≤ Shi)
    (hp : p < 2) (hinit : LowEq Klo (embed u) B)
    (hL : 0 < L) (hLe : L%2 = 0) (hLo : orb Klo L (B,p) = (B,p))
    (hgood : ∀ r, r < L → r%2 = 1-p → ¬ E r →
      sig (Slo+1) r (orb Klo r (B,p)).1 = true)
    (hJ : ∀ v, v < N → J v < N) (hu : u < N)
    (hstep : ∀ v, v < N → orb Khi L (embed v,p) = (embed (J v),p))
    (hq : 0 < q) (hcycle : iter J q u = u)
    (hchecks : ∀ j, j < q → ∀ e, e < L → e%2 = 1-p → E e →
      sig (Shi+1) (L*j+e) (orb Khi e (embed (iter J j u),p)).1 = true) :
    Cycle Khi Shi (embed u) p (L*q) := by
  exact punctured_cycle_lift hK hwidth hS hp hinit hL hLe hLo
    (Nat.mul_pos hL hq) (by simp [Nat.mul_mod,hLe])
    (period_return hJ hu hstep hcycle) E hgood
    (exceptional_residues hL hLe hJ hu hstep hchecks)

end Rule30FrontReturnMapResearch
