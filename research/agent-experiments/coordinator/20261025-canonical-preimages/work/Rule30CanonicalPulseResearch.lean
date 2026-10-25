module

public import Rule30PreimageResearch
public import Rule30Equivalents.TFunction

/-!
An all-finite-horizons obstruction, with actual canonical background ages.
This is not an all-time common mode or a zero-center canonical observer.
-/

@[expose] public section
namespace Rule30CanonicalPulseResearch
open Ruliology.CellularAutomata
open Rule30Jen (rule cell)
open Rule30Realization (evol)
open Rule30PreimageResearch

theorem evol_local (x y : Int → Bool) (t : Nat) (p : Int)
    (h : ∀ q, p-t ≤ q → q ≤ p+t → x q=y q) : evol x t p=evol y t p := by
  induction t generalizing p with
  | zero => exact h p (by omega) (by omega)
  | succ t ih =>
    change rule (evol x t (p-1)) (evol x t p) (evol x t (p+1)) =
      rule (evol y t (p-1)) (evol y t p) (evol y t (p+1))
    rw [ih (p-1) (fun q hq hq' => h q (by omega) (by omega)),
      ih p (fun q hq hq' => h q (by omega) (by omega)),
      ih (p+1) (fun q hq hq' => h q (by omega) (by omega))]

theorem evol_white (t : Nat) (p : Int) : evol (fun _ => false) t p=false := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih => simp [evol, ih, rule]

theorem pulse_evol (U : Int) (t : Nat) (p : Int) : evol (unit U) t p=cell t (p-U) := by
  induction t generalizing p with
  | zero =>
    change decide (p=U)=decide (p-U=0)
    have he : (p=U) ↔ (p-U=0) := by omega
    simp only [he]
  | succ t ih =>
    change rule (evol (unit U) t (p-1)) (evol (unit U) t p) (evol (unit U) t (p+1)) = _
    rw [ih, ih, ih]
    change rule (cell t (p-1-U)) (cell t (p-U)) (cell t (p+1-U)) =
      rule (cell t (p-U-1)) (cell t (p-U)) (cell t (p-U+1))
    congr 2 <;> omega

theorem pulse_support (U : Int) (t : Nat) (p : Int) (hp : evol (unit U) t p=true) :
    U-t ≤ p ∧ p ≤ U+t := by
  rw [pulse_evol] at hp
  constructor
  · by_contra hn
    have hw := Rule30Jen.cell_eq_false_of_lt t (p-U) (by omega)
    rw [hw] at hp; cases hp
  · by_contra hn
    have hw := Rule30Diagonals.cell_eq_false_of_gt t (p-U) (by omega)
    rw [hw] at hp; cases hp

theorem physical_local : ∀ ac ar bc br hl hc hr : Bool,
    ((hc=true ∨ hr=true) → ac=hc ∧ ar=hr ∧ bc=false ∧ br=false) →
    xor (xor hl ((!br) && hc)) ((!ac) && hr) = rule hl hc hr ∧
    ((xor ar br) && hc) = ((xor ac bc) && hr) := by decide +kernel

theorem local_mode (A B h : Int → Bool)
    (hlocal : ∀ p, (h p=true ∨ h (p+1)=true) →
      A p=h p ∧ A (p+1)=h (p+1) ∧ B p=false ∧ B (p+1)=false) :
    (∀ p, diffStep A B h p=step h p) ∧ Common A B h := by
  constructor <;> intro p
  · exact (physical_local (A p) (A (p+1)) (B p) (B (p+1))
      (h (p-1)) (h p) (h (p+1)) (hlocal p)).1
  · exact (physical_local (A p) (A (p+1)) (B p) (B (p+1))
      (h (p-1)) (h p) (h (p+1)) (hlocal p)).2

theorem canonical_gap (e : Nat) (p : Int)
    (hp : (2^e : Nat)-e ≤ p) :
    cell (2^e) p=unit (2^e : Nat) p := by
  let U : Nat := 2^e
  change (U : Int)-(e : Int) ≤ p at hp
  change cell U p=unit (U : Int) p
  by_cases hout : (U : Int) < p
  · rw [Rule30Diagonals.cell_eq_false_of_gt _ _ hout]
    symm
    simp only [unit, decide_eq_false_iff_not]; omega
  · let j : Nat := ((U : Int)-p).toNat
    have hj : j ≤ e := by dsimp [j]; omega
    have heq : (U : Int)-j=p := by dsimp [j]; omega
    have hmod := Rule30Equivalents.TFunction.orbit_two_pow_mod 1 e
    have hb := congrArg (fun n : Nat => n.testBit j) hmod
    simp only [Nat.testBit_mod_two_pow, (by omega : j < e+1), decide_true, Bool.true_and,
      Rule30Equivalents.TFunction.orbit_one_eq_a,
      Rule30Equivalents.IntegerRows.testBit_a] at hb
    change cell U ((U : Int)-j)=Nat.testBit 1 j at hb
    rw [heq] at hb
    rw [hb]
    by_cases hj0 : j=0
    · have hpU : p=(U : Int) := by omega
      simp [unit, hj0, hpU]
    · have hpU : p≠(U : Int) := by omega
      simp only [unit, hpU, decide_false]
      cases hj : j with
      | zero => exact False.elim (hj0 hj)
      | succ j => simp [Nat.testBit_succ]

theorem restart (U t : Nat) (p : Int) : evol (cell U) t p=cell (U+t) p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
    change rule (evol (cell U) t (p-1)) (evol (cell U) t p)
      (evol (cell U) t (p+1)) = _
    rw [ih, ih, ih]
    rfl

theorem gap_agreement (e H t : Nat) (he : 2*H+1 ≤ e) (ht : t ≤ H)
    (p : Int) (hp : ((2^e : Nat) : Int)-t-1 ≤ p) :
    cell (2^e+t) p=evol (unit (2^e : Nat)) t p := by
  rw [← restart]
  apply evol_local
  intro q hq _
  apply canonical_gap
  simp only [Nat.cast_pow, Nat.cast_ofNat] at *
  omega

theorem pulse_is_mode (e H t : Nat) (he : 2*H+1 ≤ e)
    (hU : 2*H+3 ≤ 2^e) (ht : t ≤ H) :
    (∀ p, diffStep (cell (2^e+t)) (cell (1+t)) (evol (unit (2^e : Nat)) t) p =
      evol (unit (2^e : Nat)) (t+1) p) ∧
    Common (cell (2^e+t)) (cell (1+t)) (evol (unit (2^e : Nat)) t) := by
  have hlocal : ∀ p, (evol (unit (2^e : Nat)) t p=true ∨
      evol (unit (2^e : Nat)) t (p+1)=true) →
      cell (2^e+t) p=evol (unit (2^e : Nat)) t p ∧
      cell (2^e+t) (p+1)=evol (unit (2^e : Nat)) t (p+1) ∧
      cell (1+t) p=false ∧ cell (1+t) (p+1)=false := by
    intro p hb
    have hp : ((2^e : Nat) : Int)-t-1 ≤ p := by
      rcases hb with hb | hb
      · have := pulse_support (2^e : Nat) t p hb; omega
      · have := pulse_support (2^e : Nat) t (p+1) hb; omega
    refine ⟨gap_agreement e H t he ht p hp,
      gap_agreement e H t he ht (p+1) (by omega), ?_, ?_⟩
    · apply Rule30Diagonals.cell_eq_false_of_gt
      omega
    · apply Rule30Diagonals.cell_eq_false_of_gt
      omega
  exact local_mode _ _ _ hlocal

/-- For every finite check horizon, actual canonical ages admit a nonzero
initial subset mode with zero center through that horizon but no restricted
finite predecessor. It does NOT carry the canonical left edge, and is not
an all-time common mode or a counterexample to the prize statement. -/
theorem arbitrarily_long_nonliftable_canonical_modes (H : Nat) :
    ∃ U : Nat, 2 ≤ U ∧ ∃ h : Nat → Int → Bool,
      h 0=unit U ∧ Subset (cell U) (cell 1) (h 0) ∧
      (∀ t, t ≤ H → Common (cell (U+t)) (cell (1+t)) (h t)) ∧
      (∀ t, t ≤ H → ∀ p, h (t+1) p=diffStep (cell (U+t)) (cell (1+t)) (h t) p) ∧
      (∀ t, t ≤ H → h t 0=false) ∧
      (¬ ∃ g : Int → Bool, (∃ lo : Int, ∀ p, p < lo → g p=false) ∧
        Subset (cell (U-1)) (cell 0) g ∧ Common (cell (U-1)) (cell 0) g ∧
        ∀ p, diffStep (cell (U-1)) (cell 0) g p=h 0 p) := by
  let e := 2*H+4
  let U := 2^e
  have hbig : 2*H+4 < U := by simpa [e, U] using (Nat.lt_two_pow_self (n:=e))
  have he : 2*H+1 ≤ e := by dsimp [e]; omega
  have hU : 2*H+3 ≤ 2^e := by change 2*H+3 ≤ U; omega
  refine ⟨U, by omega, evol (unit U), rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    by_cases hp : p=U
    · subst p
      have ha := canonical_gap e (U : Int) (by dsimp [U]; omega)
      have hb := Rule30Diagonals.cell_eq_false_of_gt 1 (U : Int) (by omega)
      have ha1 : cell U (U : Int)=true := by
        exact (show cell U (U : Int)=unit (U : Int) (U : Int) from ha).trans (by simp [unit])
      change (unit (U : Int) (U : Int) && xor (cell U (U : Int)) (cell 1 (U : Int))) =
        unit (U : Int) (U : Int)
      rw [ha1, hb]
      simp [unit]
    · simp [evol, unit, hp]
  · intro t ht
    exact (pulse_is_mode e H t he hU ht).2
  · intro t ht p
    exact ((pulse_is_mode e H t he hU ht).1 p).symm
  · intro t ht
    cases hb : evol (unit (U : Int)) t 0 with
    | false => rfl
    | true => have := pulse_support (U : Int) t 0 hb; omega
  · rintro ⟨g,⟨lo,hl⟩,hs,hw,hstep⟩
    have hseed : cell 0=unit 0 := rfl
    rw [hseed] at hs hw hstep
    exact no_restricted_lift (U : Int) (by omega) (cell (U-1)) g lo hl hs hw hstep

end Rule30CanonicalPulseResearch
