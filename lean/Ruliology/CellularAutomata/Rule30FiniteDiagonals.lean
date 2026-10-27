module

public import Ruliology.CellularAutomata.Rule30Diagonals
public import Ruliology.CellularAutomata.Rule30FiniteConfigs

/-!
# The diagonals of every configuration with an edge

`Rule30Diagonals` proves, for the single black cell, that every right diagonal is periodic from
the start with period `2^j` and every left diagonal is eventually periodic with period `2^j`. The
proofs use the seed only through its edges: right of the right edge and left of the left edge
everything is white. So they hold for every configuration that is white beyond some cell, with
the same period bounds.

* `Rd x hi j t = evol x t (hi + t - j)`. If `x` is white right of `hi`, every `Rd x hi j` is
  periodic from time `0` with period `2^j` (`Rd_periodic`). Diagonal `0` is constant, diagonal
  `1` accumulates it, and diagonal `j + 2` accumulates the parity of `Rd (j + 1) âˆ¨ Rd j`.
* `Ld x lo j t = evol x t (lo - t + j)`. If `x` is white left of `lo`, every `Ld x lo j` is
  periodic with period `2^j` from the uniform onset `2^j-1` (`Ld_uniform_period`);
  the original eventual statement remains `Ld_periodic`.
* `evol_eq_Rd`, `evol_eq_Ld`: column `hi - i` at time `t` is `Rd x hi (t + i) t`, and column
  `lo + i` is `Ld x lo (t + i) t`. Each column reads the array of diagonals along a line of slope
  one, as the center column of the seed does (`Rule30Diagonals.center_eq_R`).
* `column_reads_periodic_rows`: so every column of every configuration that is white right of
  some cell is a diagonal readout `t â†¦ A (t + i) t` of an array `A` whose row `j` has period
  dividing `2^j`.

In bitwise form (`Rule30Equivalents.TFunction`), `Rd_periodic` says that for every natural number
`a`, bit `j` of `Î¦^t(a)` has period dividing `2^j` in `t`, where `Î¦(x) = x âŠ• (2x âˆ¨ 4x)`.

So the periodic right diagonals behind the 2-adic odometer of the right edge are
not special to the seed: a proof of Problem 1 cannot get anything from them that it would not
also get for every finite configuration.

Sources: the single-seed statements are `Rule30Diagonals`; E. M. Coven, M. Pivato, R. Yassawi,
*Prevalence of odometers in cellular automata*, Proc. Amer. Math. Soc. 135 (2007) 815â€“821, for
the odometer.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30FiniteDiagonals

open Rule30Jen Rule30Realization Rule30Diagonals

theorem evol_congr {x : Int â†’ Bool} {t : Nat} {p q : Int} (h : p = q) :
    evol x t p = evol x t q := h â–¸ rfl

theorem evol_succ' (x : Int â†’ Bool) (t : Nat) (p a b c : Int) (ha : a = p - 1) (hb : b = p)
    (hc : c = p + 1) : evol x (t + 1) p = rule (evol x t a) (evol x t b) (evol x t c) := by
  subst ha hb hc; rfl

/-! ### Right diagonals -/

/-- The `j`-th diagonal left of the line `hi + t`: `Rd x hi j t = evol x t (hi + t - j)`. -/
def Rd (x : Int â†’ Bool) (hi : Int) (j t : Nat) : Bool := evol x t (hi + t - j)

section Right
variable {x : Int â†’ Bool} {hi : Int} (hright : âˆ€ p, hi < p â†’ x p = false)
include hright

/-- Right of `hi + t`, the evolution is white at time `t`. -/
theorem evol_eq_false_of_gt : âˆ€ (t : Nat) (p : Int), hi + t < p â†’ evol x t p = false
  | 0, p, h => hright p (by omega)
  | t + 1, p, h => by
    show rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1)) = false
    rw [evol_eq_false_of_gt t (p - 1) (by omega), evol_eq_false_of_gt t p (by omega),
      evol_eq_false_of_gt t (p + 1) (by omega)]
    rfl

theorem Rd_zero_succ (t : Nat) : Rd x hi 0 (t + 1) = Rd x hi 0 t := by
  have e : Rd x hi 0 (t + 1) =
      rule (Rd x hi 0 t) (evol x t (hi + t + 1)) (evol x t (hi + t + 2)) :=
    evol_succ' x t _ _ _ _ (by omega) (by omega) (by omega)
  rw [e, evol_eq_false_of_gt hright t _ (by omega), evol_eq_false_of_gt hright t _ (by omega)]
  cases Rd x hi 0 t <;> rfl

theorem Rd_one_succ (t : Nat) : Rd x hi 1 (t + 1) = xor (Rd x hi 1 t) (Rd x hi 0 t) := by
  have e : Rd x hi 1 (t + 1) = rule (Rd x hi 1 t) (Rd x hi 0 t) (evol x t (hi + t + 1)) :=
    evol_succ' x t _ _ _ _ (by omega) (by omega) (by omega)
  rw [e, evol_eq_false_of_gt hright t _ (by omega)]
  cases Rd x hi 1 t <;> cases Rd x hi 0 t <;> rfl

omit hright in
theorem Rd_step (j t : Nat) :
    Rd x hi (j + 2) (t + 1) = xor (Rd x hi (j + 2) t) (Rd x hi (j + 1) t || Rd x hi j t) :=
  evol_succ' x t _ _ _ _ (by omega) (by omega) (by omega)

/-- **Every right diagonal is periodic from the start, with period `2^j`**, for every
configuration that is white right of `hi`. -/
theorem Rd_periodic : âˆ€ j t, Rd x hi j (t + 2 ^ j) = Rd x hi j t := by
  have h0 : âˆ€ t, Rd x hi 0 (t + 1) = Rd x hi 0 t := Rd_zero_succ hright
  have pair : âˆ€ j, (âˆ€ t, Rd x hi j (t + 2 ^ j) = Rd x hi j t) âˆ§
      (âˆ€ t, Rd x hi (j + 1) (t + 2 ^ (j + 1)) = Rd x hi (j + 1) t) := by
    intro j
    induction j with
    | zero =>
      refine âŸ¨fun t => by simpa using h0 t, fun t => ?_âŸ©
      have := xor_accum_periodic (x := Rd x hi 1) (g := Rd x hi 0) (L := 1)
        (fun t => Rd_one_succ hright t) h0 t
      simpa using this
    | succ j ih =>
      refine âŸ¨ih.2, ?_âŸ©
      have hg : âˆ€ t, (Rd x hi (j + 1) (t + 2 ^ (j + 1)) || Rd x hi j (t + 2 ^ (j + 1))) =
          (Rd x hi (j + 1) t || Rd x hi j t) := by
        intro t
        rw [ih.2 t, show 2 ^ (j + 1) = 2 * 2 ^ j by rw [Nat.pow_succ]; omega,
          periodic_double ih.1 t]
      have := xor_accum_periodic (x := Rd x hi (j + 2))
        (g := fun t => Rd x hi (j + 1) t || Rd x hi j t) (L := 2 ^ (j + 1))
        (fun t => Rd_step j t) hg
      intro t
      rw [show 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) by rw [Nat.pow_succ]; omega]
      exact this t
  exact fun j => (pair j).1

/-- The period `2^i` of the right diagonal `i` divides `2^j` for `i â‰¤ j`. -/
theorem Rd_periodic_mul (i k t : Nat) : Rd x hi i (t + k * 2 ^ i) = Rd x hi i t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show t + (k + 1) * 2 ^ i = (t + k * 2 ^ i) + 2 ^ i by rw [Nat.succ_mul]; omega,
      Rd_periodic hright, ih]

end Right

/-- Column `hi - i` at time `t` is the right diagonal `t + i` at time `t`. -/
theorem evol_eq_Rd (x : Int â†’ Bool) (hi : Int) (i t : Nat) :
    evol x t (hi - i) = Rd x hi (t + i) t :=
  evol_congr (by omega)

/-- **Every column reads periodic rows along a diagonal.** If `x` is white right of `hi`, column
`hi - i` is `t â†¦ A (t + i) t` for an array `A` whose row `j` is periodic with period `2^j`. -/
theorem column_reads_periodic_rows {x : Int â†’ Bool} {hi : Int}
    (hright : âˆ€ p, hi < p â†’ x p = false) (i : Nat) :
    âˆƒ A : Nat â†’ Nat â†’ Bool, (âˆ€ j t, A j (t + 2 ^ j) = A j t) âˆ§
      âˆ€ t, evol x t (hi - i) = A (t + i) t :=
  âŸ¨Rd x hi, Rd_periodic hright, fun t => evol_eq_Rd x hi i tâŸ©

/-! ### Left diagonals -/

/-- The `j`-th diagonal right of the line `lo - t`: `Ld x lo j t = evol x t (lo - t + j)`. -/
def Ld (x : Int â†’ Bool) (lo : Int) (j t : Nat) : Bool := evol x t (lo - t + j)

section Left
variable {x : Int â†’ Bool} {lo : Int} (hleft : âˆ€ p, p < lo â†’ x p = false)
include hleft

theorem Ld_zero_succ (t : Nat) : Ld x lo 0 (t + 1) = Ld x lo 0 t := by
  have e : Ld x lo 0 (t + 1) =
      rule (evol x t (lo - t - 2)) (evol x t (lo - t - 1)) (Ld x lo 0 t) :=
    evol_succ' x t _ _ _ _ (by omega) (by omega) (by omega)
  rw [e, Rule30FiniteConfigs.evol_eq_false_of_lt hleft t _ (by omega),
    Rule30FiniteConfigs.evol_eq_false_of_lt hleft t _ (by omega)]
  cases Ld x lo 0 t <;> rfl

theorem Ld_one_succ (t : Nat) : Ld x lo 1 (t + 1) = (Ld x lo 0 t || Ld x lo 1 t) := by
  have e : Ld x lo 1 (t + 1) = rule (evol x t (lo - t - 1)) (Ld x lo 0 t) (Ld x lo 1 t) :=
    evol_succ' x t _ _ _ _ (by omega) (by omega) (by omega)
  rw [e, Rule30FiniteConfigs.evol_eq_false_of_lt hleft t _ (by omega)]
  cases Ld x lo 0 t <;> cases Ld x lo 1 t <;> rfl

omit hleft in
theorem Ld_step (j t : Nat) :
    Ld x lo (j + 2) (t + 1) = xor (Ld x lo j t) (Ld x lo (j + 1) t || Ld x lo (j + 2) t) :=
  evol_succ' x t _ _ _ _ (by omega) (by omega) (by omega)

omit hleft in
/-- Any Boolean array with the left-diagonal recurrence has the explicit
power-of-two clock onset, for every initial row. -/
theorem left_recurrence_uniform_period (b : Nat â†’ Nat â†’ Bool)
    (hzero : âˆ€ t, b 0 (t+1) = b 0 t)
    (hone : âˆ€ t, b 1 (t+1) = (b 0 t || b 1 t))
    (hstep : âˆ€ i t, b (i+2) (t+1) = xor (b i t) (b (i+1) t || b (i+2) t)) :
    âˆ€ i t, 2^i-1 â‰¤ t â†’ b i (t+2^i) = b i t := by
  have pair : âˆ€ i,
      (âˆ€ t, 2^i-1 â‰¤ t â†’ b i (t+2^i) = b i t) âˆ§
      (âˆ€ t, 2^(i+1)-1 â‰¤ t â†’ b (i+1) (t+2^(i+1)) = b (i+1) t) := by
    intro i
    induction i with
    | zero =>
      constructor
      Â· intro t _
        simpa using hzero t
      Â· have ht := transducer_periodic
          (x := b 1) (F := fun t x => b 0 t || x) (T := 0) (L := 1)
          (fun t _ => hone t)
          (fun t _ => by funext x; rw [hzero t])
        simpa using ht
    | succ i ih =>
      refine âŸ¨ih.2, ?_âŸ©
      have hp : 0 < 2^(i+1) := Nat.two_pow_pos _
      have hpow : 2^(i+2) = 2*2^(i+1) := by
        rw [show i+2=(i+1)+1 by omega, Nat.pow_succ]; omega
      have hpow0 : 2^(i+1) = 2*2^i := by rw [Nat.pow_succ]; omega
      have old : âˆ€ t, 2^(i+1)-1 â‰¤ t â†’ b i (t+2^(i+1)) = b i t := by
        intro t ht
        rw [hpow0, show t+2*2^i=(t+2^i)+2^i by omega,
          ih.1 _ (by omega), ih.1 t (by omega)]
      have ht := transducer_periodic
        (x := b (i+2)) (F := fun t x => xor (b i t) (b (i+1) t || x))
        (T := 2^(i+1)-1) (L := 2^(i+1))
        (fun t _ => hstep i t)
        (fun t ht => by funext x; rw [old t ht, ih.2 t ht])
      intro t ht0
      rw [show i+1+1=i+2 by omega, hpow] at ht0 âŠ¢
      exact ht t (by omega)
  exact fun i => (pair i).1

/-- Every left diagonal has period `2^i` from the uniform onset `2^i-1`,
independently of the initial configuration to the right of the white edge. -/
theorem Ld_uniform_period (i t : Nat) (ht : 2^i-1 â‰¤ t) :
    Ld x lo i (t+2^i) = Ld x lo i t :=
  left_recurrence_uniform_period (Ld x lo) (Ld_zero_succ hleft)
    (Ld_one_succ hleft) (fun i t => Ld_step i t) i t ht

/-- **Every left diagonal is eventually periodic, with period `2^j`**, for every configuration
that is white left of `lo`. -/
theorem Ld_periodic : âˆ€ j, âˆƒ T, âˆ€ t, T â‰¤ t â†’ Ld x lo j (t + 2 ^ j) = Ld x lo j t := by
  have h0 : âˆ€ t, Ld x lo 0 t = x lo := by
    intro t
    induction t with
    | zero =>
      show x (lo - ((0 : Nat) : Int) + ((0 : Nat) : Int)) = x lo
      congr 1; omega
    | succ t ih => rw [Ld_zero_succ hleft, ih]
  have h1 : âˆ€ t, 1 â‰¤ t â†’ Ld x lo 1 (t + 1) = Ld x lo 1 t := by
    intro t ht
    obtain âŸ¨s, rflâŸ© : âˆƒ s, t = s + 1 := âŸ¨t - 1, by omegaâŸ©
    rw [Ld_one_succ hleft, Ld_one_succ hleft, h0, h0]
    cases x lo <;> cases Ld x lo 1 s <;> rfl
  have pair : âˆ€ j, (âˆƒ T, âˆ€ t, T â‰¤ t â†’ Ld x lo j (t + 2 ^ j) = Ld x lo j t) âˆ§
      (âˆƒ T, âˆ€ t, T â‰¤ t â†’ Ld x lo (j + 1) (t + 2 ^ (j + 1)) = Ld x lo (j + 1) t) := by
    intro j
    induction j with
    | zero =>
      refine âŸ¨âŸ¨0, fun t _ => by rw [h0, h0]âŸ©, âŸ¨1, fun t ht => ?_âŸ©âŸ©
      rw [show t + 2 ^ (0 + 1) = (t + 1) + 1 by simp, h1 (t + 1) (by omega), h1 t ht]
    | succ j ih =>
      refine âŸ¨ih.2, ?_âŸ©
      obtain âŸ¨âŸ¨Ta, haâŸ©, âŸ¨Tb, hbâŸ©âŸ© := ih
      have hp := Nat.two_pow_pos j
      have ha2 : âˆ€ t, Ta â‰¤ t â†’ Ld x lo j (t + 2 ^ (j + 1)) = Ld x lo j t := by
        intro t ht
        rw [show t + 2 ^ (j + 1) = (t + 2 ^ j) + 2 ^ j by rw [Nat.pow_succ]; omega,
          ha _ (by omega), ha t ht]
      refine âŸ¨max Ta Tb + 2 ^ (j + 1), fun t ht => ?_âŸ©
      have := transducer_periodic (x := Ld x lo (j + 2))
        (F := fun t b => xor (Ld x lo j t) (Ld x lo (j + 1) t || b)) (T := max Ta Tb)
        (L := 2 ^ (j + 1))
        (fun t _ => Ld_step j t)
        (fun t ht => by
          funext b
          rw [ha2 t (by omega), hb t (by omega)])
        t (by omega)
      rw [show 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) by rw [Nat.pow_succ]; omega]
      exact this
  exact fun j => (pair j).1

end Left

/-- Column `lo + i` at time `t` is the left diagonal `t + i` at time `t`. -/
theorem evol_eq_Ld (x : Int â†’ Bool) (lo : Int) (i t : Nat) :
    evol x t (lo + i) = Ld x lo (t + i) t :=
  evol_congr (by omega)

end Rule30FiniteDiagonals
end Ruliology.CellularAutomata
