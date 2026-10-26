module

public import Ruliology.CellularAutomata.Rule30StripCertificates
public import Ruliology.CellularAutomata.Rule30WhiteEnd
public import Ruliology.CellularAutomata.Rule30Certificates.WhiteEndNineChecks

/-!
# The white end from `q = 9`: no eventual `1 0^q` for any `q ≥ 9`

`Rule30WhiteEnd` excludes the eventual center words `1 0^q` for every `q ≥ 10`. Its strip relaxation
fails at `q = 9` (`control_q9`). For `1 0^9`, column `1` is not constant at the white phase two steps
after the black cell in the relaxations we checked, so a plain bitmask strip certificate does not apply there. This module gives a uniform statement
for every `q ≥ 9`.

**Mode certificates.** Fix a word `w`, a strip width `K`, `k` warm-up periods and one white phase
`pe`. Let `S0` be a strip set that contains the strips reachable after `k` periods and is closed
under one more period. At every other white phase, column `1` is constant on the corresponding set
(as in `Rule30StripCertificates.stripCert`). At `pe`, column `1` is a *label* fixed by the strip at
the start of the period: `1` on a set `E1`, `0` on a set `E0`, with `S0 ⊆ E0 ∪ E1`. Two transition
rules are checked on bitmasks:
* after a period labelled `1` comes a period labelled `0` (`applyWord w E1 ⊆ E0`);
* after two periods labelled `0` comes a period labelled `0`.
So along the true history the labels are eventually constant `0` or alternate `0 1 0 1 …`. Either
way `orCol 0` is eventually periodic with period `2 |w|`, which
`Rule30MaskedJen.orCol_not_eventuallyPeriodic` forbids (`not_eventually_word_mode`).

**The instance `1 0^9`** has strip width `12`, `5` warm-up periods and label phase `2`.
`|S0| = 245`, `|E1| = 21`, `|E0| = 224`. In the twelve-cell relaxation the label sequence of every
path is `(0 1)^a 0^ω`, `(1 0)^a 0^ω` or an alternation. Our searches found no such certificate at widths `≤ 11`. The
sets were found by computer search (forward images of the strip relaxation) and are checked by the
kernel.

* `not_eventually_one_zero_nine`: the single-seed center column is not eventually `1 0^9`.
* `not_eventually_white_end_ge9`: **for every `q ≥ 9`** it is not eventually `1 0^q`, whatever the
  transient. `q ≥ 10` is `Rule30WhiteEnd.not_eventuallyWord_white_end`.

The word `0^9 1`, a rotation of `1 0^9`, was excluded before by a rank certificate with `40010` ranks
(AIOvernight, kit pull request 3, closed as a standalone certificate). The mode certificate replaces
it with three bitmask sets, inside the uniform `q ≥ 9` statement.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30WhiteEndNine

open Rule30Jen Rule30Prize Rule30MaskedJen Rule30StripCertificates

/-- The encoding of a strip is unique. -/
theorem enc_unique {K t : Nat} {j : Int} {r r' : Nat} (h : Enc K t j r) (h' : Enc K t j r') : r = r' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < K
  · rw [h.2 i hi, h'.2 i hi]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h.1 (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h'.1 (Nat.pow_le_pow_right (by omega) (by omega)))]


/-- **Mode certificate.** `S0` is the strip set after `k` warm-up periods of `w`, mapped into
itself by one more period. At every white phase other than `pe`, column `1` is constant on the
corresponding set (as in `stripCert`). At the phase `pe` column `1` is a label of the strip at the
start of the period: `1` on `E1`, `0` on `E0`, and `E0 ∪ E1` covers `S0`. The labels obey two
transition rules: after a `1` comes a `0`, and after `0 0` comes a `0`. -/
def modeCert (w : List Bool) (K k pe S0 E0 E1 : Nat) : Bool :=
  subsetB K (iterW K w k (fullSet K)) S0 &&
  subsetB K (applyWord K w S0) S0 &&
  ((List.range w.length).all fun φ => w.getD φ false || φ == pe ||
      colConst K (applyWord K (w.take φ) S0) false || colConst K (applyWord K (w.take φ) S0) true) &&
  decide (pe < w.length) && !(w.getD pe false) &&
  subsetB K S0 (E0 ||| E1) &&
  colConst K (applyWord K (w.take pe) E1) true &&
  colConst K (applyWord K (w.take pe) E0) false &&
  subsetB K (applyWord K w E1) E0 &&
  subsetB K (applyWord K w (applyWord K w E0 &&& E0)) E0

theorem subsetB_spec {K S S' : Nat} (h : subsetB K S S' = true) {r : Nat} (hr : r < 2 ^ K)
    (hS : S.testBit r = true) : S'.testBit r = true := by
  have := allBelow_spec h r hr
  rw [hS, Bool.not_true, Bool.false_or] at this
  exact this

theorem colConst_spec {K S : Nat} {b : Bool} (h : colConst K S b = true) {r : Nat} (hr : r < 2 ^ K)
    (hS : S.testBit r = true) : r.testBit 0 = b := by
  have := allBelow_spec h r hr
  rw [hS, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  exact this

/-- **Soundness of mode certificates.** -/
theorem not_eventually_word_mode (w : List Bool) (K k pe S0 E0 E1 : Nat) (hK : 1 ≤ K)
    (hw : 0 < w.length) (hcert : modeCert w K k pe S0 E0 E1 = true) : ¬ EventuallyWord w := by
  rintro ⟨T, hT⟩
  unfold modeCert at hcert
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcert
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hini, hsub⟩, hforce⟩, hpe⟩, hpew⟩, hcov⟩, hl1⟩, hl0⟩, hd1⟩, hd2⟩ := hcert
  have hblock : ∀ m s, s < w.length → cell (T + m * w.length + s) 0 = w.getD s false := by
    intro m s hs
    rw [hT _ (by omega), show T + m * w.length + s - T = s + m * w.length by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  have hcper : ∀ t, T ≤ t → cell (t + w.length) 0 = cell t 0 := by
    intro t ht
    rw [hT t ht, hT (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
      Nat.add_mod_right]
  -- the strip at the start of period `m` (after warm-up)
  let R : Nat → Nat := fun m => encRow (T + (k + m) * w.length) 0 K
  have hR : ∀ m, Enc K (T + (k + m) * w.length) 0 (R m) := fun m => enc_encRow K _ 0
  have htime : ∀ m, T + (k + m) * w.length + w.length = T + (k + (m + 1)) * w.length := by
    intro m; rw [show k + (m + 1) = (k + m) + 1 by omega, Nat.succ_mul]; omega
  -- one period maps membership forward
  have hstep : ∀ m X, X.testBit (R m) = true → (applyWord K w X).testBit (R (m + 1)) = true := by
    intro m X hX
    obtain ⟨r', he', hS'⟩ := enc_applyWord w _ (R m) X (hR m) hX (fun s hs => hblock (k + m) s hs)
    rw [htime m] at he'
    rw [enc_unique (hR (m + 1)) he']
    exact hS'
  -- the strip is in `S0` at every period start
  have hS0 : ∀ m, S0.testBit (R m) = true := by
    have hstart : ∃ r, Enc K (T + k * w.length) 0 r ∧ (iterW K w k (fullSet K)).testBit r = true := by
      have h0 := enc_encRow K T 0
      have hfull : (fullSet K).testBit (encRow T 0 K) = true := by
        unfold fullSet; rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true h0.1
      exact enc_iterW w k T _ _ h0 hfull (fun m s _ hs => hblock m s hs)
    intro m
    induction m with
    | zero =>
      obtain ⟨r, he, hS⟩ := hstart
      rw [enc_unique (hR 0) (by simpa using he)]; exact subsetB_spec hini he.1 hS
    | succ m ih =>
      exact subsetB_spec hsub (hR (m + 1)).1 (hstep m _ ih)
  -- the column-1 value at phase `φ` of period `m` is read from the strip set reached from `X`
  have hread : ∀ m φ X, φ < w.length → X.testBit (R m) = true →
      ∃ r', r' < 2 ^ K ∧ (applyWord K (w.take φ) X).testBit r' = true ∧
        cell (T + (k + m) * w.length + φ) 1 = r'.testBit 0 := by
    intro m φ X hφ hX
    obtain ⟨r', he', hS'⟩ := enc_applyWord (w.take φ) _ (R m) X (hR m) hX (fun s hs => by
      rw [List.length_take] at hs
      have hs' : s < φ := by omega
      rw [hblock _ s (by omega)]
      simp [List.getD_eq_getElem?_getD, hs'])
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hφ)] at he'
    refine ⟨r', he'.1, hS', ?_⟩
    rw [he'.2 0 (by omega)]; rfl
  -- labels
  let ℓ : Nat → Bool := fun m => cell (T + (k + m) * w.length + pe) 1
  have hlab1 : ∀ m, E1.testBit (R m) = true → ℓ m = true := by
    intro m h
    obtain ⟨r', hr', hS', hc⟩ := hread m pe E1 hpe h
    show cell _ 1 = true
    rw [hc]; exact colConst_spec hl1 hr' hS'
  have hlab0 : ∀ m, E0.testBit (R m) = true → ℓ m = false := by
    intro m h
    obtain ⟨r', hr', hS', hc⟩ := hread m pe E0 hpe h
    show cell _ 1 = false
    rw [hc]; exact colConst_spec hl0 hr' hS'
  have hcover : ∀ m, E0.testBit (R m) = true ∨ E1.testBit (R m) = true := by
    intro m
    have := subsetB_spec hcov (hR m).1 (hS0 m)
    rw [Nat.testBit_or, Bool.or_eq_true] at this
    exact this
  have hd1' : ∀ m, E1.testBit (R m) = true → E0.testBit (R (m + 1)) = true :=
    fun m h => subsetB_spec hd1 (hR (m + 1)).1 (hstep m E1 h)
  have hd2' : ∀ m, E0.testBit (R m) = true → E0.testBit (R (m + 1)) = true →
      E0.testBit (R (m + 2)) = true := by
    intro m h0 h1
    have ha : (applyWord K w E0 &&& E0).testBit (R (m + 1)) = true := by
      rw [Nat.testBit_and, hstep m E0 h0, h1]; rfl
    exact subsetB_spec hd2 (hR (m + 2)).1 (hstep (m + 1) _ ha)
  -- the labels are eventually 2-periodic
  have hper2 : ∃ m0, ∀ m, m0 ≤ m → ℓ (m + 2) = ℓ m := by
    by_cases hA : ∃ m, E0.testBit (R m) = true ∧ E0.testBit (R (m + 1)) = true
    · obtain ⟨m0, h0, h1⟩ := hA
      have hall : ∀ n, E0.testBit (R (m0 + n)) = true ∧ E0.testBit (R (m0 + n + 1)) = true := by
        intro n
        induction n with
        | zero => exact ⟨h0, h1⟩
        | succ n ih =>
          refine ⟨by simpa [Nat.add_assoc] using ih.2, ?_⟩
          have := hd2' (m0 + n) ih.1 ih.2
          simpa [Nat.add_assoc] using this
      refine ⟨m0, fun m hm => ?_⟩
      obtain ⟨n, rfl⟩ : ∃ n, m = m0 + n := ⟨m - m0, by omega⟩
      rw [hlab0 _ (hall n).1, hlab0 _ (by simpa [Nat.add_assoc] using (hall (n + 1)).2)]
    · have hB : ∀ m, E0.testBit (R m) = true → E0.testBit (R (m + 1)) = true → False :=
        fun m h0 h1 => hA ⟨m, h0, h1⟩
      refine ⟨0, fun m _ => ?_⟩
      by_cases h1 : E1.testBit (R m) = true
      · have h0' := hd1' m h1
        have h2 : E1.testBit (R (m + 2)) = true := by
          rcases hcover (m + 2) with h | h
          · exact absurd (hB (m + 1) h0' h) id
          · exact h
        rw [hlab1 _ h1, hlab1 _ h2]
      · have h0 : E0.testBit (R m) = true := by
          rcases hcover m with h | h
          · exact h
          · exact absurd h h1
        have h1' : E1.testBit (R (m + 1)) = true := by
          rcases hcover (m + 1) with h | h
          · exact absurd (hB m h0 h) id
          · exact h
        rw [hlab0 _ h0, hlab0 _ (hd1' (m + 1) h1')]
  obtain ⟨m0, hm0⟩ := hper2
  -- column `1` at the other white phases is forced
  have hforced : ∀ m φ, φ < w.length → w.getD φ false = false → φ ≠ pe →
      cell (T + (k + m) * w.length + φ) 1 =
        !colConst K (applyWord K (w.take φ) S0) false := by
    intro m φ hφ hwφ hne
    obtain ⟨r', hr', hS', hc⟩ := hread m φ _ hφ (hS0 m)
    rw [hc]
    have hf := List.all_eq_true.mp hforce φ (List.mem_range.mpr hφ)
    rw [hwφ, Bool.false_or, show (φ == pe) = false from beq_false_of_ne hne, Bool.false_or] at hf
    cases hc0 : colConst K (applyWord K (w.take φ) S0) false
    · rw [hc0, Bool.false_or] at hf
      rw [colConst_spec hf hr' hS']; rfl
    · rw [colConst_spec hc0 hr' hS']; rfl
  -- `orCol 0` repeats with period `2 |w|` along the periods
  have hrep : ∀ m φ, m0 ≤ m → φ < w.length →
      orCol 0 (T + (k + (m + 2)) * w.length + φ) = orCol 0 (T + (k + m) * w.length + φ) := by
    intro m φ hm hφ
    unfold orCol
    simp only [Int.zero_add]
    rw [hblock (k + (m + 2)) φ hφ, hblock (k + m) φ hφ]
    cases hwφ : w.getD φ false
    · simp only [Bool.false_or]
      by_cases hne : φ = pe
      · subst hne
        exact hm0 m hm
      · rw [hforced (m + 2) φ hφ hwφ hne, hforced m φ hφ hwφ hne]
    · rfl
  refine orCol_not_eventuallyPeriodic 0 ⟨T, w.length, hw, hcper⟩
    ⟨T + (k + m0) * w.length, 2 * w.length, by omega, fun t ht => ?_⟩
  show orCol 0 (t + 2 * w.length) = orCol 0 t
  have hφ : (t - T) % w.length < w.length := Nat.mod_lt _ hw
  have hq : k + m0 ≤ (t - T) / w.length := (Nat.le_div_iff_mul_le hw).2 (by omega)
  have hdec : t = T + (k + ((t - T) / w.length - k)) * w.length + (t - T) % w.length := by
    have hd := Nat.div_add_mod (t - T) w.length
    rw [show k + ((t - T) / w.length - k) = (t - T) / w.length by omega, Nat.mul_comm]
    omega
  have h2 := hrep ((t - T) / w.length - k) ((t - T) % w.length) (by omega) hφ
  rw [← hdec] at h2
  rw [← h2]
  congr 1
  rw [show k + ((t - T) / w.length - k + 2) = (k + ((t - T) / w.length - k)) + 2 by omega,
    Nat.add_mul]
  omega

theorem modeCert_1e9 : modeCert w_1e9 12 5 2 S0_1e9 E0_1e9 E1_1e9 = true := by
  have mc_force : ((List.range w_1e9.length).all fun φ => w_1e9.getD φ false || φ == 2 ||
      colConst 12 (applyWord 12 (w_1e9.take φ) S0_1e9) false ||
      colConst 12 (applyWord 12 (w_1e9.take φ) S0_1e9) true) = true := by
    rw [show w_1e9.length = 10 from rfl, List.all_eq_true]
    intro φ hφ
    have h := List.mem_range.1 hφ
    rcases (by omega : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 ∨ φ = 4 ∨ φ = 5 ∨ φ = 6 ∨ φ = 7 ∨ φ = 8 ∨ φ = 9)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mc_force0
    · exact mc_force1
    · exact mc_force2
    · exact mc_force3
    · exact mc_force4
    · exact mc_force5
    · exact mc_force6
    · exact mc_force7
    · exact mc_force8
    · exact mc_force9
  unfold modeCert
  rw [mc_ini, mc_sub, mc_force, mc_cov, mc_l1, mc_l0, mc_d1, mc_d2]
  decide

/-- **`1 0^9` is excluded**, whatever the transient. -/
theorem not_eventually_one_zero_nine : ¬ EventuallyWord (true :: List.replicate 9 false) :=
  not_eventually_word_mode w_1e9 12 5 2 S0_1e9 E0_1e9 E1_1e9 (by decide) (by decide) modeCert_1e9

/-- **The white end from `q = 9`.** For every `q ≥ 9`, the center column of the single-seed pattern
is not eventually the repeating word `1 0^q`, whatever the transient. -/
theorem not_eventually_white_end_ge9 (q : Nat) (hq : 9 ≤ q) :
    ¬ EventuallyWord (true :: List.replicate q false) := by
  rcases Nat.lt_or_ge q 10 with h | h
  · obtain rfl : q = 9 := by omega
    exact not_eventually_one_zero_nine
  · exact Rule30WhiteEnd.not_eventuallyWord_white_end q h

end Rule30WhiteEndNine
end Ruliology.CellularAutomata
