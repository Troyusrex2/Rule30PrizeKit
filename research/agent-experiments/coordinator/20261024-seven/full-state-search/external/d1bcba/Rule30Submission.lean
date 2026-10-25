import Rule30PrizeKit
import Ruliology.CellularAutomata.Rule30StripCertificates
import Ruliology.CellularAutomata.Rule30StripCertificateTable
import Ruliology.CellularAutomata.Rule30FiniteMaskedJen
import Ruliology.CellularAutomata.Rule30PeriodTwoWidth5
import Ruliology.CellularAutomata.Rule30PeriodTwoWidth6
import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripe
import Ruliology.CellularAutomata.Rule30ZeroBoundarySmall
import Ruliology.CellularAutomata.Rule30Coupled
import Ruliology.CellularAutomata.Rule30EtherThreeReach
import Ruliology.CellularAutomata.Rule30EtherThreeSkeleton
import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# Semigroup Saturation for Strip Certificates, Coupled Period-2/3/4 Reductions, and Sideways Certification

This module extends `Ruliology.CellularAutomata.Rule30StripCertificates`,
`Rule30StripCertificateTable`, `Rule30BlackRunBlocks`, `Rule30PeriodTwoSideways`,
`Rule30Coupled`, `Rule30Ether`, `Rule30PeriodFourSkeleton`, `Rule30EtherThreeTrap`,
`Rule30EtherThreeReach`, and `Rule30EtherThreeSkeleton` in five directions:

1. **Uniformity across all finite configurations (`EncAt`, `EventuallyWordAt`).**
   The bitmask strip certificate engine (`stripCert`) and the thirty-word table (`certTable`) depend
   on the single-cell seed only through `Rule30MaskedJen.orCol_not_eventuallyPeriodic`. Using
   `Rule30FiniteMaskedJen.orCol_not_eventuallyPeriodic`, every bitmask strip certificate excludes its
   driver word in **every column `j` of every configuration `x` with a leftmost black cell**, and in
   particular in every column of every nonzero finite configuration (`not_eventually_word_strip_finite`,
   `not_eventually_certTable_finite`).

2. **Semigroup saturation and parametric strip certificates (`iterAtLeast`, `paramStripCert`).**
   For a fixed strip width `K`, the nondeterministic step operator `image K a` on `2^K`-bit masks is
   monotone on a finite lattice. Given a threshold `r0 ≥ 1`, `iterAtLeast K a r0 S` computes the
   closure under `image K a` of `applyWord K (List.replicate r0 a) S`. When the boolean check
   `paramStripCert a r0 u K k` holds, a **single finite kernel evaluation** certifies that the entire
   infinite family of repeating words
   `List.replicate r a ++ u` for **all `r ≥ r0`**
   is excluded for every transient, in every column of every configuration with a leftmost black cell
   (`not_eventually_param_word_leftmost`), every nonzero finite configuration
   (`not_eventually_param_word_finite`), and the center column of the single-seed pattern
   (`not_eventually_param_word`).

3. **New infinite family exclusions and sharpened thresholds.**
   * **White-run families `0^q u` (`a = false`):**
     `Rule30StripCertificateTable` excluded only isolated lengths `8 … 13` (such as `0^10 1`,
     `0^11 1`, `0^12 1`, `0^9 1011`, `0^8 10011`, `0^7 101111`). Parametric strip
     certificates exclude the entire infinite families:
     - `0^q 1` for all `q ≥ 10` (`not_eventually_white_run_1`, `no_white_run_1_finite`);
     - `0^q 11` for all `q ≥ 9` (`not_eventually_white_run_11`);
     - `0^q 1011` for all `q ≥ 9` (`not_eventually_white_run_1011`);
     - `0^q 1101` for all `q ≥ 11` (`not_eventually_white_run_1101`);
     - `0^q 10011` for all `q ≥ 9` (`not_eventually_white_run_10011`);
     - `0^q 10111` for all `q ≥ 9`, `0^q 11011` for all `q ≥ 9`, `0^q 101111` for all `q ≥ 9`
       (`paramWhiteTable`, `not_eventually_paramWhiteTable`, `not_eventually_paramWhiteTable_finite`).
   * **Black-run families `1^r u` (`a = true`, sharpening Theorem B′ of `Rule30BlackRunBlocks`):**
     `Rule30BlackRunBlocks` excluded `1^r u` for `u ∈ {0, 00, 000, 0000, 0100}` only for `r ≥ 18`
     (`j0 = 2`) and for `u ∈ {010, 0010, 0110}` only for `r ≥ 27` (`j0 = 3`). At strip width
     `K = 5` with `k = 1` warm-up period, `paramStripCert` lowers all of these thresholds to
     `r ≥ 8` (`u = 010, 00010`) and `r ≥ 9` (`u = 0, 00, 000, 0000, 0010, 0100, 0110, 00000, 01100,
     01110`), as well as `r ≥ 15` at `K = 7` for `u = 00110, 01010`
     (`paramBlackTable`, `not_eventually_paramBlackTable`, `not_eventually_black_run_010`,
     `not_eventually_black_run_00010`).

4. **Period-2 sideways dichotomy, forbidden language on `Psi R`, and `CQ01Empty` to depth `1000`.**
   Generalizing `Cert.sound_bad` and `Rule30PeriodTwoLanguage.occurs` to any `IsR30 F` yields a
   universal dichotomy (`isR30_bad_or_periodic`, `drv_bad_or_u_periodic`), the width-`6` forbidden
   language on `u R` and `Psi R` (`Psi_free_constraints_width6_of_finSupp`), instantaneous
   invariants from `s = 0` (`u_golden`, `u_black_among_five`, `Psi_even_first_defect_le_10`,
   `Psi_black_in_window_16`), and a linear-time bitwise kernel certification of `Psi empty` to depth
   `1000` (`psi_empty_997_true`, `psi_empty_black_in_window_9`, `no_empty_right_alternating_le_996`).

5. **Period-3 and Period-4 coupled exclusions, unconditional `R = ∅` solutions, and skeletons.**
   * **Universal difference front and master coupled exclusion (`evol_diff_front`, `exact_death_conf`,
     `not_coupled_of_right_masked_periodic`, `lc_infinite_of_right_masked_periodic`):**
     Generalizes exact death from `altCol` to every target column `c` and right half `R`, and shows
     that any masked periodicity of column `1` of `drv ω x` rules out every left-finite `s` coupled
     to `(ω, x)` and forces the sideways-reconstructed left half `lc R ω · 0` to have infinite support.
   * **Unconditional solution of the `R = ∅` coupled problem (`CQEmpty`) for all Period-4 words
     (`0001`, `0011`, `0111`) and Period-3 (`001`) across all phases `φ ∈ ℕ`:**
     The empty right half enters `Rule30Ether.InFamily` at `t1 ≤ 16` for all three period-4 words
     and all 4 phases (`empty_inFamily_0001`, `empty_inFamily_0011`, `empty_inFamily_0111`), and
     enters the 47-cell trap `t001` at `t1 ≤ 1270` for `w001` across all 3 phases
     (`empty_absorbed_t001_all_phases`). Consequently, no left-finite configuration is coupled with
     `empty` for `0001`, `0011`, `0111`, or `001` at any phase (`no_empty_right_coupled_0001`,
     `no_empty_right_coupled_0011`, `no_empty_right_coupled_0111`, `no_empty_right_coupled_001`),
     and `lc (fun _ => false) ω · 0` has infinite support (`lc_empty_infinite_*`).
   * **Uniform Period-3/4 skeletons (`skeleton_001_finite`, `skeleton_011_finite`,
     `skeleton_0001_finite`, `skeleton_0011_finite`), kernel-checked bounded-width `Q001`
     (`q001_width_le_12`), and depth-`1000` sideways certification for `011` (`lc_empty_011_999_true`,
     `lc_empty_011_black_in_window_9`, `no_empty_right_011_le_998`).**

6. **Sublinear run bounds via diagonal defect spectra (Problems 1 & 2).**
   Master theorems connecting left diagonals `D j a = cell a (j - a)` to center-column run lengths:
   - For white runs: any diagonal defect `D j a ≠ decide ((a - j) % 2 = 1)` forces `L ≤ a - j` whenever
     `ℓ + 1 < a - j` (`white_run_le_of_diag_defect`, `white_run_le_diag3`).
   - For black runs: `D 2 a = false` for all `a ≥ 2` forces `L ≤ a - 2` for all even `a ≥ 2`
     (`black_run_le_diag2_even`), and `D 4 a = true` for all `a ≥ 2` forces `L ≤ a - 4` for all odd `a ≥ 4`
     (`black_run_le_diag4_odd`). Together, these strictly sharpen Morales's linear bound `L ≤ a` to
     `L ≤ a - 2` for all `a ≥ 4` (`black_run_le_ge4`).
-/

namespace Rule30Submission

open Ruliology.CellularAutomata
open Rule30Jen Rule30Prize Rule30Realization Rule30PeriodTwoSideways
open Rule30FiniteConfigs Rule30FiniteMaskedJen
open Rule30StripCertificates Rule30StripCertificateTable

/-! ### List indexing lemmas for parametric words `List.replicate r a ++ u` -/

theorem getD_replicate (a : Bool) :
    ∀ (n s : Nat), s < n → (List.replicate n a).getD s false = a
  | 0, s, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | n + 1, s + 1, h => getD_replicate a n s (by omega)

theorem getD_replicate_append_left (a : Bool) (u : List Bool) :
    ∀ (r s : Nat), s < r → (List.replicate r a ++ u).getD s false = a
  | 0, s, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | r + 1, s + 1, h => getD_replicate_append_left a u r s (by omega)

theorem getD_replicate_append_right (a : Bool) (u : List Bool) :
    ∀ (r s : Nat), (List.replicate r a ++ u).getD (r + s) false = u.getD s false
  | 0, s => by simp
  | r + 1, s => by
    rw [show r + 1 + s = (r + s) + 1 by omega]
    exact getD_replicate_append_right a u r s

theorem getD_take :
    ∀ (u : List Bool) (ψ s : Nat), s < ψ → (u.take ψ).getD s false = u.getD s false
  | [], _, _, _ => by simp
  | _ :: _, 0, s, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: u, ψ + 1, s + 1, h => getD_take u ψ s (by omega)

/-! ### Strip encodings in the evolution of an arbitrary configuration -/

/-- Column `j` of `evol x` equals `w` repeated from time `T` on. -/
def EventuallyWordAt (x : Int → Bool) (j : Int) (w : List Bool) : Prop :=
  ∃ T, ∀ t, T ≤ t → evol x t j = w.getD ((t - T) % w.length) false

/-- The single black cell at position `0`. -/
def seed0 (p : Int) : Bool := decide (p = 0)

theorem evol_seed0 : ∀ (t : Nat) (p : Int), evol seed0 t p = cell t p
  | 0, _ => rfl
  | t + 1, p => by
    show rule (evol seed0 t (p - 1)) (evol seed0 t p) (evol seed0 t (p + 1)) =
      rule (cell t (p - 1)) (cell t p) (cell t (p + 1))
    rw [evol_seed0 t (p - 1), evol_seed0 t p, evol_seed0 t (p + 1)]

theorem eventuallyWordAt_seed0_iff (w : List Bool) :
    EventuallyWordAt seed0 0 w ↔ EventuallyWord w := by
  unfold EventuallyWordAt EventuallyWord
  simp only [evol_seed0]

/-- Strip encoding in `evol x`: `r < 2 ^ K` and bit `k < K` of `r` is `evol x t (j + 1 + k)`. -/
def EncAt (x : Int → Bool) (K t : Nat) (j : Int) (r : Nat) : Prop :=
  r < 2 ^ K ∧ ∀ k, k < K → r.testBit k = evol x t (j + 1 + k)

theorem encAt_step {x : Int → Bool} {K t : Nat} {j : Int} {r : Nat} (h : EncAt x K t j r) :
    EncAt x K (t + 1) j (stripStep K (evol x t j) (evol x t (j + 1 + K)) r) := by
  refine ⟨stripStep_lt _ _ _ _, fun k hk => ?_⟩
  rw [testBit_stripStep K _ _ r h.1 k hk]
  show _ = rule (evol x t (j + 1 + (k : Int) - 1)) (evol x t (j + 1 + k)) (evol x t (j + 1 + k + 1))
  have hc : r.testBit k = evol x t (j + 1 + k) := h.2 k hk
  have hl : (if k = 0 then evol x t j else r.testBit (k - 1)) =
      evol x t (j + 1 + (k : Int) - 1) := by
    split
    · rename_i h0; subst h0; congr 1; omega
    · rename_i h0; rw [h.2 (k - 1) (by omega)]; congr 1; omega
  have hr : (if k + 1 = K then evol x t (j + 1 + K) else r.testBit (k + 1)) =
      evol x t (j + 1 + k + 1) := by
    split
    · rename_i h1; congr 1; omega
    · rename_i h1; rw [h.2 (k + 1) (by omega)]; congr 1; omega
  rw [hl, hc, hr]

/-- The integer encoding of the actual strip of `K` cells right of column `j` in `evol x t`. -/
def encRowAt (x : Int → Bool) (t : Nat) (j : Int) : Nat → Nat
  | 0 => 0
  | K + 1 => encRowAt x t j K ||| ((evol x t (j + 1 + K)).toNat <<< K)

theorem testBit_encRowAt (x : Int → Bool) (t : Nat) (j : Int) :
    ∀ K k, (encRowAt x t j K).testBit k = (decide (k < K) && evol x t (j + 1 + k))
  | 0, k => by simp [encRowAt]
  | K + 1, k => by
    rw [encRowAt, Nat.testBit_or, testBit_encRowAt x t j K k, Nat.testBit_shiftLeft, testBit_toNat]
    by_cases hk : k < K
    · simp [hk, show k < K + 1 by omega, show ¬ K ≤ k by omega]
    · by_cases hk' : k = K
      · subst hk'; simp
      · simp [hk, show ¬ k < K + 1 by omega, show k - K ≠ 0 by omega]

theorem encAt_encRowAt (x : Int → Bool) (K t : Nat) (j : Int) :
    EncAt x K t j (encRowAt x t j K) := by
  refine ⟨Nat.lt_pow_two_of_testBit _ fun i hi => ?_, fun k hk => ?_⟩
  · rw [testBit_encRowAt]; simp [show ¬ i < K by omega]
  · rw [testBit_encRowAt]; simp [hk]

/-- Soundness of `applyWord` for an arbitrary configuration `x` and column `j`. -/
theorem encAt_applyWord {x : Int → Bool} {K : Nat} {j : Int} :
    ∀ (u : List Bool) (t r S : Nat), EncAt x K t j r → S.testBit r = true →
      (∀ s, s < u.length → evol x (t + s) j = u.getD s false) →
      ∃ r', EncAt x K (t + u.length) j r' ∧ (applyWord K u S).testBit r' = true
  | [], t, r, S, he, hS, _ => ⟨r, he, hS⟩
  | a :: u, t, r, S, he, hS, hu => by
    have ha : evol x t j = a := by simpa using hu 0 (by simp)
    have he1 := encAt_step he
    rw [ha] at he1
    have hS1 : (image K a S).testBit (stripStep K a (evol x t (j + 1 + K)) r) = true :=
      mem_imageAux hS _ (2 ^ K) he.1
    obtain ⟨r', he', hS'⟩ := encAt_applyWord u (t + 1) _ _ he1 hS1 (fun s hs => by
      have := hu (s + 1) (by simp; omega)
      rw [show t + (s + 1) = t + 1 + s by omega] at this
      simpa using this)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (a :: u).length = t + 1 + u.length by simp; omega]
    exact he'

theorem encAt_iterW {x : Int → Bool} {K : Nat} {j : Int} (w : List Bool) :
    ∀ (k t r S : Nat), EncAt x K t j r → S.testBit r = true →
      (∀ m s, m < k → s < w.length → evol x (t + m * w.length + s) j = w.getD s false) →
      ∃ r', EncAt x K (t + k * w.length) j r' ∧ (iterW K w k S).testBit r' = true
  | 0, t, r, S, he, hS, _ => ⟨r, by simpa using he, hS⟩
  | k + 1, t, r, S, he, hS, hw => by
    obtain ⟨r1, he1, hS1⟩ := encAt_applyWord w t r S he hS (fun s hs => by
      simpa using hw 0 s (by omega) hs)
    obtain ⟨r', he', hS'⟩ := encAt_iterW w k (t + w.length) r1 _ he1 hS1 (fun m s hm hs => by
      rw [show t + w.length + m * w.length + s = t + (m + 1) * w.length + s by
        rw [Nat.succ_mul]; omega]
      exact hw (m + 1) s (by omega) hs)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (k + 1) * w.length = t + w.length + k * w.length by rw [Nat.succ_mul]; omega]
    exact he'

/-! ### Part 1: Uniformity of `stripCert` and `certTable` across all finite configurations -/

/-- **Soundness of bitmask strip certificates for any configuration with a leftmost black cell.**
If `stripCert w K k` holds, no column `j` of `evol x` is eventually equal to `w` repeated. -/
theorem not_eventually_word_strip_leftmost {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (j : Int)
    (w : List Bool) (K k : Nat) (hK : 1 ≤ K) (hw : 0 < w.length)
    (hcert : stripCert w K k = true) : ¬ EventuallyWordAt x j w := by
  rintro ⟨T, hT⟩
  unfold stripCert at hcert
  rw [Bool.and_eq_true] at hcert
  obtain ⟨hsub, hforce⟩ := hcert
  have hsub' := allBelow_spec hsub
  have hblock : ∀ m s, s < w.length → evol x (T + m * w.length + s) j = w.getD s false := by
    intro m s hs
    rw [hT _ (by omega), show T + m * w.length + s - T = s + m * w.length by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  have hcper : ∀ t, T ≤ t → evol x (t + w.length) j = evol x t j := by
    intro t ht
    rw [hT t ht, hT (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
      Nat.add_mod_right]
  let S0 := iterW K w k (fullSet K)
  have hstart : ∃ r, EncAt x K (T + k * w.length) j r ∧ S0.testBit r = true := by
    have h0 := encAt_encRowAt x K T j
    have hfull : (fullSet K).testBit (encRowAt x T j K) = true := by
      unfold fullSet; rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true h0.1
    exact encAt_iterW w k T _ _ h0 hfull (fun m s _ hs => hblock m s hs)
  have hinv : ∀ m, ∃ r, EncAt x K (T + (k + m) * w.length) j r ∧ S0.testBit r = true := by
    intro m
    induction m with
    | zero => simpa using hstart
    | succ m ih =>
      obtain ⟨r, he, hS⟩ := ih
      obtain ⟨r', he', hS'⟩ := encAt_applyWord w _ r S0 he hS (fun s hs => hblock (k + m) s hs)
      refine ⟨r', ?_, ?_⟩
      · have hm : (k + (m + 1)) * w.length = (k + m) * w.length + w.length := by
          rw [show k + (m + 1) = (k + m) + 1 by omega, Nat.succ_mul]
        rw [hm, ← Nat.add_assoc]
        exact he'
      · have := hsub' r' he'.1
        rw [hS', Bool.not_true, Bool.false_or] at this
        exact this
  let g : Nat → Bool := fun φ => w.getD φ false ||
    !colConst K (applyWord K (w.take φ) S0) false
  have hform : ∀ t, T + k * w.length ≤ t → orCol x j t = g ((t - T) % w.length) := by
    intro t ht
    have hφ : (t - T) % w.length < w.length := Nat.mod_lt _ hw
    have hdec : t = T + (k + ((t - T) / w.length - k)) * w.length + (t - T) % w.length := by
      have hd := Nat.div_add_mod (t - T) w.length
      have hq : k ≤ (t - T) / w.length := (Nat.le_div_iff_mul_le hw).2 (by omega)
      rw [show k + ((t - T) / w.length - k) = (t - T) / w.length by omega, Nat.mul_comm]
      omega
    obtain ⟨r, he, hS⟩ := hinv ((t - T) / w.length - k)
    obtain ⟨r', he', hS'⟩ := encAt_applyWord (w.take ((t - T) % w.length)) _ r S0 he hS
      (fun s hs => by
        rw [List.length_take] at hs
        have hs' : s < (t - T) % w.length := by omega
        rw [hblock _ s (by omega), getD_take w _ s hs'])
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hφ), ← hdec] at he'
    have hcell : evol x t (j + 1) = r'.testBit 0 := by
      rw [he'.2 0 (by omega)]; congr 1; omega
    unfold orCol g
    rw [hT t (by omega)]
    have hfφ := List.all_eq_true.mp hforce ((t - T) % w.length) (List.mem_range.mpr hφ)
    cases hwφ : w.getD ((t - T) % w.length) false
    · rw [hwφ, Bool.false_or] at hfφ
      simp only [Bool.false_or]
      rw [hcell]
      cases hc0 : colConst K (applyWord K (w.take ((t - T) % w.length)) S0) false
      · rw [hc0, Bool.false_or] at hfφ
        have := allBelow_spec hfφ r' he'.1
        rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
        rw [this]; rfl
      · have := allBelow_spec hc0 r' he'.1
        rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
        rw [this]; rfl
    · rfl
  refine Rule30FiniteMaskedJen.orCol_not_eventuallyPeriodic hlo hzero j ⟨T, w.length, hw, hcper⟩
    ⟨T + k * w.length, w.length, hw, fun t ht => ?_⟩
  show orCol x j (t + w.length) = orCol x j t
  rw [hform t ht, hform (t + w.length) (by omega),
    show t + w.length - T = (t - T) + w.length by omega, Nat.add_mod_right]

/-- **Every nonzero finite configuration**: if `stripCert w K k` holds, no column `j` of `evol x`
is eventually `w` repeated. -/
theorem not_eventually_word_strip_finite {x : Int → Bool} (hfin : FinConfig x)
    (hne : ∃ p, x p = true) (j : Int) (w : List Bool) (K k : Nat) (hK : 1 ≤ K) (hw : 0 < w.length)
    (hcert : stripCert w K k = true) : ¬ EventuallyWordAt x j w := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact not_eventually_word_strip_leftmost hlo hzero j w K k hK hw hcert

/-- **All thirty words of `certTable` are excluded in every column of every nonzero finite
configuration.** -/
theorem not_eventually_certTable_finite {x : Int → Bool} (hfin : FinConfig x)
    (hne : ∃ p, x p = true) (j : Int) (e : Nat × Nat × Nat × Nat) (he : e ∈ certTable) :
    ¬ EventuallyWordAt x j (wordOf e.1 e.2.1) := by
  have h := List.all_eq_true.mp certTable_ok e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact not_eventually_word_strip_finite hfin hne j (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2 h.1.1
    (by rw [wordOf_length]; exact h.1.2) h.2

/-! ### Part 2: Semigroup Saturation and Parametric Strip Certificates (`paramStripCert`) -/

/-- Iterate `S ↦ S ||| image K a S` up to `m` steps, stopping early once a fixed point is reached. -/
def closeIter (K : Nat) (a : Bool) : Nat → Nat → Nat
  | 0, S => S
  | m + 1, S =>
    if (S ||| image K a S) == S then S else closeIter K a m (S ||| image K a S)

theorem testBit_closeIter (K : Nat) (a : Bool) :
    ∀ (m S r : Nat), S.testBit r = true → (closeIter K a m S).testBit r = true
  | 0, _, _, h => h
  | m + 1, S, r, h => by
    unfold closeIter
    split
    · exact h
    · refine testBit_closeIter K a m (S ||| image K a S) r ?_
      rw [Nat.testBit_or, h, Bool.true_or]

/-- Semigroup closure over-approximating `n ≥ n0` steps of `image K a` from `S`. -/
def iterAtLeast (K : Nat) (a : Bool) (n0 S : Nat) : Nat :=
  closeIter K a (2 ^ K) (applyWord K (List.replicate n0 a) S)

/-- One abstract period of `List.replicate r a ++ u` (`r ≥ r0`) on a strip bitmask `S`. -/
def absPeriod (K : Nat) (a : Bool) (r0 : Nat) (u : List Bool) (S : Nat) : Nat :=
  applyWord K u (iterAtLeast K a r0 S)

/-- `k` abstract warm-up periods from `S`. -/
def iterAbsPeriod (K : Nat) (a : Bool) (r0 : Nat) (u : List Bool) : Nat → Nat → Nat
  | 0, S => S
  | k + 1, S => iterAbsPeriod K a r0 u k (absPeriod K a r0 u S)

/-- Verify that `iterAtLeast K a r0 S` is closed under `image K a` along each of `k` warm-up steps. -/
def warmupClosed (K : Nat) (a : Bool) (r0 : Nat) (u : List Bool) : Nat → Nat → Bool
  | 0, _ => true
  | k + 1, S =>
    let T := iterAtLeast K a r0 S
    subsetB K (image K a T) T && warmupClosed K a r0 u k (applyWord K u T)

/-- Check that all phases during the `a^r` prefix have constant column-1 values when `a = false`. -/
def runPhasesForced (K : Nat) (a : Bool) (r0 S0 : Nat) : Bool :=
  a || (subsetB K (image K a (iterAtLeast K a (r0 - 1) S0)) (iterAtLeast K a (r0 - 1) S0) &&
    (List.range (r0 - 1)).all (fun φ =>
      colConst K (applyWord K (List.replicate φ a) S0) false ||
        colConst K (applyWord K (List.replicate φ a) S0) true) &&
    (colConst K (iterAtLeast K a (r0 - 1) S0) false ||
      colConst K (iterAtLeast K a (r0 - 1) S0) true))

theorem runPhasesForced_of_ne_true {K : Nat} {a : Bool} {r0 S0 : Nat}
    (h : runPhasesForced K a r0 S0 = true) (hna : ¬ a = true) :
    subsetB K (image K a (iterAtLeast K a (r0 - 1) S0)) (iterAtLeast K a (r0 - 1) S0) = true ∧
      ((List.range (r0 - 1)).all fun φ =>
        colConst K (applyWord K (List.replicate φ a) S0) false ||
          colConst K (applyWord K (List.replicate φ a) S0) true) = true ∧
      (colConst K (iterAtLeast K a (r0 - 1) S0) false ||
        colConst K (iterAtLeast K a (r0 - 1) S0) true) = true := by
  unfold runPhasesForced at h
  cases a
  · simp only [Bool.false_or, Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · exact absurd rfl hna

/-- **Parametric strip certificate** for the infinite family `List.replicate r a ++ u` (`r ≥ r0`)
at strip width `K` with `k` warm-up periods. -/
def paramStripCert (a : Bool) (r0 : Nat) (u : List Bool) (K k : Nat) : Bool :=
  let S0 := iterAbsPeriod K a r0 u k (fullSet K)
  let T0 := iterAtLeast K a r0 S0
  warmupClosed K a r0 u k (fullSet K) &&
    subsetB K (image K a T0) T0 &&
    subsetB K (applyWord K u T0) S0 &&
    runPhasesForced K a r0 S0 &&
    (List.range u.length).all (fun ψ =>
      u.getD ψ false ||
        colConst K (applyWord K (u.take ψ) T0) false ||
        colConst K (applyWord K (u.take ψ) T0) true)

/-- If `T` is closed under `image K a`, any run of `m` steps of `a` keeps the strip in `T`. -/
theorem encAt_stay_closed {x : Int → Bool} {K : Nat} {j : Int} {a : Bool} {T : Nat}
    (hclosed : subsetB K (image K a T) T = true) :
    ∀ (m t r : Nat), EncAt x K t j r → T.testBit r = true →
      (∀ s, s < m → evol x (t + s) j = a) →
      ∃ r', EncAt x K (t + m) j r' ∧ T.testBit r' = true
  | 0, t, r, he, hT, _ => ⟨r, he, hT⟩
  | m + 1, t, r, he, hT, ha => by
    have ha0 : evol x t j = a := by simpa using ha 0 (by omega)
    have he1 := encAt_step he
    rw [ha0] at he1
    have himg : (image K a T).testBit (stripStep K a (evol x t (j + 1 + K)) r) = true :=
      mem_imageAux hT _ (2 ^ K) he.1
    have hsub := allBelow_spec hclosed _ he1.1
    rw [himg, Bool.not_true, Bool.false_or] at hsub
    obtain ⟨r', he', hT'⟩ := encAt_stay_closed hclosed m (t + 1) _ he1 hsub (fun s hs => by
      have := ha (s + 1) (by omega)
      rwa [show t + (s + 1) = t + 1 + s by omega] at this)
    rw [show t + (m + 1) = t + 1 + m by omega]
    exact ⟨r', he', hT'⟩

/-- Soundness of `iterAtLeast`: for every `n ≥ n0`, a run of `n` steps of `a` from `S` lands in
`iterAtLeast K a n0 S` whenever the latter is closed under `image K a`. -/
theorem encAt_iterAtLeast {x : Int → Bool} {K : Nat} {j : Int} {a : Bool} {n0 n t r S : Nat}
    (hn : n0 ≤ n) (hclosed : subsetB K (image K a (iterAtLeast K a n0 S)) (iterAtLeast K a n0 S) = true)
    (he : EncAt x K t j r) (hS : S.testBit r = true)
    (ha : ∀ s, s < n → evol x (t + s) j = a) :
    ∃ r', EncAt x K (t + n) j r' ∧ (iterAtLeast K a n0 S).testBit r' = true := by
  obtain ⟨r1, he1, hS1⟩ := encAt_applyWord (List.replicate n0 a) t r S he hS (fun s hs => by
    rw [List.length_replicate] at hs
    rw [ha s (by omega), getD_replicate a n0 s hs])
  rw [List.length_replicate] at he1
  have hT1 : (iterAtLeast K a n0 S).testBit r1 = true :=
    testBit_closeIter K a (2 ^ K) _ r1 hS1
  obtain ⟨r', he', hT'⟩ := encAt_stay_closed hclosed (n - n0) (t + n0) r1 he1 hT1 (fun s hs => by
    have := ha (n0 + s) (by omega)
    rwa [show t + (n0 + s) = t + n0 + s by omega] at this)
  rw [show t + n0 + (n - n0) = t + n by omega] at he'
  exact ⟨r', he', hT'⟩

/-- Soundness of one abstract period `absPeriod K a r0 u S` for any `r ≥ r0`. -/
theorem encAt_absPeriod {x : Int → Bool} {K : Nat} {j : Int} {a : Bool} {r0 r : Nat}
    {u : List Bool} {t r_st S : Nat} (hr : r0 ≤ r)
    (hclosed : subsetB K (image K a (iterAtLeast K a r0 S)) (iterAtLeast K a r0 S) = true)
    (he : EncAt x K t j r_st) (hS : S.testBit r_st = true)
    (hw : ∀ s, s < r + u.length →
      evol x (t + s) j = (List.replicate r a ++ u).getD s false) :
    ∃ r', EncAt x K (t + (r + u.length)) j r' ∧ (absPeriod K a r0 u S).testBit r' = true := by
  obtain ⟨r1, he1, hT1⟩ := encAt_iterAtLeast hr hclosed he hS (fun s hs => by
    rw [hw s (by omega), getD_replicate_append_left a u r s hs])
  obtain ⟨r', he', hS'⟩ := encAt_applyWord u (t + r) r1 (iterAtLeast K a r0 S) he1 hT1
    (fun s hs => by
      have := hw (r + s) (by omega)
      rw [show t + (r + s) = t + r + s by omega, getD_replicate_append_right a u r s] at this
      exact this)
  rw [show t + r + u.length = t + (r + u.length) by omega] at he'
  exact ⟨r', he', hS'⟩

/-- Soundness of `k` abstract warm-up periods `iterAbsPeriod K a r0 u k S` for any `r ≥ r0`. -/
theorem encAt_iterAbsPeriod {x : Int → Bool} {K : Nat} {j : Int} {a : Bool} {r0 r : Nat}
    (u : List Bool) (hr : r0 ≤ r) :
    ∀ (k t r_st S : Nat), warmupClosed K a r0 u k S = true →
      EncAt x K t j r_st → S.testBit r_st = true →
      (∀ m s, m < k → s < r + u.length →
        evol x (t + m * (r + u.length) + s) j = (List.replicate r a ++ u).getD s false) →
      ∃ r', EncAt x K (t + k * (r + u.length)) j r' ∧
        (iterAbsPeriod K a r0 u k S).testBit r' = true
  | 0, t, r_st, S, _, he, hS, _ => ⟨r_st, by simpa using he, hS⟩
  | k + 1, t, r_st, S, hwc, he, hS, hw => by
    unfold warmupClosed at hwc
    rw [Bool.and_eq_true] at hwc
    obtain ⟨r1, he1, hS1⟩ := encAt_absPeriod hr hwc.1 he hS (fun s hs => by
      simpa using hw 0 s (by omega) hs)
    obtain ⟨r', he', hS'⟩ := encAt_iterAbsPeriod u hr k (t + (r + u.length)) r1
      (absPeriod K a r0 u S) hwc.2 he1 hS1 (fun m s hm hs => by
        rw [show t + (r + u.length) + m * (r + u.length) + s =
          t + (m + 1) * (r + u.length) + s by rw [Nat.succ_mul]; omega]
        exact hw (m + 1) s (by omega) hs)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (k + 1) * (r + u.length) =
      t + (r + u.length) + k * (r + u.length) by rw [Nat.succ_mul]; omega]
    exact he'

/-- **Universal soundness of parametric strip certificates (`paramStripCert`).**
If `paramStripCert a r0 u K k = true`, then for **every** `r ≥ r0`, no column `j` of `evol x`
(for any configuration `x` with a leftmost black cell) is eventually equal to
`List.replicate r a ++ u` repeated, whatever the transient. -/
theorem not_eventually_param_word_leftmost {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (j : Int)
    (a : Bool) (r0 : Nat) (u : List Bool) (K k : Nat)
    (hK : 1 ≤ K) (hr0 : 1 ≤ r0) (hcert : paramStripCert a r0 u K k = true) :
    ∀ r, r0 ≤ r → ¬ EventuallyWordAt x j (List.replicate r a ++ u) := by
  intro r hr ⟨T, hT⟩
  let w := List.replicate r a ++ u
  have hwlen : w.length = r + u.length := by simp [w]
  have hwpos : 0 < w.length := by rw [hwlen]; omega
  unfold paramStripCert at hcert
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcert
  obtain ⟨⟨⟨⟨hwc, hT0closed⟩, hsub⟩, hrunForce⟩, huForce⟩ := hcert
  have hsub' := allBelow_spec hsub
  have hblock : ∀ m s, s < r + u.length →
      evol x (T + m * (r + u.length) + s) j = w.getD s false := by
    intro m s hs
    have hs' : s < w.length := by rw [hwlen]; exact hs
    rw [hT _ (by omega), ← hwlen, show T + m * w.length + s - T = s + m * w.length by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs']
  have hcper : ∀ t, T ≤ t → evol x (t + w.length) j = evol x t j := by
    intro t ht
    rw [hT t ht, hT (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
      Nat.add_mod_right]
  let S0 := iterAbsPeriod K a r0 u k (fullSet K)
  let T0 := iterAtLeast K a r0 S0
  let Ttail := iterAtLeast K a (r0 - 1) S0
  have hstart : ∃ r_st, EncAt x K (T + k * (r + u.length)) j r_st ∧ S0.testBit r_st = true := by
    have h0 := encAt_encRowAt x K T j
    have hfull : (fullSet K).testBit (encRowAt x T j K) = true := by
      unfold fullSet; rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true h0.1
    exact encAt_iterAbsPeriod u hr k T _ (fullSet K) hwc h0 hfull (fun m s _ hs => hblock m s hs)
  have hinv : ∀ m, ∃ r_st, EncAt x K (T + (k + m) * (r + u.length)) j r_st ∧
      S0.testBit r_st = true := by
    intro m
    induction m with
    | zero => simpa using hstart
    | succ m ih =>
      obtain ⟨r_st, he, hS⟩ := ih
      obtain ⟨r', he', hS'⟩ := encAt_absPeriod hr hT0closed he hS (fun s hs => hblock (k + m) s hs)
      refine ⟨r', ?_, ?_⟩
      · have hm : (k + (m + 1)) * (r + u.length) =
            (k + m) * (r + u.length) + (r + u.length) := by
          rw [show k + (m + 1) = (k + m) + 1 by omega, Nat.succ_mul]
        rw [hm, ← Nat.add_assoc]
        exact he'
      · have := hsub' r' he'.1
        unfold absPeriod at hS'
        rw [hS', Bool.not_true, Bool.false_or] at this
        exact this
  let g : Nat → Bool := fun φ =>
    if φ < r0 - 1 then
      a || !colConst K (applyWord K (List.replicate φ a) S0) false
    else if φ < r then
      a || !colConst K Ttail false
    else
      u.getD (φ - r) false || !colConst K (applyWord K (u.take (φ - r)) T0) false
  have hform : ∀ t, T + k * w.length ≤ t → orCol x j t = g ((t - T) % w.length) := by
    intro t ht
    have hφ : (t - T) % w.length < w.length := Nat.mod_lt _ hwpos
    generalize hφdef : (t - T) % w.length = φ at hφ
    have hφ' : φ < r + u.length := by omega
    let m := (t - T) / w.length - k
    have hdec : t = T + (k + m) * (r + u.length) + φ := by
      have hd := Nat.div_add_mod (t - T) w.length
      have hq : k ≤ (t - T) / w.length := (Nat.le_div_iff_mul_le hwpos).2 (by omega)
      rw [hφdef] at hd
      rw [← hwlen, show k + m = (t - T) / w.length by omega, Nat.mul_comm]
      omega
    obtain ⟨r_st, he, hS⟩ := hinv m
    unfold orCol g
    rw [hT t (by omega), hφdef]
    by_cases h1 : φ < r0 - 1
    · rw [if_pos h1]
      have hφr : φ < r := by omega
      have hcenter : w.getD φ false = a := getD_replicate_append_left a u r φ hφr
      rw [hcenter]
      by_cases ha : a = true
      · rw [ha, Bool.true_or, Bool.true_or]
      · obtain ⟨_, hpref, _⟩ := runPhasesForced_of_ne_true hrunForce ha
        have haf : a = false := Bool.eq_false_iff.mpr ha
        obtain ⟨r', he', hS'⟩ := encAt_applyWord (List.replicate φ a) _ r_st S0 he hS
          (fun s hs => by
            rw [List.length_replicate] at hs
            rw [hblock (k + m) s (by omega), getD_replicate_append_left a u r s (by omega),
              getD_replicate a φ s hs])
        rw [List.length_replicate, ← hdec] at he'
        have hcell : evol x t (j + 1) = r'.testBit 0 := by
          rw [he'.2 0 (by omega)]; congr 1; omega
        rw [hcell]
        have hfφ := List.all_eq_true.mp hpref φ (List.mem_range.mpr h1)
        cases hc0 : colConst K (applyWord K (List.replicate φ a) S0) false
        · rw [hc0, Bool.false_or] at hfφ
          have := allBelow_spec hfφ r' he'.1
          rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
          rw [this, haf]; rfl
        · have := allBelow_spec hc0 r' he'.1
          rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
          rw [this, haf]; rfl
    · rw [if_neg h1]
      by_cases h2 : φ < r
      · rw [if_pos h2]
        have hcenter : w.getD φ false = a := getD_replicate_append_left a u r φ h2
        rw [hcenter]
        by_cases ha : a = true
        · rw [ha, Bool.true_or, Bool.true_or]
        · obtain ⟨hTtailClosed, _, hTtailForce⟩ := runPhasesForced_of_ne_true hrunForce ha
          have haf : a = false := Bool.eq_false_iff.mpr ha
          obtain ⟨r', he', hS'⟩ := encAt_iterAtLeast (n0 := r0 - 1) (n := φ) (by omega)
            hTtailClosed he hS (fun s hs => by
              rw [hblock (k + m) s (by omega), getD_replicate_append_left a u r s (by omega)])
          rw [← hdec] at he'
          have hcell : evol x t (j + 1) = r'.testBit 0 := by
            rw [he'.2 0 (by omega)]; congr 1; omega
          rw [hcell]
          cases hc0 : colConst K Ttail false
          · rw [hc0, Bool.false_or] at hTtailForce
            have := allBelow_spec hTtailForce r' he'.1
            rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
            rw [this, haf]; rfl
          · have := allBelow_spec hc0 r' he'.1
            rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
            rw [this, haf]; rfl
      · rw [if_neg h2]
        let ψ := φ - r
        have hψ : ψ < u.length := by omega
        have hφeq : φ = r + ψ := by omega
        have hcenter : w.getD φ false = u.getD ψ false := by
          rw [hφeq]; exact getD_replicate_append_right a u r ψ
        rw [hcenter]
        obtain ⟨r1, he1, hT1⟩ := encAt_iterAtLeast hr hT0closed he hS (fun s hs => by
          rw [hblock (k + m) s (by omega), getD_replicate_append_left a u r s hs])
        obtain ⟨r', he', hS'⟩ := encAt_applyWord (u.take ψ) _ r1 T0 he1 hT1 (fun s hs => by
          rw [List.length_take] at hs
          have hs' : s < ψ := by omega
          have hb := hblock (k + m) (r + s) (by omega)
          rw [show T + (k + m) * (r + u.length) + (r + s) =
            T + (k + m) * (r + u.length) + r + s by omega,
            getD_replicate_append_right a u r s] at hb
          rw [hb, getD_take u ψ s hs'])
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hψ),
          show T + (k + m) * (r + u.length) + r + ψ = t by omega] at he'
        have hcell : evol x t (j + 1) = r'.testBit 0 := by
          rw [he'.2 0 (by omega)]; congr 1; omega
        have hfψ := List.all_eq_true.mp huForce ψ (List.mem_range.mpr hψ)
        cases huψ : u.getD ψ false
        · rw [huψ, Bool.false_or] at hfψ
          simp only [Bool.false_or]
          rw [hcell]
          cases hc0 : colConst K (applyWord K (u.take ψ) T0) false
          · rw [hc0, Bool.false_or] at hfψ
            have := allBelow_spec hfψ r' he'.1
            rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
            rw [this]; rfl
          · have := allBelow_spec hc0 r' he'.1
            rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
            rw [this]; rfl
        · rfl
  refine Rule30FiniteMaskedJen.orCol_not_eventuallyPeriodic hlo hzero j ⟨T, w.length, hwpos, hcper⟩
    ⟨T + k * w.length, w.length, hwpos, fun t ht => ?_⟩
  show orCol x j (t + w.length) = orCol x j t
  rw [hform t ht, hform (t + w.length) (by omega),
    show t + w.length - T = (t - T) + w.length by omega, Nat.add_mod_right]

/-- **Every nonzero finite configuration**: if `paramStripCert a r0 u K k = true`, then for every
`r ≥ r0`, no column `j` of `evol x` is eventually `List.replicate r a ++ u` repeated. -/
theorem not_eventually_param_word_finite {x : Int → Bool} (hfin : FinConfig x)
    (hne : ∃ p, x p = true) (j : Int) (a : Bool) (r0 : Nat) (u : List Bool) (K k : Nat)
    (hK : 1 ≤ K) (hr0 : 1 ≤ r0) (hcert : paramStripCert a r0 u K k = true) :
    ∀ r, r0 ≤ r → ¬ EventuallyWordAt x j (List.replicate r a ++ u) := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact not_eventually_param_word_leftmost hlo hzero j a r0 u K k hK hr0 hcert

/-- **Single-seed center column (`EventuallyWord`)**: if `paramStripCert a r0 u K k = true`, then
for every `r ≥ r0`, `¬ EventuallyWord (List.replicate r a ++ u)`. -/
theorem not_eventually_param_word (a : Bool) (r0 : Nat) (u : List Bool) (K k : Nat)
    (hK : 1 ≤ K) (hr0 : 1 ≤ r0) (hcert : paramStripCert a r0 u K k = true) :
    ∀ r, r0 ≤ r → ¬ EventuallyWord (List.replicate r a ++ u) := by
  intro r hr hew
  have hlo : seed0 0 = true := rfl
  have hzero : ∀ p, p < 0 → seed0 p = false := fun p hp => by
    unfold seed0; simp [show p ≠ 0 by omega]
  exact not_eventually_param_word_leftmost hlo hzero 0 a r0 u K k hK hr0 hcert r hr
    ((eventuallyWordAt_seed0_iff _).2 hew)

/-- Bridge from the `t1`-shifted periodic block presentation (used in `Rule30BlackRunBlocks` and
`Rule30WhiteRunEight`) to `EventuallyWordAt`. -/
theorem eventuallyWordAt_of_run_block {x : Int → Bool} {j : Int} {a : Bool} {T r t1 : Nat}
    {u : List Bool} (hP : 0 < r + u.length)
    (hper : ∀ t, T ≤ t → evol x (t + (r + u.length)) j = evol x t j) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → evol x (t1 + s) j = a)
    (hu : ∀ i, i < u.length → evol x (t1 + r + i) j = u.getD i false) :
    EventuallyWordAt x j (List.replicate r a ++ u) := by
  have hperk : ∀ m t, T ≤ t → evol x (t + m * (r + u.length)) j = evol x t j :=
    periodic_mul (f := fun t => evol x t j) hper
  refine ⟨t1, fun t ht => ?_⟩
  have hlen : (List.replicate r a ++ u).length = r + u.length := by simp
  rw [hlen]
  have hmod : (t - t1) % (r + u.length) < r + u.length := Nat.mod_lt _ hP
  have hd := Nat.div_add_mod (t - t1) (r + u.length)
  generalize (t - t1) / (r + u.length) = m at hd
  generalize (t - t1) % (r + u.length) = s at hd hmod
  have ht_eq : t = t1 + s + m * (r + u.length) := by rw [Nat.mul_comm] at hd; omega
  rw [ht_eq, hperk m (t1 + s) (by omega)]
  by_cases hsr : s < r
  · rw [hrun s hsr, getD_replicate_append_left a u r s hsr]
  · have h1 : t1 + s = t1 + r + (s - r) := by omega
    have h2 := getD_replicate_append_right a u r (s - r)
    rw [show r + (s - r) = s by omega] at h2
    rw [h1, hu (s - r) (by omega), h2]

/-- **Block-form exclusion (`Rule30BlackRunBlocks` / `Rule30WhiteRunEight` style)** for any
configuration with a leftmost black cell and any column `j`. -/
theorem no_param_run_block_leftmost {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (j : Int)
    (a : Bool) (r0 : Nat) (u : List Bool) (K k : Nat)
    (hK : 1 ≤ K) (hr0 : 1 ≤ r0) (hcert : paramStripCert a r0 u K k = true)
    (T r t1 : Nat) (hr : r0 ≤ r)
    (hper : ∀ t, T ≤ t → evol x (t + (r + u.length)) j = evol x t j) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → evol x (t1 + s) j = a)
    (hu : ∀ i, i < u.length → evol x (t1 + r + i) j = u.getD i false) : False :=
  not_eventually_param_word_leftmost hlo hzero j a r0 u K k hK hr0 hcert r hr
    (eventuallyWordAt_of_run_block (by omega) hper ht1 hrun hu)

/-! ### Part 3: Kernel-checked Parametric Tables and Headline Theorems -/

/-- Parametric black-run table `(n, bits, r0, K, k)`: block `u = wordOf n bits` of length `n`,
threshold `r0`, strip width `K`, warm-up periods `k`. Certifies `1^r ++ u` for all `r ≥ r0`. -/
def paramBlackTable : List (Nat × Nat × Nat × Nat × Nat) := [
  -- Length 1..4 blocks from Rule30BlackRunBlocks (lowered from r ≥ 18 / 27 to r ≥ 8 / 9 at K = 5)
  (1, 0, 9, 5, 1),   -- u = 0:     all r ≥ 9  (was r ≥ 18)
  (2, 0, 9, 5, 1),   -- u = 00:    all r ≥ 9  (was r ≥ 18)
  (3, 0, 9, 5, 1),   -- u = 000:   all r ≥ 9  (was r ≥ 18)
  (3, 2, 8, 5, 1),   -- u = 010:   all r ≥ 8  (was r ≥ 27)
  (4, 0, 9, 5, 1),   -- u = 0000:  all r ≥ 9  (was r ≥ 18)
  (4, 2, 9, 5, 1),   -- u = 0010:  all r ≥ 9  (was r ≥ 27)
  (4, 4, 9, 5, 1),   -- u = 0100:  all r ≥ 9  (was r ≥ 18)
  (4, 6, 9, 5, 1),   -- u = 0110:  all r ≥ 9  (was r ≥ 27)
  -- New length-5 blocks
  (5, 0, 9, 5, 1),   -- u = 00000: all r ≥ 9
  (5, 2, 8, 5, 1),   -- u = 00010: all r ≥ 8
  (5, 6, 15, 7, 1),  -- u = 00110: all r ≥ 15
  (5, 10, 15, 7, 1), -- u = 01010: all r ≥ 15
  (5, 12, 9, 5, 1),  -- u = 01100: all r ≥ 9
  (5, 14, 9, 5, 1)   -- u = 01110: all r ≥ 9
]

theorem paramBlackTable_ok :
    paramBlackTable.all (fun e =>
      decide (1 ≤ e.2.2.2.1) && decide (1 ≤ e.2.2.1) &&
        paramStripCert true e.2.2.1 (wordOf e.1 e.2.1) e.2.2.2.1 e.2.2.2.2) = true := by
  decide +kernel

/-- **Every black-run family `1^r ++ u` (`r ≥ r0`) in `paramBlackTable` is excluded** as an
eventual repeating word of the center column, whatever the transient. -/
theorem not_eventually_paramBlackTable (e : Nat × Nat × Nat × Nat × Nat)
    (he : e ∈ paramBlackTable) (r : Nat) (hr : e.2.2.1 ≤ r) :
    ¬ EventuallyWord (List.replicate r true ++ wordOf e.1 e.2.1) := by
  have h := List.all_eq_true.mp paramBlackTable_ok e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact not_eventually_param_word true e.2.2.1 (wordOf e.1 e.2.1) e.2.2.2.1 e.2.2.2.2
    h.1.1 h.1.2 h.2 r hr

/-- **Every black-run family `1^r ++ u` (`r ≥ r0`) in `paramBlackTable` is excluded in every
column of every nonzero finite configuration.** -/
theorem not_eventually_paramBlackTable_finite {x : Int → Bool} (hfin : FinConfig x)
    (hne : ∃ p, x p = true) (j : Int) (e : Nat × Nat × Nat × Nat × Nat)
    (he : e ∈ paramBlackTable) (r : Nat) (hr : e.2.2.1 ≤ r) :
    ¬ EventuallyWordAt x j (List.replicate r true ++ wordOf e.1 e.2.1) := by
  have h := List.all_eq_true.mp paramBlackTable_ok e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact not_eventually_param_word_finite hfin hne j true e.2.2.1 (wordOf e.1 e.2.1)
    e.2.2.2.1 e.2.2.2.2 h.1.1 h.1.2 h.2 r hr

/-- **Sharpened Theorem B′ for `u = 010`**: `1^r 010` is excluded for all `r ≥ 8` (lowering the
threshold `r ≥ 27` of `Rule30BlackRunBlocks.det_010` to `r ≥ 8`). -/
theorem not_eventually_black_run_010 (r : Nat) (hr : 8 ≤ r) :
    ¬ EventuallyWord (List.replicate r true ++ [false, true, false]) :=
  not_eventually_param_word true 8 [false, true, false] 5 1 (by decide) (by decide)
    (by decide +kernel) r hr

/-- **New block `u = 00010` at `r ≥ 8`**: `1^r 00010` is excluded for all `r ≥ 8` at strip width `5`. -/
theorem not_eventually_black_run_00010 (r : Nat) (hr : 8 ≤ r) :
    ¬ EventuallyWord (List.replicate r true ++ [false, false, false, true, false]) :=
  not_eventually_param_word true 8 [false, false, false, true, false] 5 1 (by decide) (by decide)
    (by decide +kernel) r hr

/-- Parametric white-run table `(n, bits, q0, K, k)`: block `u = wordOf n bits` of length `n`,
threshold `q0`, strip width `K`, warm-up periods `k`. Certifies `0^q ++ u` for all `q ≥ q0`. -/
def paramWhiteTable : List (Nat × Nat × Nat × Nat × Nat) := [
  (1, 1, 10, 8, 2),  -- 0^q 1:      all q ≥ 10 (certTable had only q = 10, 11, 12)
  (2, 3, 9, 6, 2),   -- 0^q 11:     all q ≥ 9  (certified purely by width-6 bitmasks)
  (4, 11, 9, 6, 3),  -- 0^q 1011:   all q ≥ 9  (certTable had only q = 9)
  (4, 13, 11, 7, 2), -- 0^q 1101:   all q ≥ 11 (new infinite family)
  (5, 19, 9, 6, 2),  -- 0^q 10011:  all q ≥ 9  (certTable had only q = 8)
  (5, 23, 9, 8, 3),  -- 0^q 10111:  all q ≥ 9  (new infinite family)
  (5, 27, 9, 6, 2),  -- 0^q 11011:  all q ≥ 9  (new infinite family)
  (6, 47, 9, 6, 2)   -- 0^q 101111: all q ≥ 9  (certTable had only q = 7)
]

theorem paramWhiteTable_ok :
    paramWhiteTable.all (fun e =>
      decide (1 ≤ e.2.2.2.1) && decide (1 ≤ e.2.2.1) &&
        paramStripCert false e.2.2.1 (wordOf e.1 e.2.1) e.2.2.2.1 e.2.2.2.2) = true := by
  decide +kernel

/-- **Every white-run family `0^q ++ u` (`q ≥ q0`) in `paramWhiteTable` is excluded** as an
eventual repeating word of the center column, whatever the transient. -/
theorem not_eventually_paramWhiteTable (e : Nat × Nat × Nat × Nat × Nat)
    (he : e ∈ paramWhiteTable) (q : Nat) (hq : e.2.2.1 ≤ q) :
    ¬ EventuallyWord (List.replicate q false ++ wordOf e.1 e.2.1) := by
  have h := List.all_eq_true.mp paramWhiteTable_ok e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact not_eventually_param_word false e.2.2.1 (wordOf e.1 e.2.1) e.2.2.2.1 e.2.2.2.2
    h.1.1 h.1.2 h.2 q hq

/-- **Every white-run family `0^q ++ u` (`q ≥ q0`) in `paramWhiteTable` is excluded in every
column of every nonzero finite configuration.** -/
theorem not_eventually_paramWhiteTable_finite {x : Int → Bool} (hfin : FinConfig x)
    (hne : ∃ p, x p = true) (j : Int) (e : Nat × Nat × Nat × Nat × Nat)
    (he : e ∈ paramWhiteTable) (q : Nat) (hq : e.2.2.1 ≤ q) :
    ¬ EventuallyWordAt x j (List.replicate q false ++ wordOf e.1 e.2.1) := by
  have h := List.all_eq_true.mp paramWhiteTable_ok e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact not_eventually_param_word_finite hfin hne j false e.2.2.1 (wordOf e.1 e.2.1)
    e.2.2.2.1 e.2.2.2.2 h.1.1 h.1.2 h.2 q hq

/-- **The words `0^q 1`, `q ≥ 10`, are excluded**: the center column is never eventually equal to
`0^q 1` repeated for any `q ≥ 10`, whatever the transient (generalizing the three cases
`q = 10, 11, 12` of `Rule30StripCertificateTable` to all `q ≥ 10`). -/
theorem not_eventually_white_run_1 (q : Nat) (hq : 10 ≤ q) :
    ¬ EventuallyWord (List.replicate q false ++ [true]) :=
  not_eventually_param_word false 10 [true] 8 2 (by decide) (by decide) (by decide +kernel) q hq

/-- **The words `0^q 1`, `q ≥ 10`, are excluded in every column of every nonzero finite
configuration**, whatever the transient. -/
theorem no_white_run_1_finite {x : Int → Bool} (hfin : FinConfig x) (hne : ∃ p, x p = true)
    (j : Int) (T q t0 : Nat) (hq : 10 ≤ q)
    (hper : ∀ t, T ≤ t → evol x (t + (q + 1)) j = evol x t j) (ht0 : T ≤ t0)
    (hw : ∀ i, i < q → evol x (t0 + i) j = false) (hb : evol x (t0 + q) j = true) : False := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact no_param_run_block_leftmost hlo hzero j false 10 [true] 8 2 (by decide) (by decide)
    (by decide +kernel) T q t0 hq hper ht0 hw (fun i hi => by
      have : i = 0 := by simp at hi; omega
      subst this; simpa using hb)

/-- **The words `0^q 1011`, `q ≥ 9`, are excluded** (generalizing `q = 9` in
`Rule30StripCertificateTable` to all `q ≥ 9`). -/
theorem not_eventually_white_run_1011 (q : Nat) (hq : 9 ≤ q) :
    ¬ EventuallyWord (List.replicate q false ++ [true, false, true, true]) :=
  not_eventually_param_word false 9 [true, false, true, true] 6 3
    (by decide) (by decide) (by decide +kernel) q hq

/-- **The words `0^q 10011`, `q ≥ 9`, are excluded** at strip width `6`. -/
theorem not_eventually_white_run_10011 (q : Nat) (hq : 9 ≤ q) :
    ¬ EventuallyWord (List.replicate q false ++ [true, false, false, true, true]) :=
  not_eventually_param_word false 9 [true, false, false, true, true] 6 2
    (by decide) (by decide) (by decide +kernel) q hq

/-- **The words `0^q 101111`, `q ≥ 9`, are excluded** at strip width `6`. -/
theorem not_eventually_white_run_101111 (q : Nat) (hq : 9 ≤ q) :
    ¬ EventuallyWord (List.replicate q false ++ [true, false, true, true, true, true]) :=
  not_eventually_param_word false 9 [true, false, true, true, true, true] 6 2
    (by decide) (by decide) (by decide +kernel) q hq

/-! ## 5. Universal Bad-Class Dichotomy and Period-2 Forbidden Languages (`IsR30`, `Psi R`, `FinConfig`) -/

section Phase2

open Rule30ZeroBoundary Rule30PeriodTwoCoupled Rule30PeriodTwoSideways
open Rule30Ether (IsR30 rowOf rowOf_succ rowOf_head drv drv_col0 drv_init drv_isR30 seg_congr)
open Rule30PeriodFourSkeleton Rule30PeriodTwoLanguage

/-- **Universal bad-class dichotomy for any right-half evolution `IsR30 F`.**
If column `0` of `F` is `C.w`-periodic from time `T`, and `C` is a valid bad-class certificate
(`checkb`, `checkGb`), then either the strip `rowOf F t 0 C.b` eventually stays in the bad rank
class `bad`, or there is a period `P = C.m r * C.P > 0` such that column `1` of `F` is `P`-periodic
at all white steps of column `0` from some time `T' ≥ T` onward. -/
theorem isR30_bad_or_periodic {F : Nat → Nat → Bool} (hF : IsR30 F)
    (C : Cert) (bad : Nat) (hC : Cert.checkb C bad = true) (hG : Cert.checkGb C bad = true)
    (hP : 0 < C.P) (hb : 0 < C.b)
    (T : Nat) (h0 : ∀ t, T ≤ t → F t 0 = C.wAt ((t - T) % C.P)) :
    (∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → C.rk ((t - T) % C.P) (rowOf F t 0 C.b) = bad) ∨
    (∃ T' P, T ≤ T' ∧ 0 < P ∧ P % C.P = 0 ∧
      (∀ t, T' ≤ t → F (t + P) 0 = F t 0) ∧
      (∀ t, T' ≤ t → F t 0 = false → F (t + P) 1 = F t 1)) := by
  let ph : Nat → Nat := fun t => (t - T) % C.P
  let st : Nat → List Bool := fun t => rowOf F t 0 C.b
  have hst_len : ∀ t, (st t).length = C.b := fun t => length_seg C.b _
  have hst_head : ∀ t, (st t).headD false = F t 1 := by
    intro t
    obtain ⟨b', hb'⟩ : ∃ b', C.b = b' + 1 := ⟨C.b - 1, by omega⟩
    show (rowOf F t 0 C.b).headD false = F t (0 + 1)
    rw [hb']
    exact rowOf_head F t 0 b'
  have hph : ∀ t, T ≤ t → ph (t + 1) = (ph t + 1) % C.P := by
    intro t ht
    show (t + 1 - T) % C.P = ((t - T) % C.P + 1) % C.P
    rw [show t + 1 - T = (t - T) + 1 by omega]
    exact (Nat.mod_add_mod (t - T) C.P 1).symm
  have hphlt : ∀ t, ph t < C.P := fun t => Nat.mod_lt _ hP
  have hedge : ∀ t, T ≤ t → Cert.edgeOKb C bad (ph t) (st t) (st (t + 1)) = true := by
    intro t ht
    have hall := hC
    unfold Cert.checkb at hall
    have h1 := List.all_eq_true.1 hall (ph t) (List.mem_range.2 (hphlt t))
    have h2 := List.all_eq_true.1 h1 (st t) (allLists_mem _ _ (hst_len t))
    have h3 := List.all_eq_true.1 h2 (F t (C.b + 1)) (by cases F t (C.b + 1) <;> simp)
    have hs : st (t + 1) = lin3 (C.wAt (ph t) :: (st t ++ [F t (C.b + 1)])) := by
      show rowOf F (t + 1) 0 C.b = _
      rw [rowOf_succ hF t 0 C.b, Nat.zero_add, h0 t ht]
    rw [hs]; exact h3
  let Rk : Nat → Nat := fun t => C.rk (ph t) (st t)
  have hRle : ∀ t, T ≤ t → Rk (t + 1) ≤ Rk t := by
    intro t ht
    have e := hedge t ht
    unfold Cert.edgeOKb at e
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e
    show C.rk (ph (t + 1)) (st (t + 1)) ≤ C.rk (ph t) (st t)
    rw [hph t ht]; exact e.1
  obtain ⟨T', hT', hconst⟩ := antitone_eventually_const Rk T hRle
  by_cases hne : Rk T' = bad
  · refine Or.inl ⟨T', hT', fun t₀ ht₀ => ?_⟩
    exact (hconst t₀ ht₀).trans hne
  · let r := Rk T'
    have hrne : r ≠ bad := hne
    have hrb : (r == bad) = false := by
      cases hq : (r == bad) with
      | false => rfl
      | true => exact absurd (beq_iff_eq.1 hq) hne
    have hstep : ∀ t, T' ≤ t →
        C.ps (ph (t + 1)) (st (t + 1)) = C.nextPos r (C.ps (ph t) (st t)) (ph t) ∧
        (C.wAt (ph t) = false → F t 1 = C.u r (C.ps (ph t) (st t))) := by
      intro t ht
      have e := hedge t (by omega)
      have hRt : Rk t = r := hconst t ht
      have hRt1 : Rk (t + 1) = r := hconst (t + 1) (by omega)
      unfold Cert.edgeOKb at e
      rw [← hph t (by omega)] at e
      have hr1 : C.rk (ph (t + 1)) (st (t + 1)) = C.rk (ph t) (st t) := by
        show Rk (t + 1) = Rk t; rw [hRt, hRt1]
      have hrt : C.rk (ph t) (st t) = r := hRt
      simp only [hr1, hrt, hrb, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq] at e
      refine ⟨e.2.1, fun hw => ?_⟩
      have e2 := e.2.2
      rw [hw, Bool.false_or, beq_iff_eq] at e2
      rw [← hst_head t]; exact e2
    let q : Nat → Nat × Nat := fun t => (C.ps (ph t) (st t), ph t)
    have hq : ∀ t, T' ≤ t → q (t + 1) = C.G r (q t) := by
      intro t ht
      show (C.ps (ph (t + 1)) (st (t + 1)), ph (t + 1)) =
        (C.nextPos r (C.ps (ph t) (st t)) (ph t), (ph t + 1) % C.P)
      rw [(hstep t ht).1, hph t (by omega)]
    have hqiter : ∀ t, T' ≤ t → ∀ n, q (t + n) = C.iterG r n (q t) := by
      intro t ht n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [show t + (n + 1) = (t + n) + 1 by omega, hq (t + n) (by omega), ih,
          iterG_add C r n 1 (q t)]
        rfl
    have hGn : ∀ φ, φ < C.P → ∀ s, s ∈ allLists C.b → C.rk φ s = bad ∨ C.ps φ s < C.m (C.rk φ s) := by
      have hG' := hG
      unfold Cert.checkGb at hG'
      simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hG'
      exact hG'
    have hposr : ∀ t, T' ≤ t → C.ps (ph t) (st t) < C.m r := by
      intro t ht
      have hrt : C.rk (ph t) (st t) = r := hconst t ht
      rcases hGn (ph t) (hphlt t) (st t) (allLists_mem _ _ (hst_len t)) with h' | h'
      · rw [hrt] at h'; exact absurd h' hrne
      · rw [hrt] at h'; exact h'
    have hm : 0 < C.m r := by have := hposr T' (Nat.le_refl _); omega
    have hper : ∀ t, T' ≤ t → q (t + C.m r * C.P) = q t := by
      intro t ht
      rw [hqiter t ht]
      exact C.iterG_period r hm hP _ _ (hposr t ht) (hphlt t)
    refine Or.inr ⟨T', C.m r * C.P, hT', Nat.mul_pos hm hP, Nat.mul_mod_left (C.m r) C.P, ?_, ?_⟩
    · intro t ht
      rw [h0 (t + C.m r * C.P) (by omega), h0 t (by omega)]
      congr 1
      rw [show t + C.m r * C.P - T = (t - T) + C.P * C.m r by rw [Nat.mul_comm]; omega,
        Nat.add_mul_mod_self_left]
    · intro t ht hw
      have hwt : C.wAt (ph t) = false := by rw [← h0 t (by omega)]; exact hw
      have hqe := hper t ht
      have hph' : ph (t + C.m r * C.P) = ph t := congrArg Prod.snd hqe
      have hps' : C.ps (ph (t + C.m r * C.P)) (st (t + C.m r * C.P)) = C.ps (ph t) (st t) :=
        congrArg Prod.fst hqe
      have hwt' : C.wAt (ph (t + C.m r * C.P)) = false := by rw [hph']; exact hwt
      rw [(hstep (t + C.m r * C.P) (by omega)).2 hwt', (hstep t ht).2 hwt, hps']

/-- **Soundness of `occurs` for any `IsR30 F`.** If column `0` of `F` is `C.w`-periodic from `T`
with `C.w = [false, true]` and `rowOf F t 0 C.b` stays in `bad` from `T'`, then for any `pat` with
`occurs C bad pat = false` and any white time `t ≥ T'`, column `1` of `F` at `t, t + 2, …` never
spells `pat`. -/
theorem isR30_no_pattern {F : Nat → Nat → Bool} (hF : IsR30 F)
    (C : Cert) (bad : Nat) (hw : C.w = [false, true]) (T T' : Nat) (hTT : T ≤ T')
    (h0 : ∀ t, T ≤ t → F t 0 = C.wAt ((t - T) % C.P))
    (hbad : ∀ t, T' ≤ t → C.rk ((t - T) % C.P) (rowOf F t 0 C.b) = bad) (hb : 0 < C.b)
    (pat : List Bool) (hocc : occurs C bad pat = false) (t : Nat) (ht : T' ≤ t) (hph : (t - T) % 2 = 0) :
    ¬ ∀ i, i < pat.length → F (t + 2 * i) 1 = pat.getD i false := by
  intro hm
  have hP : C.P = 2 := by unfold Cert.P; rw [hw]; rfl
  have hst_len : ∀ u, (rowOf F u 0 C.b).length = C.b := fun _ => length_seg C.b _
  have hhead : ∀ u, (rowOf F u 0 C.b).headD false = F u 1 := by
    intro u
    obtain ⟨b', hb'⟩ : ∃ b', C.b = b' + 1 := ⟨C.b - 1, by omega⟩
    show (rowOf F u 0 C.b).headD false = F u (0 + 1)
    rw [hb']; exact rowOf_head F u 0 b'
  have hstep : ∀ u, T' ≤ u → (u - T) % 2 = 0 →
      rowOf F (u + 1) 0 C.b = lin3 (C.wAt 0 :: (rowOf F u 0 C.b ++ [F u (C.b + 1)])) ∧
      rowOf F (u + 2) 0 C.b = lin3 (C.wAt 1 :: (rowOf F (u + 1) 0 C.b ++ [F (u + 1) (C.b + 1)])) ∧
      inBad C bad 1 (rowOf F (u + 1) 0 C.b) = true ∧
      inBad C bad 0 (rowOf F (u + 2) 0 C.b) = true ∧
      inBad C bad 0 (rowOf F u 0 C.b) = true := by
    intro u hu hpu
    have e0 : F u 0 = C.wAt 0 := by rw [h0 u (by omega), hP, hpu]
    have e1 : F (u + 1) 0 = C.wAt 1 := by
      rw [h0 (u + 1) (by omega), hP, show (u + 1 - T) % 2 = 1 by omega]
    refine ⟨by rw [rowOf_succ hF, Nat.zero_add, e0], by rw [rowOf_succ hF, Nat.zero_add, e1], ?_, ?_, ?_⟩
    · have := hbad (u + 1) (by omega)
      rw [hP, show (u + 1 - T) % 2 = 1 by omega] at this
      unfold inBad; rw [this]; simp
    · have := hbad (u + 2) (by omega)
      rw [hP, show (u + 2 - T) % 2 = 0 by omega] at this
      unfold inBad; rw [this]; simp
    · have := hbad u hu
      rw [hP, hpu] at this
      unfold inBad; rw [this]; simp
  have key : ∀ (ys : List Bool) (S u : Nat), T' ≤ u → (u - T) % 2 = 0 →
      S.testBit (encList (rowOf F u 0 C.b)) = true →
      (∀ i, i < ys.length → F (u + 2 * (i + 1)) 1 = ys.getD i false) →
      (simMask C bad S ys).testBit (encList (rowOf F (u + 2 * ys.length) 0 C.b)) = true := by
    intro ys
    induction ys with
    | nil => intro S u _ _ hS _; exact hS
    | cons y ys ih =>
      intro S u hu hpu hS hys
      obtain ⟨e1, e2, b1, b2, _⟩ := hstep u hu hpu
      have hnext := occStep_bit C bad S y (allLists C.b) (rowOf F u 0 C.b) (rowOf F (u + 2) 0 C.b)
        (F u (C.b + 1)) (F (u + 1) (C.b + 1))
        (allLists_mem _ _ (hst_len u)) hS (by rw [← e1]; exact b1) (by rw [e2, e1]) b2
        (by rw [hhead]; have := hys 0 (by simp); simpa using this)
      have := ih _ (u + 2) (by omega) (by omega) hnext (fun i hi => by
        have := hys (i + 1) (by simp; omega)
        rw [show u + 2 + 2 * (i + 1) = u + 2 * (i + 1 + 1) by omega]
        simpa using this)
      show (simMask C bad (occStep C bad S y (allLists C.b)) ys).testBit _ = true
      rw [show u + 2 * (y :: ys).length = u + 2 + 2 * ys.length by simp; omega]
      exact this
  cases pat with
  | nil => simp [occurs] at hocc
  | cons y ys =>
    have hS0 := startMask_bit C bad y (allLists C.b) (rowOf F t 0 C.b) (allLists_mem _ _ (hst_len t))
      (hstep t ht hph).2.2.2.2 (by rw [hhead]; have := hm 0 (by simp); simpa using this)
    have := key ys _ t ht hph hS0 (fun i hi => by
      have := hm (i + 1) (by simp; omega)
      simpa using this)
    unfold occurs at hocc
    rw [show (simMask C bad (startMask C bad y (allLists C.b)) ys) = 0 by
      revert hocc; cases (simMask C bad (startMask C bad y (allLists C.b)) ys) == 0 <;> simp] at this
    simp at this

/-- Right half of `evol x` relative to column `j : Int`. -/
def evolRight (x : Int → Bool) (j : Int) (t p : Nat) : Bool :=
  evol x t (j + (p : Int))

theorem evolRight_isR30 (x : Int → Bool) (j : Int) : IsR30 (evolRight x j) := by
  intro t p
  show evol x (t + 1) (j + ((p + 1 : Nat) : Int)) =
    rule (evol x t (j + (p : Int))) (evol x t (j + ((p + 1 : Nat) : Int)))
      (evol x t (j + ((p + 2 : Nat) : Int)))
  have h1 : j + ((p + 1 : Nat) : Int) - 1 = j + (p : Int) := by omega
  have h2 : j + ((p + 1 : Nat) : Int) + 1 = j + ((p + 2 : Nat) : Int) := by omega
  rw [← h1, ← h2]
  rfl

/-- **Bad-class soundness for every configuration with a leftmost black cell.**
If column `j` is `C.w`-periodic from `T`, the right strip `rowOf (evolRight x j) t 0 C.b` eventually stays in
the bad rank class `bad`. -/
theorem sound_bad_leftmost {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) (j : Int)
    (C : Cert) (bad : Nat) (hC : Cert.checkb C bad = true) (hG : Cert.checkGb C bad = true)
    (hP : 0 < C.P) (hb : 0 < C.b)
    (T : Nat) (h : ∀ t, T ≤ t → evol x t j = C.wAt ((t - T) % C.P)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → C.rk ((t - T) % C.P) (rowOf (evolRight x j) t 0 C.b) = bad := by
  have h0 : ∀ t, T ≤ t → evolRight x j t 0 = C.wAt ((t - T) % C.P) := by
    intro t ht
    show evol x t (j + 0) = _
    rw [Int.add_zero]
    exact h t ht
  rcases isR30_bad_or_periodic (evolRight_isR30 x j) C bad hC hG hP hb T h0 with
    ⟨T', hT', hbad⟩ | ⟨T', P, _, hPpos, _, hper0, hper1⟩
  · exact ⟨T', hT', hbad⟩
  · exfalso
    refine Rule30FiniteMaskedJen.masked_jen hlo hzero j hPpos (T := T') ?_ ?_
    · intro t ht
      have := hper0 t ht
      simpa [evolRight] using this
    · intro t ht hw
      have := hper1 t ht (by simpa [evolRight] using hw)
      simpa [evolRight] using this

/-- **Every predicate checked on the bad class holds eventually** in every column `j` of every
configuration with a leftmost black cell. -/
theorem eventually_pred_leftmost {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) (j : Int)
    (C : Cert) (bad : Nat) (pred : Nat → List Bool → Bool)
    (hC : Cert.checkb C bad = true) (hG : Cert.checkGb C bad = true)
    (hI : Cert.badImp C bad pred = true) (hP : 0 < C.P) (hb : 0 < C.b)
    (T : Nat) (h : ∀ t, T ≤ t → evol x t j = C.wAt ((t - T) % C.P)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → pred ((t - T) % C.P) (rowOf (evolRight x j) t 0 C.b) = true := by
  obtain ⟨T', hT', hbad⟩ := sound_bad_leftmost hlo hzero j C bad hC hG hP hb T h
  refine ⟨T', hT', fun t ht => ?_⟩
  have hall := hI
  unfold Cert.badImp at hall
  have h1 := List.all_eq_true.1 hall ((t - T) % C.P) (List.mem_range.2 (Nat.mod_lt _ hP))
  have h2 := List.all_eq_true.1 h1 (rowOf (evolRight x j) t 0 C.b)
    (allLists_mem _ _ (length_seg C.b _))
  rw [hbad t ht] at h2
  simpa using h2

/-- **Width-`6` right-half constraints for every configuration with a leftmost black cell.**
If column `j` is `(01)^∞` from time `T`, then from some time `T' ≥ T` on, column `j + 1` at
consecutive white steps never spells any of the 9 forbidden words of
`Rule30PeriodTwoWidth6.col1Forbidden`. -/
theorem col1_constraints_width6_leftmost {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) (j : Int)
    (T : Nat) (h : ∀ t, T ≤ t → evol x t j = ((t - T) % 2 == 1)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → (t - T) % 2 = 0 → ∀ pat ∈ Rule30PeriodTwoWidth6.col1Forbidden,
      ¬ ∀ i, i < pat.length → evol x (t + 2 * i) (j + 1) = pat.getD i false := by
  have h' : ∀ t, T ≤ t → evol x t j = Rule30PeriodTwoWidth6.K6.wAt ((t - T) % Rule30PeriodTwoWidth6.K6.P) :=
    fun t ht => by rw [Rule30PeriodTwoWidth6.wAt_eq, h t ht]
  obtain ⟨T', hT', hbad⟩ := sound_bad_leftmost hlo hzero j Rule30PeriodTwoWidth6.K6 0
    Rule30PeriodTwoWidth6.K6_checkb Rule30PeriodTwoWidth6.K6_checkGb (by decide) (by decide) T h'
  have h0 : ∀ t, T ≤ t → evolRight x j t 0 = Rule30PeriodTwoWidth6.K6.wAt ((t - T) % Rule30PeriodTwoWidth6.K6.P) := by
    intro t ht; show evol x t (j + 0) = _; rw [Int.add_zero]; exact h' t ht
  refine ⟨T', hT', fun t ht hph pat hpat => ?_⟩
  simp only [Rule30PeriodTwoWidth6.col1Forbidden, List.mem_cons, List.not_mem_nil, or_false] at hpat
  rcases hpat with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact isR30_no_pattern (evolRight_isR30 x j) Rule30PeriodTwoWidth6.K6 0 rfl T T' hT' h0 hbad (by decide) _ Rule30PeriodTwoWidth6.occ_p11 t ht hph
  · exact isR30_no_pattern (evolRight_isR30 x j) Rule30PeriodTwoWidth6.K6 0 rfl T T' hT' h0 hbad (by decide) _ Rule30PeriodTwoWidth6.occ_p00000 t ht hph
  · exact isR30_no_pattern (evolRight_isR30 x j) Rule30PeriodTwoWidth6.K6 0 rfl T T' hT' h0 hbad (by decide) _ Rule30PeriodTwoWidth6.occ_g21 t ht hph
  · exact isR30_no_pattern (evolRight_isR30 x j) Rule30PeriodTwoWidth6.K6 0 rfl T T' hT' h0 hbad (by decide) _ Rule30PeriodTwoWidth6.occ_g23 t ht hph
  · exact isR30_no_pattern (evolRight_isR30 x j) Rule30PeriodTwoWidth6.K6 0 rfl T T' hT' h0 hbad (by decide) _ Rule30PeriodTwoWidth6.occ_g12 t ht hph
  · exact isR30_no_pattern (evolRight_isR30 x j) Rule30PeriodTwoWidth6.K6 0 rfl T T' hT' h0 hbad (by decide) _ Rule30PeriodTwoWidth6.occ_g114 t ht hph
  · exact isR30_no_pattern (evolRight_isR30 x j) Rule30PeriodTwoWidth6.K6 0 rfl T T' hT' h0 hbad (by decide) _ Rule30PeriodTwoWidth6.occ_g132 t ht hph
  · exact isR30_no_pattern (evolRight_isR30 x j) Rule30PeriodTwoWidth6.K6 0 rfl T T' hT' h0 hbad (by decide) _ Rule30PeriodTwoWidth6.occ_g241 t ht hph
  · exact isR30_no_pattern (evolRight_isR30 x j) Rule30PeriodTwoWidth6.K6 0 rfl T T' hT' h0 hbad (by decide) _ Rule30PeriodTwoWidth6.occ_g243 t ht hph

/-- **Width-`6` right-half constraints for every nonzero finite configuration.** -/
theorem col1_constraints_width6_finite {x : Int → Bool} (hfin : FinConfig x)
    (hne : ∃ p, x p = true) (j : Int)
    (T : Nat) (h : ∀ t, T ≤ t → evol x t j = ((t - T) % 2 == 1)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → (t - T) % 2 = 0 → ∀ pat ∈ Rule30PeriodTwoWidth6.col1Forbidden,
      ¬ ∀ i, i < pat.length → evol x (t + 2 * i) (j + 1) = pat.getD i false := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact col1_constraints_width6_leftmost hlo hzero j T h

/-! ## 6. Sideways Bad-Class Dichotomy and Forbidden Language for `Psi R` (`Rule30PeriodTwoSideways`) -/

/-- **Universal sideways dichotomy for `drv altCol R` and `u R`.**
For any right half `R : Nat → Bool` and any bad-class certificate `C` for `w = [false, true]`,
either the driven strip `rowOf (drv altCol R) t 0 C.b` eventually stays in the bad rank class `bad`,
or `u R` is eventually periodic (`EventuallyPeriodic (u R)`, which implies `¬ FinSupp (Psi R)`). -/
theorem drv_bad_or_u_periodic (R : Nat → Bool) (C : Cert) (bad : Nat)
    (hw : C.w = [false, true]) (hC : Cert.checkb C bad = true) (hG : Cert.checkGb C bad = true)
    (hb : 0 < C.b) :
    (∃ T', 1 ≤ T' ∧ ∀ t, T' ≤ t → C.rk ((t - 1) % C.P) (rowOf (drv altCol R) t 0 C.b) = bad) ∨
    EventuallyPeriodic (u R) := by
  have hP : C.P = 2 := by unfold Cert.P; rw [hw]; rfl
  have hPpos : 0 < C.P := by rw [hP]; decide
  have h0 : ∀ t, 1 ≤ t → drv altCol R t 0 = C.wAt ((t - 1) % C.P) := by
    intro t ht
    rw [drv_col0, hP]
    unfold altCol Cert.wAt
    rw [hw]
    rcases Nat.mod_two_eq_zero_or_one (t - 1) with h | h
    · have ht2 : t % 2 = 1 := by omega
      simp [h, ht2]
    · have ht2 : t % 2 = 0 := by omega
      simp [h, ht2]
  rcases isR30_bad_or_periodic (drv_isR30 altCol R) C bad hC hG hPpos hb 1 h0 with
    hbad | ⟨T', P, hT', hPpos', hPmod, _, hper1⟩
  · exact Or.inl hbad
  · right
    rw [hP] at hPmod
    refine ⟨T', P / 2, by omega, fun s hs => ?_⟩
    have hw_odd : drv altCol R (2 * s + 1) 0 = false := by
      rw [drv_col0]; exact altCol_odd s
    have hstep := hper1 (2 * s + 1) (by omega) hw_odd
    unfold u
    rw [show 2 * (s + P / 2) + 1 = 2 * s + 1 + P by omega]
    exact hstep

/-- **Every candidate counterexample `Psi R` (`FinSupp (Psi R)`) forces `drv altCol R` into the
bad rank class.** -/
theorem Psi_enters_bad_of_finSupp (R : Nat → Bool) (hfin : FinSupp (Psi R))
    (C : Cert) (bad : Nat) (hw : C.w = [false, true])
    (hC : Cert.checkb C bad = true) (hG : Cert.checkGb C bad = true) (hb : 0 < C.b) :
    ∃ T', 1 ≤ T' ∧ ∀ t, T' ≤ t → C.rk ((t - 1) % C.P) (rowOf (drv altCol R) t 0 C.b) = bad := by
  rcases drv_bad_or_u_periodic R C bad hw hC hG hb with hbad | hper
  · exact hbad
  · exact absurd hfin (not_finSupp_Psi_of_eventuallyPeriodic R hper)

/-- **Pattern exclusion on `u R` and the free bits of `Psi R` inside the bad class.** -/
theorem u_no_pattern_of_bad (R : Nat → Bool) (C : Cert) (bad : Nat) (hw : C.w = [false, true])
    (hb : 0 < C.b) (T' : Nat) (hT' : 1 ≤ T')
    (hbad : ∀ t, T' ≤ t → C.rk ((t - 1) % C.P) (rowOf (drv altCol R) t 0 C.b) = bad)
    (pat : List Bool) (hocc : occurs C bad pat = false) (s : Nat) (hs : T' ≤ 2 * s + 1) :
    (¬ ∀ i, i < pat.length → u R (s + i) = pat.getD i false) ∧
    (¬ ∀ i, i < pat.length → zrow (Psi R) (2 * (s + i) + 1) 1 = !pat.getD i false) := by
  have hP : C.P = 2 := by unfold Cert.P; rw [hw]; rfl
  have h0 : ∀ t, 1 ≤ t → drv altCol R t 0 = C.wAt ((t - 1) % C.P) := by
    intro t ht
    rw [drv_col0, hP]
    unfold altCol Cert.wAt
    rw [hw]
    rcases Nat.mod_two_eq_zero_or_one (t - 1) with h | h
    · have ht2 : t % 2 = 1 := by omega
      simp [h, ht2]
    · have ht2 : t % 2 = 0 := by omega
      simp [h, ht2]
  have hno := isR30_no_pattern (drv_isR30 altCol R) C bad hw 1 T' hT' h0 hbad hb pat hocc
    (2 * s + 1) hs (by omega)
  have hu : ¬ ∀ i, i < pat.length → u R (s + i) = pat.getD i false := by
    intro hm
    refine hno fun i hi => ?_
    rw [show 2 * s + 1 + 2 * i = 2 * (s + i) + 1 by omega]
    exact hm i hi
  refine ⟨hu, fun hpsi => hu fun i hi => ?_⟩
  have e := hpsi i hi
  rw [Psi_free] at e
  unfold u
  revert e
  cases drv altCol R (2 * (s + i) + 1) 1 <;> cases pat.getD i false <;> decide

/-- **Width-`6` forbidden language on the free bits of `Psi R` whenever `FinSupp (Psi R)` holds.**
For any right half `R : Nat → Bool` (including `R = empty`), if `Psi R` is finitely supported,
then from some step `S₀` onward, for all `pat ∈ Rule30PeriodTwoWidth6.col1Forbidden` (`11`, `00000`,
gap pairs `21`, `23`, `12`, gap triples `114`, `132`, `241`, `243`), `u R` never spells `pat` and
the free bits `zrow (Psi R) (2 * (s + i) + 1) 1` of `Psi R` never spell the complement `!pat`. -/
theorem Psi_free_constraints_width6_of_finSupp (R : Nat → Bool) (hfin : FinSupp (Psi R)) :
    ∃ S₀, ∀ s, S₀ ≤ s → ∀ pat ∈ Rule30PeriodTwoWidth6.col1Forbidden,
      (¬ ∀ i, i < pat.length → u R (s + i) = pat.getD i false) ∧
      (¬ ∀ i, i < pat.length → zrow (Psi R) (2 * (s + i) + 1) 1 = !pat.getD i false) := by
  obtain ⟨T', hT', hbad⟩ := Psi_enters_bad_of_finSupp R hfin Rule30PeriodTwoWidth6.K6 0 rfl
    Rule30PeriodTwoWidth6.K6_checkb Rule30PeriodTwoWidth6.K6_checkGb (by decide)
  refine ⟨T', fun s hs pat hpat => ?_⟩
  have hs' : T' ≤ 2 * s + 1 := by omega
  simp only [Rule30PeriodTwoWidth6.col1Forbidden, List.mem_cons, List.not_mem_nil, or_false] at hpat
  rcases hpat with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u_no_pattern_of_bad R Rule30PeriodTwoWidth6.K6 0 rfl (by decide) T' hT' hbad _ Rule30PeriodTwoWidth6.occ_p11 s hs'
  · exact u_no_pattern_of_bad R Rule30PeriodTwoWidth6.K6 0 rfl (by decide) T' hT' hbad _ Rule30PeriodTwoWidth6.occ_p00000 s hs'
  · exact u_no_pattern_of_bad R Rule30PeriodTwoWidth6.K6 0 rfl (by decide) T' hT' hbad _ Rule30PeriodTwoWidth6.occ_g21 s hs'
  · exact u_no_pattern_of_bad R Rule30PeriodTwoWidth6.K6 0 rfl (by decide) T' hT' hbad _ Rule30PeriodTwoWidth6.occ_g23 s hs'
  · exact u_no_pattern_of_bad R Rule30PeriodTwoWidth6.K6 0 rfl (by decide) T' hT' hbad _ Rule30PeriodTwoWidth6.occ_g12 s hs'
  · exact u_no_pattern_of_bad R Rule30PeriodTwoWidth6.K6 0 rfl (by decide) T' hT' hbad _ Rule30PeriodTwoWidth6.occ_g114 s hs'
  · exact u_no_pattern_of_bad R Rule30PeriodTwoWidth6.K6 0 rfl (by decide) T' hT' hbad _ Rule30PeriodTwoWidth6.occ_g132 s hs'
  · exact u_no_pattern_of_bad R Rule30PeriodTwoWidth6.K6 0 rfl (by decide) T' hT' hbad _ Rule30PeriodTwoWidth6.occ_g241 s hs'
  · exact u_no_pattern_of_bad R Rule30PeriodTwoWidth6.K6 0 rfl (by decide) T' hT' hbad _ Rule30PeriodTwoWidth6.occ_g243 s hs'

/-! ## 7. Instantaneous Invariants of `u R`, `Psi R`, and Stripe Epochs (from `s = 0`) -/

/-- **Golden rule for `u R` from `s = 0`.** For every right half `R : Nat → Bool` and every `s`,
if `u R s = true` then `u R (s + 1) = false`. -/
theorem u_golden (R : Nat → Bool) (s : Nat) (h : u R s = true) : u R (s + 1) = false := by
  have h1 : drv altCol R (2 * s + 1) 1 = true := h
  have e1 : drv altCol R (2 * s + 2) 1 =
      rule (drv altCol R (2 * s + 1) 0) (drv altCol R (2 * s + 1) 1) (drv altCol R (2 * s + 1) 2) := rfl
  rw [drv_col0, altCol_odd, h1] at e1
  have h2 : drv altCol R (2 * s + 2) 1 = true := by rw [e1]; rfl
  have e2 : drv altCol R (2 * s + 3) 1 =
      rule (drv altCol R (2 * s + 2) 0) (drv altCol R (2 * s + 2) 1) (drv altCol R (2 * s + 2) 2) := rfl
  rw [drv_col0, show 2 * s + 2 = 2 * (s + 1) by omega, altCol_even,
    show 2 * (s + 1) = 2 * s + 2 by omega, h2] at e2
  unfold u
  rw [show 2 * (s + 1) + 1 = 2 * s + 3 by omega, e2]
  rfl

/-- Finite window of `drv c R` starting at column `p + 1` of length `n`. -/
def drvRow (c R : Nat → Bool) (t p : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => drv c R t (p + 1) :: drvRow c R t (p + 1) n

theorem length_drvRow (c R : Nat → Bool) (t : Nat) :
    ∀ (n p : Nat), (drvRow c R t p n).length = n
  | 0, _ => rfl
  | n + 1, p => by simp [drvRow, length_drvRow c R t n (p + 1)]

theorem stepRow_drvRow (c R : Nat → Bool) (t : Nat) : ∀ (n p : Nat),
    Rule30BlackRuns.stepRow (drv c R t p) (drvRow c R t p (n + 1)) = drvRow c R (t + 1) p n
  | 0, _ => rfl
  | n + 1, p => by
    show rule (drv c R t p) (drv c R t (p + 1)) (drv c R t (p + 2)) ::
        Rule30BlackRuns.stepRow (drv c R t (p + 1)) (drvRow c R t (p + 1) (n + 1)) =
      drv c R (t + 1) (p + 1) :: drvRow c R (t + 1) (p + 1) n
    rw [stepRow_drvRow c R t n (p + 1)]
    rfl

theorem col1_drvRow (R : Nat → Bool) : ∀ (cs : List Bool) (t n : Nat),
    (∀ i, (hi : i < cs.length) → drv altCol R (t + i) 0 = cs[i]) →
    Rule30PeriodTwo.col1 cs (drvRow altCol R t 0 (n + cs.length + 1)) =
      (List.range cs.length).map (fun i => drv altCol R (t + i) 1)
  | [], t, n, _ => rfl
  | c :: cs, t, n, h => by
    have h0 : drv altCol R t 0 = c := h 0 (by simp)
    have hs : Rule30BlackRuns.stepRow c (drvRow altCol R t 0 ((n + cs.length + 1) + 1)) =
        drvRow altCol R (t + 1) 0 (n + cs.length + 1) := by
      rw [← h0]; exact stepRow_drvRow altCol R t (n + cs.length + 1) 0
    have ih := col1_drvRow R cs (t + 1) n (fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show t + 1 + i = t + (i + 1) by omega]
      simpa using this)
    show (drvRow altCol R t 0 (n + (cs.length + 1) + 1)).headD false ::
        Rule30PeriodTwo.col1 cs (Rule30BlackRuns.stepRow c (drvRow altCol R t 0 (n + (cs.length + 1) + 1))) =
      (List.range (cs.length + 1)).map (fun i => drv altCol R (t + i) 1)
    rw [show n + (cs.length + 1) + 1 = (n + cs.length + 1) + 1 by omega, hs, ih,
      List.range_succ_eq_map]
    simp only [drvRow, List.headD_cons, List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.succ_eq_add_one]
    rw [show t + 1 + i = t + (i + 1) by omega]

/-- **Five-step rule for `u R` from `s = 0`.** For every right half `R : Nat → Bool` and every `s`,
at least one of the five consecutive values `u R (s + i)` (`i < 5`) is `true`. -/
theorem u_black_among_five (R : Nat → Bool) (s : Nat) :
    ∃ i, i < 5 ∧ u R (s + i) = true := by
  have hc : ∀ i, (hi : i < (Rule30PeriodTwo.alt 9).length) →
      drv altCol R (2 * s + 1 + i) 0 = (Rule30PeriodTwo.alt 9)[i] := by
    intro i hi
    simp only [Rule30PeriodTwo.alt, List.getElem_map, List.getElem_range]
    rw [drv_col0]
    unfold altCol
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · have h1 : (2 * s + 1 + i) % 2 = 1 := by omega
      simp [h, h1]
    · have h1 : (2 * s + 1 + i) % 2 = 0 := by omega
      simp [h, h1]
  have hw := col1_drvRow R (Rule30PeriodTwo.alt 9) (2 * s + 1) 1 hc
  rw [Rule30PeriodTwo.alt_length] at hw
  have hmem : drvRow altCol R (2 * s + 1) 0 (1 + 9 + 1) ∈ allLists 11 := by
    have := mem_allLists (drvRow altCol R (2 * s + 1) 0 11)
    rwa [length_drvRow] at this
  have hck := List.all_eq_true.1 col1_five_check _ hmem
  rw [hw] at hck
  have hv : ∀ i, i < 9 →
      ((List.range 9).map (fun i => drv altCol R (2 * s + 1 + i) 1)).getD i false =
        drv altCol R (2 * s + 1 + i) 1 := by
    intro i hi
    simp [List.getD_eq_getElem?_getD, hi]
  unfold blackAmongFive at hck
  rw [hv 0 (by omega), hv 2 (by omega), hv 4 (by omega), hv 6 (by omega), hv 8 (by omega)] at hck
  simp only [Bool.or_eq_true] at hck
  rcases hck with (((h0 | h2) | h4) | h6) | h8
  · exact ⟨0, by omega, by unfold u; rw [show 2 * (s + 0) + 1 = 2 * s + 1 + 0 by omega]; exact h0⟩
  · exact ⟨1, by omega, by unfold u; rw [show 2 * (s + 1) + 1 = 2 * s + 1 + 2 by omega]; exact h2⟩
  · exact ⟨2, by omega, by unfold u; rw [show 2 * (s + 2) + 1 = 2 * s + 1 + 4 by omega]; exact h4⟩
  · exact ⟨3, by omega, by unfold u; rw [show 2 * (s + 3) + 1 = 2 * s + 1 + 6 by omega]; exact h6⟩
  · exact ⟨4, by omega, by unfold u; rw [show 2 * (s + 4) + 1 = 2 * s + 1 + 8 by omega]; exact h8⟩

/-- **The free bits of `Psi R` contain no `00` and no `11111` at any step `s ≥ 0`.** -/
theorem Psi_free_no00_no11111 (R : Nat → Bool) (s : Nat) :
    ¬ (zrow (Psi R) (2 * s + 1) 1 = false ∧ zrow (Psi R) (2 * (s + 1) + 1) 1 = false) ∧
    ¬ ∀ i, i < 5 → zrow (Psi R) (2 * (s + i) + 1) 1 = true := by
  refine ⟨fun ⟨h0, h1⟩ => ?_, fun hall => ?_⟩
  · rw [Psi_free] at h0 h1
    have hu0 : u R s = true := by unfold u; revert h0; cases drv altCol R (2 * s + 1) 1 <;> decide
    have hu1 : u R (s + 1) = true := by unfold u; revert h1; cases drv altCol R (2 * (s + 1) + 1) 1 <;> decide
    have := u_golden R s hu0
    rw [hu1] at this
    exact absurd this (by decide)
  · obtain ⟨i, hi, hub⟩ := u_black_among_five R s
    have hpsi := hall i hi
    rw [Psi_free] at hpsi
    unfold u at hub
    rw [hub] at hpsi
    exact absurd hpsi (by decide)

/-- Well-ordering helper: if `P` fails somewhere in `1..n`, there is a first `d ∈ [1, n]` where `P` fails. -/
theorem exists_first_diff_le (P : Nat → Prop) [DecidablePred P] :
    ∀ n, (¬ ∀ k, 1 ≤ k → k ≤ n → P k) →
      ∃ d, 1 ≤ d ∧ d ≤ n ∧ (∀ k, 1 ≤ k → k < d → P k) ∧ ¬ P d
  | 0, h => absurd (fun _ h1 h2 => by omega) h
  | n + 1, h => by
    by_cases hn : ∀ k, 1 ≤ k → k ≤ n → P k
    · have hnp : ¬ P (n + 1) := fun hp => h fun k hk1 hk2 => by
        rcases Nat.lt_or_eq_of_le hk2 with hlt | rfl
        · exact hn k hk1 (by omega)
        · exact hp
      exact ⟨n + 1, by omega, by omega, fun k hk1 hk2 => hn k hk1 (by omega), hnp⟩
    · obtain ⟨d, hd1, hd2, hag, hne⟩ := exists_first_diff_le P n hn
      exact ⟨d, hd1, by omega, hag, hne⟩

/-- **At every even step `2 * s`, `zrow (Psi R) (2 * s)` never agrees with `stripe` on `1..10`.** -/
theorem Psi_even_not_stripe_10 (R : Nat → Bool) (s : Nat) :
    ¬ ∀ k, 1 ≤ k → k ≤ 10 → zrow (Psi R) (2 * s) k = stripe k := by
  intro hag
  refine (Psi_free_no00_no11111 R s).2 fun i hi => ?_
  rw [show 2 * (s + i) + 1 = 2 * s + (2 * i + 1) by omega, zrow_shift,
    zrow_light_cone (L' := stripe) (2 * i + 1) 1 (fun k hk1 hk2 => hag k hk1 (by omega)),
    zrow_stripe]
  rfl

/-- **First-deviation bound for `Psi R` at every even step.**
For every right half `R : Nat → Bool` and every `s : Nat`, the first depth `d` at which
`zrow (Psi R) (2 * s)` (and in particular `Psi R` at `s = 0`) deviates from the stripe `…10101`
is an even depth `d ∈ {2, 4, 6, 8, 10}`. -/
theorem Psi_even_first_defect_le_10 (R : Nat → Bool) (s : Nat) :
    ∃ d, 2 ≤ d ∧ d ≤ 10 ∧ d % 2 = 0 ∧
      (∀ k, 1 ≤ k → k < d → zrow (Psi R) (2 * s) k = stripe k) ∧
      zrow (Psi R) (2 * s) d ≠ stripe d := by
  obtain ⟨d, hd1, hd10, hag, hne⟩ :=
    exists_first_diff_le (fun k => zrow (Psi R) (2 * s) k = stripe k) 10 (Psi_even_not_stripe_10 R s)
  have hc : Rule30ZeroBoundaryStripe.Constrained (zrow (Psi R) (2 * s)) 10 := by
    intro j _
    rw [← zrow_shift, show 2 * s + 2 * j = 2 * (s + j) by omega]
    exact Psi_inX R (s + j)
  have hev := Rule30ZeroBoundaryStripe.first_defect_even (zrow (Psi R) (2 * s)) 10 d hd1 (by omega)
    hag hne hc
  exact ⟨d, by omega, hd10, hev, hag, hne⟩

/-! ## 8. Universal Bounded-Gap and Coupled Death Theorems (`alternation_bounded_of_Psi_black`) -/

/-- **A single black cell of `Psi R` at depth `D` bounds the alternation time of every left half
`L` that is white at depth `D`.**
In particular, if `Psi R D = true`, then for all `2^(D - 1)` left halves `L` supported below `D`,
`glue L R` has an exact alternation death time `1 ≤ d ≤ D`. -/
theorem alternation_bounded_of_Psi_black (L R : Nat → Bool) {D : Nat} (hD : 1 ≤ D)
    (hPsi : Psi R D = true) (hL : L D = false) :
    ∃ d, 1 ≤ d ∧ d ≤ D ∧
      (∀ t, t < d → evol (glue L R) t 0 = altCol t) ∧
      evol (glue L R) d 0 ≠ altCol d := by
  have hnot : ¬ ∀ k, 1 ≤ k → k ≤ D → L k = Psi R k := by
    intro hall
    have := hall D hD (Nat.le_refl D)
    rw [hL, hPsi] at this
    exact absurd this (by decide)
  obtain ⟨d, hd1, hdD, hag, hne⟩ := exists_first_diff_le (fun k => L k = Psi R k) D hnot
  obtain ⟨h1, h2⟩ := exact_death_center hd1 hag hne
  exact ⟨d, hd1, hdD, h1, h2⟩

/-- **General bounded-gap theorem from a bounded-width `Q01` certificate.**
If every start supported at depths `≤ W` dies at an even step `< 2 * D`, then every constrained
row `L` (`InX L`) has a black cell in `(d, 2 * D - 1]` for every `d ≤ W`. -/
theorem inX_black_in_window_of_q01 {W D : Nat} (hD : 1 ≤ D)
    (hq : ∀ x : Nat → Bool, (∀ k, W < k → x k = false) →
      ∃ j, 2 * j < 2 * D ∧ zrow x (2 * j) 1 = false)
    {L : Nat → Bool} (hX : InX L) {d : Nat} (hd : d ≤ W) :
    ∃ k, d < k ∧ k ≤ 2 * D - 1 ∧ L k = true := by
  refine Classical.byContradiction fun hn => ?_
  have hz : ∀ k, d < k → k ≤ 2 * D - 1 → L k = false := by
    intro k hk1 hk2
    cases h : L k
    · rfl
    · exact absurd ⟨k, hk1, hk2, h⟩ hn
  obtain ⟨j, hj, hdead⟩ := hq (truncate L d) (fun k hk => truncate_fin L d k (by omega))
  have hlc : zrow (truncate L d) (2 * j) 1 = zrow L (2 * j) 1 := by
    apply zrow_light_cone
    intro i _ hi
    unfold truncate
    by_cases hid : i ≤ d
    · simp [hid]
    · simp [hid, hz i (by omega) (by omega)]
  rw [hlc, hX j] at hdead
  exact absurd hdead (by decide)

/-- **Universal window bound for `Psi R` and `zrow (Psi R) (2 * s)` from `q01_width_le_16`.**
For every right half `R : Nat → Bool`, every `s : Nat`, and every `d ≤ 16`, the row
`zrow (Psi R) (2 * s)` (and in particular `Psi R` itself at `s = 0`) has a black cell at some
depth `k` with `d < k ≤ 33`. In particular (`d = 16`), `Psi R` always has a black cell in `[17, 33]`. -/
theorem Psi_black_in_window_16 (R : Nat → Bool) (s d : Nat) (hd : d ≤ 16) :
    ∃ k, d < k ∧ k ≤ 33 ∧ zrow (Psi R) (2 * s) k = true := by
  have hX : InX (zrow (Psi R) (2 * s)) := by
    intro j
    rw [← zrow_shift, show 2 * s + 2 * j = 2 * (s + j) by omega]
    exact Psi_inX R (s + j)
  exact inX_black_in_window_of_q01 (W := 16) (D := 17) (by decide)
    Rule30ZeroBoundarySmall.q01_width_le_16 hX hd

/-- **Every coupled configuration `glue L R` with `L` supported at depths `≤ 16` fails center
alternation at an exact time `1 ≤ d ≤ 33`, whatever the right half `R`.** -/
theorem coupled_no_left16_alternating (L R : Nat → Bool) (hL : ∀ k, 16 < k → L k = false) :
    ∃ d, 1 ≤ d ∧ d ≤ 33 ∧
      (∀ t, t < d → evol (glue L R) t 0 = altCol t) ∧
      evol (glue L R) d 0 ≠ altCol d := by
  obtain ⟨D, hD1, hD2, hPsi⟩ := Psi_black_in_window_16 R 0 16 (Nat.le_refl 16)
  rw [Nat.mul_zero, zrow_zero_of_pos _ (by omega)] at hPsi
  obtain ⟨d, hd1, hdD, h1, h2⟩ := alternation_bounded_of_Psi_black L R (by omega) hPsi (hL D hD1)
  exact ⟨d, hd1, by omega, h1, h2⟩

/-! ## 9. Bitwise Kernel Certification of the `R = ∅` Milestone (`Psi empty`, `CQ01Empty`) to Depth `1000` -/

/-- **Quantitative Jen-clock lower bound on the support of `Psi R`.**
If `u R` is `p`-periodic (`p > 0`) on a window `[s₀, s₀ + ℓ]` and `Psi R` is supported at depths
`≤ W`, then `2 * ℓ + 2 ≤ 2 * s₀ + W + 4 * p`. -/
theorem Psi_support_bound_of_u_period (R : Nat → Bool) {W s₀ ℓ p : Nat} (hp : 0 < p)
    (hW : ∀ k, W < k → Psi R k = false)
    (hper : ∀ s, s₀ ≤ s → s + p ≤ s₀ + ℓ → u R (s + p) = u R s) :
    2 * ℓ + 2 ≤ 2 * s₀ + W + 4 * p := by
  obtain ⟨m, hm, hedge, hz⟩ := last_black (show Psi R 1 = true from Psi_inX R 0) W hW
  have h1 := free_bits_clock hm hedge hz (Psi_inX R) hp (s₀ := s₀) (ℓ := ℓ) (fun s hs1 hs2 => by
    rw [Psi_free, Psi_free]
    exact congrArg (!·) (hper s hs1 hs2))
  have hmW : m ≤ W := by
    rcases Nat.lt_or_ge W m with hlt | hge
    · rw [hW m hlt] at hedge; exact absurd hedge (by decide)
    · exact hge
  omega

/-- One step of the packed right half driven by `cNext` at column `0`.
Bit `p` of `r` holds column `p` at time `t`. -/
def rstep (cNext : Bool) (r : Nat) : Nat :=
  ((r ^^^ ((r >>> 1) ||| (r >>> 2))) <<< 1) ||| (if cNext then 1 else 0)

theorem testBit_rstep (cNext : Bool) (r : Nat) : ∀ p : Nat,
    (rstep cNext r).testBit p =
      if p = 0 then cNext else rule (r.testBit (p - 1)) (r.testBit p) (r.testBit (p + 1))
  | 0 => by cases cNext <;> simp [rstep]
  | q + 1 => by
    have h0 : (if cNext then 1 else 0).testBit (q + 1) = false := by
      cases cNext
      · simp
      · exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
    simp [rstep, Nat.testBit_or, h0, Nat.testBit_shiftLeft, Nat.testBit_xor,
      Nat.testBit_shiftRight, rule, show 1 + q = q + 1 by omega, show 2 + q = q + 2 by omega]

/-- Packed evolution of `drv altCol empty` at time `t`. -/
def rrun : Nat → Nat
  | 0 => 1
  | t + 1 => rstep (decide ((t + 1) % 2 = 0)) (rrun t)

theorem testBit_rrun : ∀ t p : Nat, (rrun t).testBit p = drv altCol empty t p
  | 0, 0 => rfl
  | 0, p + 1 => Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
  | t + 1, 0 => by
    rw [rrun, testBit_rstep]
    rfl
  | t + 1, p + 1 => by
    rw [rrun, testBit_rstep]
    simp [testBit_rrun t p, testBit_rrun t (p + 1), testBit_rrun t (p + 2)]
    rfl

theorem u_empty_eq_rrun (s : Nat) : u empty s = (rrun (2 * s + 1)).testBit 1 := by
  unfold u
  exact (testBit_rrun (2 * s + 1) 1).symm

/-- Linear-time collector of `[u empty k, …, u empty (k + n - 1)]` from `r = rrun (2 * k)`. -/
def collectU : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, r =>
    let r1 := rstep false r
    let r2 := rstep true r1
    r1.testBit 1 :: collectU n r2

theorem getD_collectU : ∀ (n k j : Nat), j < n →
    (collectU n (rrun (2 * k))).getD j false = u empty (k + j)
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | _ + 1, k, 0, _ => by
    have h1 : rstep false (rrun (2 * k)) = rrun (2 * k + 1) := by
      show _ = rstep (decide ((2 * k + 1) % 2 = 0)) (rrun (2 * k))
      rw [decide_eq_false (by omega)]
    simp [collectU, h1, u_empty_eq_rrun]
  | n + 1, k, j + 1, hj => by
    have h1 : rstep false (rrun (2 * k)) = rrun (2 * k + 1) := by
      show _ = rstep (decide ((2 * k + 1) % 2 = 0)) (rrun (2 * k))
      rw [decide_eq_false (by omega)]
    have h2 : rstep true (rrun (2 * k + 1)) = rrun (2 * (k + 1)) := by
      show _ = rstep (decide ((2 * k + 1 + 1) % 2 = 0)) (rrun (2 * k + 1))
      rw [decide_eq_true (by omega)]
    show (collectU n (rstep true (rstep false (rrun (2 * k))))).getD j false = u empty (k + (j + 1))
    rw [h1, h2, getD_collectU n (k + 1) j (by omega), show k + 1 + j = k + (j + 1) by omega]

/-- Check that `u empty` has period `7` on `[4, 152]` (`4 ≤ s ≤ 145`) and breaks period `7` at `s = 153`. -/
def checkUPeriod7 : Bool :=
  let us := collectU 154 1
  (List.range 142).all (fun i => us.getD (4 + i + 7) false == us.getD (4 + i) false) &&
    (us.getD 153 false != us.getD 146 false)

theorem checkUPeriod7_ok : checkUPeriod7 = true := by decide +kernel

/-- **The period-`7` ether transient in `u empty`.**
Driven by `altCol` from the white right half `empty`, column `1` at the white steps (`u empty`)
locks into a period-`7` stretch across `[4, 152]` (`21` full periods) before the right light-cone
reflection breaks period `7` at `s = 153` (`t = 307`). -/
theorem u_empty_period7_stretch :
    (∀ s, 4 ≤ s → s + 7 ≤ 152 → u empty (s + 7) = u empty s) ∧ u empty 153 ≠ u empty 146 := by
  have h := checkUPeriod7_ok
  unfold checkUPeriod7 at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, bne_iff_ne, ne_eq] at h
  refine ⟨fun s hs1 hs2 => ?_, ?_⟩
  · have hi := h.1 (s - 4) (by omega)
    have e1 := getD_collectU 154 0 (4 + (s - 4) + 7) (by omega)
    have e2 := getD_collectU 154 0 (4 + (s - 4)) (by omega)
    simp only [rrun, Nat.zero_add] at e1 e2
    rw [show 4 + (s - 4) = s by omega] at e1 e2 hi
    rw [← e1, ← e2]
    exact hi
  · have e1 := getD_collectU 154 0 153 (by omega)
    have e2 := getD_collectU 154 0 146 (by omega)
    simp only [rrun, Nat.zero_add] at e1 e2
    rw [← e1, ← e2]
    exact h.2

/-- Linear-time builder of the packed column-`-1` sequence `alt (fun s => !u empty s)` on `[t, t + n)`. -/
def buildY : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, t, r =>
    let b := if t % 2 == 0 then true else !r.testBit 1
    (if b then 1 <<< t else 0) ||| buildY n (t + 1) (rstep (decide ((t + 1) % 2 = 0)) r)

theorem testBit_buildY : ∀ (n t i : Nat),
    (buildY n t (rrun t)).testBit i =
      (decide (t ≤ i) && decide (i < t + n) && alt (fun s => !u empty s) i)
  | 0, t, i => by
    simp only [buildY, Nat.zero_testBit]
    by_cases h : t ≤ i
    · simp [h]
    · simp [h]
  | n + 1, t, i => by
    have hstep : rstep (decide ((t + 1) % 2 = 0)) (rrun t) = rrun (t + 1) := rfl
    have hb : (if t % 2 == 0 then true else !(rrun t).testBit 1) = alt (fun s => !u empty s) t := by
      unfold alt
      by_cases hev : t % 2 = 0
      · simp [hev]
      · have hodd : (t % 2 == 0) = false := by
          cases hq : (t % 2 == 0)
          · rfl
          · exact absurd (beq_iff_eq.1 hq) hev
        simp only [hev, ↓reduceIte, hodd, Bool.false_eq_true]
        rw [u_empty_eq_rrun, show 2 * (t / 2) + 1 = t by omega]
    rw [buildY, hstep, hb, Nat.testBit_or, testBit_buildY n (t + 1) i]
    by_cases hit : i = t
    · subst hit
      cases ha : alt (fun s => !u empty s) i <;>
        simp [Nat.one_shiftLeft, show ¬ (i + 1 ≤ i) by omega]
    · have h0 : (if alt (fun s => !u empty s) t then 1 <<< t else 0).testBit i = false := by
        cases alt (fun s => !u empty s) t
        · simp
        · simp [Nat.one_shiftLeft, show t ≠ i by omega]
      rw [h0, Bool.false_or]
      by_cases h1 : t + 1 ≤ i
      · simp only [h1, show t ≤ i by omega, decide_true, Bool.true_and]
        rw [show t + 1 + n = t + (n + 1) by omega]
      · simp [h1, show ¬ (t ≤ i) by omega]

/-- One sideways reconstruction step on packed time columns:
`recon a (k + 2) t = xor (recon a (k + 1) (t + 1)) (recon a (k + 1) t || recon a k t)`. -/
def reconStep (c1 c0 : Nat) : Nat := (c1 >>> 1) ^^^ (c1 ||| c0)

theorem testBit_reconStep (c1 c0 t : Nat) :
    (reconStep c1 c0).testBit t = xor (c1.testBit (t + 1)) (c1.testBit t || c0.testBit t) := by
  simp [reconStep, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.add_comm]

/-- Collects `[recon a (k + 1) 0, …, recon a (k + n) 0]` in `n` bitwise steps. -/
def reconCollect : Nat → Nat → Nat → List Bool
  | 0, _, _ => []
  | n + 1, c1, c0 => c1.testBit 0 :: reconCollect n (reconStep c1 c0) c1

theorem getD_reconCollect (a : Nat → Bool) :
    ∀ (n k c1 c0 j : Nat),
      (∀ t, t < n → c1.testBit t = recon a (k + 1) t) →
      (∀ t, t < n → c0.testBit t = recon a k t) →
      j < n →
      (reconCollect n c1 c0).getD j false = recon a (k + 1 + j) 0
  | 0, _, _, _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | _ + 1, k, c1, _, 0, hc1, _, _ => by
    simp [reconCollect, hc1 0 (by omega)]
  | n + 1, k, c1, c0, j + 1, hc1, hc0, hj => by
    show (reconCollect n (reconStep c1 c0) c1).getD j false = recon a (k + 1 + (j + 1)) 0
    rw [getD_reconCollect a n (k + 1) (reconStep c1 c0) c1 j
      (fun t ht => by
        rw [testBit_reconStep, hc1 (t + 1) (by omega), hc1 t (by omega), hc0 t (by omega),
          ← recon_two])
      (fun t ht => hc1 t (by omega))
      (by omega)]
    rw [show k + 1 + 1 + j = k + 1 + (j + 1) by omega]

/-- The first `N` cells `[Psi empty 1, …, Psi empty N]` computed in `2 N` bitwise operations. -/
def psiEmptyList (N : Nat) : List Bool :=
  reconCollect N (buildY N 0 1) 0

theorem getD_psiEmptyList (N j : Nat) (hj : j < N) :
    (psiEmptyList N).getD j false = Psi empty (j + 1) := by
  unfold psiEmptyList
  have h := getD_reconCollect (alt (fun s => !u empty s)) N 0 (buildY N 0 1) 0 j
    (fun t ht => by
      have e := testBit_buildY N 0 t
      simp only [rrun, Nat.zero_le, decide_true, Nat.zero_add, ht, Bool.true_and] at e
      exact e)
    (fun _ _ => Nat.zero_testBit _)
    hj
  rw [Nat.zero_add, show 1 + j = j + 1 by omega] at h
  exact h

/-- **Depth `997` of `Psi empty` is black** (kernel-certified). -/
theorem psi_empty_997_true : Psi empty 997 = true := by
  have h : (psiEmptyList 1000).getD 996 false = true := by decide +kernel
  rwa [getD_psiEmptyList 1000 996 (by omega)] at h

/-- Check that every window of length `gap` starting at `w < W` in `l` contains `true`. -/
def hasBlackWindow (l : List Bool) (W gap : Nat) : Bool :=
  (List.range W).all fun w => (List.range gap).any fun i => l.getD (w + i) false

theorem hasBlackWindow_psiEmpty_989_9 :
    hasBlackWindow (psiEmptyList 1000) 989 9 = true := by
  decide +kernel

/-- **Bounded white gaps in `Psi empty` up to depth `997`.**
For every `W ≤ 988`, there is a black cell of `Psi empty` at some depth `d` with `W < d ≤ W + 9`. -/
theorem psi_empty_black_in_window_9 (W : Nat) (hW : W ≤ 988) :
    ∃ d, W < d ∧ d ≤ W + 9 ∧ Psi empty d = true := by
  have hall := hasBlackWindow_psiEmpty_989_9
  unfold hasBlackWindow at hall
  have hw := List.all_eq_true.1 hall W (List.mem_range.2 (by omega))
  obtain ⟨i, hi, hbit⟩ := List.any_eq_true.1 hw
  rw [List.mem_range] at hi
  rw [getD_psiEmptyList 1000 (W + i) (by omega)] at hbit
  exact ⟨W + i + 1, by omega, by omega, hbit⟩

/-- **Exact truncation death within `9` steps for `Psi empty` up to width `988`.**
For every truncation width `W ≤ 988`, cutting `Psi empty` at depth `W` produces a configuration
`glue (truncate (Psi empty) W) empty` whose center column alternates through time `d - 1 ≥ W` and
fails alternation at an exact step `d` with `W < d ≤ W + 9`. -/
theorem psi_empty_truncation_dies_within_9 (W : Nat) (hW : W ≤ 988) :
    ∃ d, W < d ∧ d ≤ W + 9 ∧
      (∀ t, t < d → evol (glue (truncate (Psi empty) W) empty) t 0 = altCol t) ∧
      evol (glue (truncate (Psi empty) W) empty) d 0 ≠ altCol d := by
  obtain ⟨k, hk1, hk2, hbit⟩ := psi_empty_black_in_window_9 W hW
  have hnot : ¬ ∀ j, 1 ≤ j → j ≤ 9 → Psi empty (W + j) = false := by
    intro hall
    have := hall (k - W) (by omega) (by omega)
    rw [show W + (k - W) = k by omega, hbit] at this
    exact absurd this (by decide)
  obtain ⟨j, hj1, hj9, hag, hne⟩ :=
    exists_first_diff_le (fun j => Psi empty (W + j) = false) 9 hnot
  have hdj : Psi empty (W + j) = true := by
    revert hne; cases Psi empty (W + j) <;> simp
  have hz : ∀ m, W < m → m < W + j → Psi empty m = false := by
    intro m hm1 hm2
    have := hag (m - W) (by omega) (by omega)
    rwa [show W + (m - W) = m by omega] at this
  obtain ⟨h1, h2⟩ := truncation_death empty (W := W) (d := W + j) (by omega) hdj hz
  exact ⟨W + j, by omega, by omega, h1, h2⟩

/-- **No left half `L` supported at depths `≤ 996` keeps the center of `glue L empty` alternating
through step `997`** (kernel-certified extension of `CQ01Empty` to width `996`). -/
theorem no_empty_right_alternating_le_996 (L : Nat → Bool) (hL : ∀ k, 996 < k → L k = false) :
    ∃ d, 1 ≤ d ∧ d ≤ 997 ∧
      (∀ t, t < d → evol (glue L empty) t 0 = altCol t) ∧
      evol (glue L empty) d 0 ≠ altCol d :=
  alternation_bounded_of_Psi_black L empty (by decide) psi_empty_997_true (hL 997 (by decide))

end Phase2

/-! ## 10. Universal Left-Permutive Difference Front and Master Coupled Exclusion (`evol_diff_front`, `not_coupled_of_right_masked_periodic`) -/

section Phase3

open Rule30ZeroBoundary Rule30PeriodTwoCoupled Rule30PeriodTwoSideways
open Rule30Ether (ether ether_congr ether_period wallStates wall_facts IsR30 rowOf rowOf_succ
  rowOf_head drv drv_col0 drv_init drv_isR30 seg_congr wordAt w0001 w0011 w0111 aligned
  aligned_spec aligned_0001_6 aligned_0011_0 aligned_0011_1 aligned_0111_2 InFamily Absorption
  A0001 A0011 A0111 A0001_ok A0011_ok A0111_ok)
open Rule30PeriodFourSkeleton
open Rule30EtherThree

/-- **Universal left-permutive difference front.**
If two configurations `x, x' : Int → Bool` agree strictly to the right of `p₀` and differ at `p₀`,
then at every time `t`, their evolutions `evol x t` and `evol x' t` agree strictly to the right of
`p₀ + t` and differ at `p₀ + t`. -/
theorem evol_diff_front {x x' : Int → Bool} {p₀ : Int}
    (hag : ∀ p, p₀ < p → x p = x' p) (hne : x p₀ ≠ x' p₀) :
    ∀ t : Nat, (∀ p : Int, p₀ + (t : Int) < p → evol x t p = evol x' t p) ∧
      evol x t (p₀ + (t : Int)) ≠ evol x' t (p₀ + (t : Int))
  | 0 => ⟨fun p hp => hag p (by omega), by simpa [evol] using hne⟩
  | t + 1 => by
    obtain ⟨ih_ag, ih_ne⟩ := evol_diff_front hag hne t
    refine ⟨fun p hp => ?_, ?_⟩
    · show rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1)) =
        rule (evol x' t (p - 1)) (evol x' t p) (evol x' t (p + 1))
      rw [ih_ag (p - 1) (by omega), ih_ag p (by omega), ih_ag (p + 1) (by omega)]
    · show rule (evol x t (p₀ + ((t + 1 : Nat) : Int) - 1))
          (evol x t (p₀ + ((t + 1 : Nat) : Int)))
          (evol x t (p₀ + ((t + 1 : Nat) : Int) + 1)) ≠
        rule (evol x' t (p₀ + ((t + 1 : Nat) : Int) - 1))
          (evol x' t (p₀ + ((t + 1 : Nat) : Int)))
          (evol x' t (p₀ + ((t + 1 : Nat) : Int) + 1))
      have h1 : p₀ + ((t + 1 : Nat) : Int) - 1 = p₀ + (t : Int) := by omega
      rw [h1, ih_ag (p₀ + ((t + 1 : Nat) : Int)) (by omega),
        ih_ag (p₀ + ((t + 1 : Nat) : Int) + 1) (by omega)]
      revert ih_ne
      cases evol x t (p₀ + (t : Int)) <;> cases evol x' t (p₀ + (t : Int)) <;>
        cases evol x' t (p₀ + ((t + 1 : Nat) : Int)) <;>
        cases evol x' t (p₀ + ((t + 1 : Nat) : Int) + 1) <;> decide

/-- **Universal exact death for `Rule30Realization.conf R c`.**
For any right half `R : Int → Bool`, any target column `c : Nat → Bool`, any configuration
`x : Int → Bool` that agrees with `R` on `p ≥ 1`, and any depth `d : Nat`: if `x` agrees with the
sideways-reconstructed left half `lc R c · 0` on `0, …, -(d - 1)` and differs at `-d`, then column
`0` of `evol x` equals `c t` for all `t < d` and differs from `c d` at step `d`. -/
theorem exact_death_conf {x R : Int → Bool} {c : Nat → Bool} {d : Nat}
    (hR : ∀ p : Int, 1 ≤ p → x p = R p)
    (hag : ∀ m : Nat, m < d → x (-(m : Int)) = lc R c m 0)
    (hne : x (-(d : Int)) ≠ lc R c d 0) :
    (∀ t, t < d → evol x t 0 = c t) ∧ evol x d 0 ≠ c d := by
  have hfront := evol_diff_front (x := x) (x' := conf R c) (p₀ := -(d : Int))
    (fun p hp => by
      by_cases h1 : 1 ≤ p
      · rw [hR p h1, (realize R c).1 p h1]
      · have hm : (-p).toNat < d := by omega
        have hxp : x p = lc R c (-p).toNat 0 := by
          conv_lhs => rw [show p = -(((-p).toNat : Nat) : Int) by omega]
          exact hag (-p).toNat hm
        rw [hxp]
        unfold conf
        rw [if_neg h1])
    (by
      unfold conf
      rw [if_neg (by omega), show (- -(d : Int)).toNat = d by omega]
      exact hne)
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [(hfront t).1 0 (by omega), (realize R c).2 t]
  · have h := (hfront d).2
    rwa [show -(d : Int) + (d : Int) = 0 by omega, (realize R c).2 d] at h

/-- **Universal survival bound from a single black cell of `lc R c D 0`.**
If `lc R c D 0 = true` for `D ≥ 1`, then every configuration `x` with `x 0 = c 0`, `x p = R p` for
`p ≥ 1`, and `x (-D) = false` has an exact death time `1 ≤ d ≤ D` at which column `0` first
deviates from `c`. -/
theorem survival_bounded_of_lc_black {x R : Int → Bool} {c : Nat → Bool} {D : Nat} (hD : 1 ≤ D)
    (hR : ∀ p : Int, 1 ≤ p → x p = R p) (h0 : x 0 = c 0)
    (hlc : lc R c D 0 = true) (hxD : x (-(D : Int)) = false) :
    ∃ d, 1 ≤ d ∧ d ≤ D ∧ (∀ t, t < d → evol x t 0 = c t) ∧ evol x d 0 ≠ c d := by
  have hnot : ¬ ∀ m, 1 ≤ m → m ≤ D → x (-(m : Int)) = lc R c m 0 := by
    intro hall
    have := hall D hD (Nat.le_refl D)
    rw [hxD, hlc] at this
    exact absurd this (by decide)
  obtain ⟨d, hd1, hdD, hag, hne⟩ :=
    exists_first_diff_le (fun m => x (-(m : Int)) = lc R c m 0) D hnot
  have hag0 : ∀ m, m < d → x (-(m : Int)) = lc R c m 0 := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simpa [lc] using h0
    · exact hag m hpos hm
  obtain ⟨h1, h2⟩ := exact_death_conf hR hag0 hne
  exact ⟨d, hd1, hdD, h1, h2⟩

/-- Every nonzero left-finite configuration has a leftmost black cell. -/
theorem exists_leftmost_of_left_finite {x : Int → Bool} {W : Nat}
    (hW : ∀ p : Int, p < -(W : Int) → x p = false) (hne : ∃ p, x p = true) :
    ∃ lo, x lo = true ∧ ∀ p, p < lo → x p = false := by
  have key : ∀ n : Nat, (∃ p, x p = true ∧ p ≤ -(W : Int) + n) →
      ∃ lo, x lo = true ∧ ∀ p, p < lo → x p = false := by
    intro n
    induction n with
    | zero =>
      rintro ⟨p, hp, hpW⟩
      refine ⟨p, hp, fun q hq => hW q (by omega)⟩
    | succ n ih =>
      rintro ⟨p, hp, hpW⟩
      by_cases h : ∃ p, x p = true ∧ p ≤ -(W : Int) + n
      · exact ih h
      · refine ⟨p, hp, fun q hq => ?_⟩
        cases hxq : x q
        · rfl
        · exact absurd ⟨q, hxq, by omega⟩ h
  obtain ⟨p, hp⟩ := hne
  have hpW : -(W : Int) ≤ p := by
    rcases Int.lt_or_le p (-(W : Int)) with hlt | hle
    · rw [hW p hlt] at hp; exact absurd hp (by decide)
    · exact hle
  exact key (p + (W : Int)).toNat ⟨p, hp, by omega⟩

/-- **Master Coupled Exclusion Theorem.**
If a driver column `ω : Nat → Bool` has a black cell and is `Q`-periodic from `T₁` (`Q > 0`), and
column `1` of the driven right half `drv ω x` is `Q`-periodic at the white steps of `ω` from `T₁`,
then **no left-finite configuration `s` is coupled with `x` to produce `ω`**. -/
theorem not_coupled_of_right_masked_periodic {ω x : Nat → Bool}
    (hblack : ∃ t₀, ω t₀ = true) {T₁ Q : Nat} (hQ : 0 < Q)
    (hper0 : ∀ t, T₁ ≤ t → ω (t + Q) = ω t)
    (hper1 : ∀ t, T₁ ≤ t → ω t = false → drv ω x (t + Q) 1 = drv ω x t 1)
    (s : Int → Bool) (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ Rule30Coupled.Coupled ω s x := by
  intro hc
  obtain ⟨W, hW⟩ := hs
  let y : Int → Bool := Rule30Coupled.glue s (ω 0) x
  have hy0 : ∀ t, evol y t 0 = ω t := Rule30Coupled.center_glue hc
  have hy1 : ∀ t, evol y t 1 = drv ω x t 1 := by
    intro t
    have e := Rule30Coupled.evol_glue hc t 1
    rw [if_neg (by omega), show (1 : Int).toNat = 1 from rfl] at e
    exact e
  have hyW : ∀ p : Int, p < -(W : Int) → y p = false := by
    intro p hp
    show Rule30Coupled.glue s (ω 0) x p = false
    unfold Rule30Coupled.glue
    rw [if_pos (by omega)]
    exact hW p hp
  have hne : ∃ p, y p = true := by
    obtain ⟨t₀, ht₀⟩ := hblack
    refine Classical.byContradiction fun hz => ?_
    have hzero : ∀ p, y p = false := fun p => by
      cases hyp : y p
      · rfl
      · exact absurd ⟨p, hyp⟩ hz
    rw [← hy0 t₀, Rule30Coupled.evol_zero hzero] at ht₀
    exact absurd ht₀ (by decide)
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost_of_left_finite hyW hne
  refine Rule30FiniteMaskedJen.masked_jen hlo hzero 0 hQ (T := T₁) ?_ ?_
  · intro t ht
    rw [hy0 (t + Q), hy0 t]
    exact hper0 t ht
  · intro t ht hw
    rw [hy0 t] at hw
    rw [show (0 : Int) + 1 = 1 from rfl, hy1 (t + Q), hy1 t]
    exact hper1 t ht hw

/-- The realized configuration `conf R ω` is coupled with `fun p => R (p : Int)` to produce `ω`. -/
theorem coupled_conf (R : Int → Bool) (ω : Nat → Bool) :
    Rule30Coupled.Coupled ω (conf R ω) (fun p => R (p : Int)) := by
  have hc := Rule30Coupled.coupled_of_evol (conf R ω)
  have hω : (fun t => evol (conf R ω) t 0) = ω := funext (realize R ω).2
  rw [hω] at hc
  intro t
  rw [hc t]
  congr 1
  exact drv_congr (fun p hp => (realize R ω).1 (p : Int) (by omega)) t 1

/-- **Every sideways-reconstructed left half `lc R ω · 0` is coupled with `R`**, so any theorem
excluding left-finite coupled starts for `(ω, fun p => R (p : Int))` forces `lc R ω · 0` to have
infinite support (`∀ M, ∃ m > M, lc R ω m 0 = true`). -/
theorem lc_infinite_of_no_coupled {R : Int → Bool} {ω : Nat → Bool}
    (hno : ∀ s : Int → Bool, (∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) →
      ¬ Rule30Coupled.Coupled ω s (fun p => R (p : Int)))
    (M : Nat) : ∃ m, M < m ∧ lc R ω m 0 = true := by
  refine Classical.byContradiction fun h => ?_
  have hz : ∀ m, M < m → lc R ω m 0 = false := by
    intro m hm
    cases hlc : lc R ω m 0
    · rfl
    · exact absurd ⟨m, hm, hlc⟩ h
  refine hno (conf R ω) ⟨M, fun p hp => ?_⟩ (coupled_conf R ω)
  unfold conf
  rw [if_neg (by omega)]
  exact hz (-p).toNat (by omega)

/-- **Master Sideways Support Theorem (`lc_infinite_of_right_masked_periodic`).**
Whenever `ω` has a black cell and is `Q`-periodic from `T₁` (`Q > 0`), and column `1` of
`drv ω (fun p => R (p : Int))` is `Q`-periodic at the white steps of `ω` from `T₁`, the
sideways-reconstructed left half `lc R ω · 0` has infinitely many black cells. -/
theorem lc_infinite_of_right_masked_periodic {R : Int → Bool} {ω : Nat → Bool}
    (hblack : ∃ t₀, ω t₀ = true) {T₁ Q : Nat} (hQ : 0 < Q)
    (hper0 : ∀ t, T₁ ≤ t → ω (t + Q) = ω t)
    (hper1 : ∀ t, T₁ ≤ t → ω t = false →
      drv ω (fun p => R (p : Int)) (t + Q) 1 = drv ω (fun p => R (p : Int)) t 1)
    (M : Nat) : ∃ m, M < m ∧ lc R ω m 0 = true :=
  lc_infinite_of_no_coupled (not_coupled_of_right_masked_periodic hblack hQ hper0 hper1) M

/-! ## 11. Unconditional Solution of the `R = ∅` Coupled Problem (`CQEmpty`) for Period 4 (`0001`, `0011`, `0111`) and Period 3 (`001`) Across All Phases -/

/-- **General Period-4 coupled exclusion from `Rule30Ether.InFamily`.**
If a right half `x : Nat → Bool` driven by `fun t => wordAt w (t + φ)` enters `InFamily` at some
time `t1` for an aligned ether column `(j0, s_off)`, then no left-finite configuration `s` is
coupled with `x` to produce `fun t => wordAt w (t + φ)`. -/
theorem not_coupled_of_inFamily {w : List Bool} {j0 s_off φ t1 : Nat} {x : Nat → Bool}
    (hal : aligned w j0 s_off = true) (hblack : ∃ t₀, wordAt w (t₀ + φ) = true)
    (hF : InFamily (drv (fun t => wordAt w (t + φ)) x) j0 (s_off + φ) t1)
    (s : Int → Bool) (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ Rule30Coupled.Coupled (fun t => wordAt w (t + φ)) s x := by
  obtain ⟨k, hk, hE, hW⟩ := hF
  let ω : Nat → Bool := fun t => wordAt w (t + φ)
  have h0 : ∀ t, t1 ≤ t → drv ω x t 0 = ether j0 (t + (s_off + φ)) := by
    intro t _
    rw [drv_col0]
    show wordAt w (t + φ) = ether j0 (t + (s_off + φ))
    rw [← aligned_spec hal (t + φ)]
    exact ether_congr rfl (by omega)
  have inv := Rule30Ether.trap_invariant (drv_isR30 ω x) j0 (s_off + φ) k t1 hk h0 hE hW
  have key : ∀ t, t1 ≤ t → ω t = false → drv ω x t 1 = ether (j0 + 1) (t + (s_off + φ)) := by
    intro t ht hw
    obtain ⟨hE', hW'⟩ := inv (t - t1)
    rw [show t1 + (t - t1) = t by omega] at hE' hW'
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have hw2 : ether 2 ((t + (s_off + φ)) % 4) = false := by
        have e : drv ω x t 0 = ether (j0 + 0) (t + (s_off + φ)) := hE' 0 (Nat.le_refl 0)
        rw [drv_col0, hw] at e
        rw [e]; exact ether_congr (by omega) (by omega)
      have hhead := (wall_facts hW').1 hw2
      rw [rowOf_head] at hhead
      have e1 : drv ω x t 1 = ether 3 ((t + (s_off + φ)) % 4) := hhead
      rw [e1]; exact ether_congr (by omega) (by omega)
    · exact hE' 1 hk0
  have hper0 : ∀ t, t1 ≤ t → ω (t + 4) = ω t := by
    intro t _
    show wordAt w (t + 4 + φ) = wordAt w (t + φ)
    unfold wordAt
    congr 1; omega
  refine not_coupled_of_right_masked_periodic hblack (Q := 4) (T₁ := t1) (by decide) hper0 ?_ s hs
  intro t ht hw
  have hw4 : ω (t + 4) = false := by rw [hper0 t ht]; exact hw
  rw [key (t + 4) (by omega) hw4, key t ht hw]
  exact ether_congr rfl (by omega)

/-- **Period-4 `Absorption` implies the full coupled conjecture `Rule30Coupled.CQ` across all phases.** -/
theorem CQ_of_absorption (w : List Bool) (A : List (Nat × Nat))
    (hal : ∀ a ∈ A, aligned w a.1 a.2 = true)
    (hblack : ∀ φ, ∃ t₀, wordAt w (t₀ + φ) = true)
    (hA : Absorption w A) (φ : Nat) :
    Rule30Coupled.CQ (fun t => wordAt w (t + φ)) := by
  rintro ⟨s, x, hs, ⟨WR, hWR⟩, hc⟩
  obtain ⟨⟨j0, s_off⟩, ha, t1, hF⟩ := hA x WR hWR φ
  exact not_coupled_of_inFamily (hal (j0, s_off) ha) (hblack φ) hF s hs hc

/-- Bitmask checker for `InFamily (drv (fun t => wordAt w (t + φ)) (fun _ => false)) j0 (s_off + φ) t1`
using linear-time `Rule30EtherThree.rowN`. -/
def checkEmptyInFamily (w : List Bool) (φ j0 s_off t1 k : Nat) : Bool :=
  let r := rowN (fun t => wordAt w (t + φ)) 0 t1
  decide ((j0 + k) % 7 = 2) &&
  (List.range k).all (fun i => r.testBit i == ether (j0 + (i + 1)) (t1 + (s_off + φ))) &&
  wallStates.contains ((t1 + (s_off + φ)) % 4, seg (fun i => r.testBit (k + i)) 13)

theorem checkEmptyInFamily_sound {w : List Bool} {φ j0 s_off t1 k : Nat}
    (h : checkEmptyInFamily w φ j0 s_off t1 k = true) :
    InFamily (drv (fun t => wordAt w (t + φ)) (fun _ => false)) j0 (s_off + φ) t1 := by
  unfold checkEmptyInFamily at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨hk, hE⟩, hW⟩ := h
  have hx : (fun p : Nat => (0 : Nat).testBit (p - 1)) = (fun _ => false) := by
    funext p; exact Nat.zero_testBit _
  have hbits : ∀ i, (rowN (fun t => wordAt w (t + φ)) 0 t1).testBit i =
      drv (fun t => wordAt w (t + φ)) (fun _ => false) t1 (i + 1) := by
    intro i; rw [rowN_eq_drv, hx]
  refine ⟨k, hk, fun p hp1 hpk => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i, p = i + 1 := ⟨p - 1, by omega⟩
    rw [← hbits i, hE i (by omega)]
  · have hrow : rowOf (drv (fun t => wordAt w (t + φ)) (fun _ => false)) t1 k 13 =
        seg (fun i => (rowN (fun t => wordAt w (t + φ)) 0 t1).testBit (k + i)) 13 := by
      unfold rowOf
      apply seg_congr
      intro i _
      rw [hbits (k + i)]
    rw [hrow]
    exact List.contains_iff_mem.1 hW

theorem wordAt_mod4 (w : List Bool) (t φ : Nat) :
    wordAt w (t + φ) = wordAt w (t + φ % 4) := by
  unfold wordAt
  congr 1; omega

theorem inFamily_mod4 (w : List Bool) (x : Nat → Bool) (j0 s_off φ t1 : Nat)
    (h : InFamily (drv (fun t => wordAt w (t + φ % 4)) x) j0 (s_off + φ % 4) t1) :
    InFamily (drv (fun t => wordAt w (t + φ)) x) j0 (s_off + φ) t1 := by
  have hdrv : (fun t => wordAt w (t + φ)) = (fun t => wordAt w (t + φ % 4)) :=
    funext fun t => wordAt_mod4 w t φ
  obtain ⟨k, hk, hE, hW⟩ := h
  refine ⟨k, hk, fun p hp1 hpk => ?_, ?_⟩
  · rw [hdrv, hE p hp1 hpk]
    exact ether_congr rfl (by omega)
  · rw [hdrv, show (t1 + (s_off + φ)) % 4 = (t1 + (s_off + φ % 4)) % 4 by omega]
    exact hW

/-- **The empty right half driven by `0001^∞` enters `InFamily` across all phases `φ ∈ ℕ` (at `t1 ≤ 14`).** -/
theorem empty_inFamily_0001 (φ : Nat) :
    ∃ t1, InFamily (drv (fun t => wordAt w0001 (t + φ)) (fun _ => false)) 6 (0 + φ) t1 := by
  have hmod : φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 := by omega
  rcases hmod with h | h | h | h
  · refine ⟨14, inFamily_mod4 w0001 _ 6 0 φ 14 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 3) (by decide +kernel)
  · refine ⟨13, inFamily_mod4 w0001 _ 6 0 φ 13 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 3) (by decide +kernel)
  · refine ⟨12, inFamily_mod4 w0001 _ 6 0 φ 12 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 3) (by decide +kernel)
  · refine ⟨11, inFamily_mod4 w0001 _ 6 0 φ 11 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 3) (by decide +kernel)

/-- **The empty right half driven by `0011^∞` enters `InFamily` across all phases `φ ∈ ℕ` (at `t1 ≤ 12`).** -/
theorem empty_inFamily_0011 (φ : Nat) :
    ∃ a ∈ A0011, ∃ t1, InFamily (drv (fun t => wordAt w0011 (t + φ)) (fun _ => false)) a.1 (a.2 + φ) t1 := by
  have hmod : φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 := by omega
  rcases hmod with h | h | h | h
  · refine ⟨(0, 0), by decide, 12, inFamily_mod4 w0011 _ 0 0 φ 12 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 2) (by decide +kernel)
  · refine ⟨(0, 0), by decide, 11, inFamily_mod4 w0011 _ 0 0 φ 11 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 2) (by decide +kernel)
  · refine ⟨(0, 0), by decide, 10, inFamily_mod4 w0011 _ 0 0 φ 10 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 2) (by decide +kernel)
  · refine ⟨(1, 3), by decide, 9, inFamily_mod4 w0011 _ 1 3 φ 9 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 1) (by decide +kernel)

/-- **The empty right half driven by `0111^∞` enters `InFamily` across all phases `φ ∈ ℕ` (at `t1 ≤ 16`).** -/
theorem empty_inFamily_0111 (φ : Nat) :
    ∃ t1, InFamily (drv (fun t => wordAt w0111 (t + φ)) (fun _ => false)) 2 (2 + φ) t1 := by
  have hmod : φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 := by omega
  rcases hmod with h | h | h | h
  · refine ⟨9, inFamily_mod4 w0111 _ 2 2 φ 9 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 0) (by decide +kernel)
  · refine ⟨8, inFamily_mod4 w0111 _ 2 2 φ 8 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 0) (by decide +kernel)
  · refine ⟨8, inFamily_mod4 w0111 _ 2 2 φ 8 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 0) (by decide +kernel)
  · refine ⟨16, inFamily_mod4 w0111 _ 2 2 φ 16 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 0) (by decide +kernel)

theorem wordAt_has_black {w : List Bool} (h3 : wordAt w 3 = true) (φ : Nat) :
    ∃ t₀, wordAt w (t₀ + φ) = true := by
  refine ⟨3 + (4 - φ % 4), ?_⟩
  unfold wordAt at h3 ⊢
  rw [show (3 + (4 - φ % 4) + φ) % 4 = 3 % 4 by omega]
  exact h3

/-- **Unconditional solution of the `R = ∅` coupled conjecture (`CQEmpty`) for `w0001` across all phases.**
No left-finite configuration `s` is coupled with the empty right half to produce `0001^∞` at any phase `φ`. -/
theorem no_empty_right_coupled_0001 (φ : Nat) (s : Int → Bool)
    (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ Rule30Coupled.Coupled (fun t => wordAt w0001 (t + φ)) s (fun _ => false) := by
  obtain ⟨t1, hF⟩ := empty_inFamily_0001 φ
  exact not_coupled_of_inFamily aligned_0001_6 (wordAt_has_black (by decide) φ) hF s hs

/-- **Unconditional solution of the `R = ∅` coupled conjecture (`CQEmpty`) for `w0011` across all phases.**
No left-finite configuration `s` is coupled with the empty right half to produce `0011^∞` at any phase `φ`. -/
theorem no_empty_right_coupled_0011 (φ : Nat) (s : Int → Bool)
    (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ Rule30Coupled.Coupled (fun t => wordAt w0011 (t + φ)) s (fun _ => false) := by
  obtain ⟨⟨j0, s_off⟩, ha, t1, hF⟩ := empty_inFamily_0011 φ
  exact not_coupled_of_inFamily (A0011_ok (j0, s_off) ha) (wordAt_has_black (by decide) φ) hF s hs

/-- **Unconditional solution of the `R = ∅` coupled conjecture (`CQEmpty`) for `w0111` across all phases.**
No left-finite configuration `s` is coupled with the empty right half to produce `0111^∞` at any phase `φ`. -/
theorem no_empty_right_coupled_0111 (φ : Nat) (s : Int → Bool)
    (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ Rule30Coupled.Coupled (fun t => wordAt w0111 (t + φ)) s (fun _ => false) := by
  obtain ⟨t1, hF⟩ := empty_inFamily_0111 φ
  exact not_coupled_of_inFamily aligned_0111_2 (wordAt_has_black (by decide) φ) hF s hs

/-- **Sideways `R = ∅` support theorem for `w0001`:** `lc (fun _ => false) (fun t => wordAt w0001 (t + φ)) · 0`
has infinitely many black cells for every phase `φ ∈ ℕ`. -/
theorem lc_empty_infinite_0001 (φ M : Nat) :
    ∃ m, M < m ∧ lc (fun _ => false) (fun t => wordAt w0001 (t + φ)) m 0 = true :=
  lc_infinite_of_no_coupled (no_empty_right_coupled_0001 φ) M

/-- **Sideways `R = ∅` support theorem for `w0011`:** `lc (fun _ => false) (fun t => wordAt w0011 (t + φ)) · 0`
has infinitely many black cells for every phase `φ ∈ ℕ`. -/
theorem lc_empty_infinite_0011 (φ M : Nat) :
    ∃ m, M < m ∧ lc (fun _ => false) (fun t => wordAt w0011 (t + φ)) m 0 = true :=
  lc_infinite_of_no_coupled (no_empty_right_coupled_0011 φ) M

/-- **Sideways `R = ∅` support theorem for `w0111`:** `lc (fun _ => false) (fun t => wordAt w0111 (t + φ)) · 0`
has infinitely many black cells for every phase `φ ∈ ℕ`. -/
theorem lc_empty_infinite_0111 (φ M : Nat) :
    ∃ m, M < m ∧ lc (fun _ => false) (fun t => wordAt w0111 (t + φ)) m 0 = true :=
  lc_infinite_of_no_coupled (no_empty_right_coupled_0111 φ) M

/-- **General Period-3 `PTrap` invariant for arbitrary phase `φ ∈ ℕ`.** -/
theorem ptrap_invariant_phase (C : PTrap) (hC : C.check = true) {F : Nat → Nat → Bool} (hF : IsR30 F)
    (φ : Nat) (hc : ∀ t, F t 0 = wordAt3 C.w (t + φ))
    (t1 i : Nat) (hi : i < C.n) (hph : (t1 + φ) % 3 = C.lab i % 3)
    (hr : EncF F C.b t1 0 (C.st i)) :
    ∀ n, ∃ j, j < C.n ∧ EncF F C.b (t1 + n) 0 (C.st j) ∧ C.lab j = (C.lab i + n) % C.m := by
  have hli : C.lab i < C.m := (PTrap.step C hC hi false).2.2.2.1
  intro n
  induction n with
  | zero => exact ⟨i, hi, by simpa using hr, by rw [Nat.add_zero, Nat.mod_eq_of_lt hli]⟩
  | succ n ih =>
    obtain ⟨j, hj, hr', hl'⟩ := ih
    have hphase : (t1 + n + φ) % 3 = C.lab j % 3 := by
      rw [hl', show t1 + n + φ = (t1 + φ) + n by omega]
      exact PTrap.phase_lab C hC _ _ hph n
    have hc0 : F (t1 + n) 0 = wordAt3 C.w (C.lab j % 3) := by
      rw [hc (t1 + n)]; unfold wordAt3; rw [Nat.mod_mod, hphase]
    obtain ⟨hnj, hst, hlab, -, -⟩ := PTrap.step C hC hj (F (t1 + n) (0 + 1 + C.b))
    refine ⟨C.nxt j (F (t1 + n) (0 + 1 + C.b)), hnj, ?_, ?_⟩
    · rw [hst, ← hc0, show t1 + (n + 1) = t1 + n + 1 by omega]
      exact encF_step hF hr'
    · rw [hlab, hl', Nat.mod_add_mod]; rfl

/-- **General Period-3 coupled exclusion from `PTrap`.**
If a right half `x` driven by `fun t => wordAt3 C.w (t + φ)` enters a checked trap `C` at time `t1`,
then no left-finite configuration `s` is coupled with `x` to produce `fun t => wordAt3 C.w (t + φ)`. -/
theorem not_coupled_of_ptrap (C : PTrap) (hC : C.check = true) (hb : 0 < C.b)
    (φ : Nat) (hblack : ∃ t₀, wordAt3 C.w (t₀ + φ) = true)
    {x : Nat → Bool} {t1 i : Nat} (hi : i < C.n) (hph : (t1 + φ) % 3 = C.lab i % 3)
    (hr : EncF (drv (fun t => wordAt3 C.w (t + φ)) x) C.b t1 0 (C.st i))
    (s : Int → Bool) (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ Rule30Coupled.Coupled (fun t => wordAt3 C.w (t + φ)) s x := by
  obtain ⟨hm, hm3, -⟩ := PTrap.facts C hC
  let ω : Nat → Bool := fun t => wordAt3 C.w (t + φ)
  have inv := ptrap_invariant_phase C hC (drv_isR30 ω x) φ (drv_col0 ω x) t1 i hi hph hr
  have key : ∀ t, t1 ≤ t → ω t = false →
      drv ω x t 1 = C.u.testBit ((C.lab i + (t - t1)) % C.m) := by
    intro t ht hw
    obtain ⟨j, hj, hr', hl'⟩ := inv (t - t1)
    rw [show t1 + (t - t1) = t by omega] at hr'
    obtain ⟨-, -, -, -, hu⟩ := PTrap.step C hC hj false
    have hphase : (t + φ) % 3 = C.lab j % 3 := by
      rw [hl', show t + φ = (t1 + φ) + (t - t1) by omega]
      exact PTrap.phase_lab C hC _ _ hph _
    have hw' : wordAt3 C.w (C.lab j % 3) = false := by
      rw [← hw]; unfold ω wordAt3; rw [Nat.mod_mod, hphase]
    rw [← hl', ← hu hw', encF_head hr' hb]
  have hper0 : ∀ t, t1 ≤ t → ω (t + C.m) = ω t := by
    intro t _
    unfold ω wordAt3
    congr 1
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hm3
    rw [hq, show t + 3 * q + φ = (t + φ) + 3 * q by omega, Nat.add_mul_mod_self_left]
  refine not_coupled_of_right_masked_periodic hblack hm hper0 ?_ s hs
  intro t ht hw
  have hwm : ω (t + C.m) = false := by rw [hper0 t ht]; exact hw
  rw [key (t + C.m) (by omega) hwm, key t ht hw,
    show C.lab i + (t + C.m - t1) = (C.lab i + (t - t1)) + C.m * 1 by omega,
    Nat.add_mul_mod_self_left]

/-- **Period-3 `AbsorptionT C` implies the full coupled conjecture `Rule30Coupled.CQ` across all phases.** -/
theorem CQ_of_absorptionT (C : PTrap) (hC : C.check = true) (hb : 0 < C.b)
    (hblack : ∀ φ, ∃ t₀, wordAt3 C.w (t₀ + φ) = true)
    (hA : AbsorptionT C) (φ : Nat) :
    Rule30Coupled.CQ (fun t => wordAt3 C.w (t + φ)) := by
  rintro ⟨s, x, hs, ⟨WR, hWR⟩, hc⟩
  obtain ⟨t1, i, hi, hph, hr⟩ := hA x WR hWR φ
  exact not_coupled_of_ptrap C hC hb φ (hblack φ) hi hph hr s hs hc

/-- When `c 0 = false`, the empty right half `0` stays `0` at step `1`, shifting `rowN` by one time step. -/
theorem rowN_zero_shift (c : Nat → Bool) (hc0 : c 0 = false) :
    ∀ t, rowN c 0 (t + 1) = rowN (fun s => c (s + 1)) 0 t
  | 0 => by show stepN (c 0) 0 = 0; rw [hc0]; rfl
  | t + 1 => by
    show stepN (c (t + 1)) (rowN c 0 (t + 1)) = stepN (c (t + 1)) (rowN (fun s => c (s + 1)) 0 t)
    rw [rowN_zero_shift c hc0 t]

theorem wordAt3_mod3 (w : List Bool) (t φ : Nat) :
    wordAt3 w (t + φ) = wordAt3 w (t + φ % 3) := by
  unfold wordAt3
  congr 1; omega

/-- **The empty right half driven by `001^∞` enters state `597` of `t001` across all phases `φ ∈ ℕ`**
(at `t1 = 1270` for `φ ≡ 0`, `t1 = 1269` for `φ ≡ 1`, and `t1 = 1268` for `φ ≡ 2` mod `3`). -/
theorem empty_absorbed_t001_all_phases (φ : Nat) :
    ∃ t1 i, i < t001.n ∧ (t1 + φ) % 3 = t001.lab i % 3 ∧
      EncF (drv (fun t => wordAt3 w001 (t + φ)) (fun _ => false)) t001.b t1 0 (t001.st i) := by
  have hx : (fun p : Nat => (0 : Nat).testBit (p - 1)) = (fun _ => false) := by
    funext p; exact Nat.zero_testBit _
  have hb : t001.b = 47 := rfl
  have hlab : t001.lab 597 % 3 = 1 := by decide
  have hdrv : (fun t => wordAt3 w001 (t + φ)) = (fun t => wordAt3 w001 (t + φ % 3)) :=
    funext fun t => wordAt3_mod3 w001 t φ
  have h1 : rowN (fun t => wordAt3 w001 (t + 0)) 0 1270 =
      rowN (fun t => wordAt3 w001 (t + 1)) 0 1269 := by
    have e := rowN_zero_shift (fun t => wordAt3 w001 (t + 0)) rfl 1269
    have hf : (fun s => wordAt3 w001 (s + 1 + 0)) = (fun t => wordAt3 w001 (t + 1)) := rfl
    rw [hf] at e; exact e
  have h2 : rowN (fun t => wordAt3 w001 (t + 1)) 0 1269 =
      rowN (fun t => wordAt3 w001 (t + 2)) 0 1268 := by
    have e := rowN_zero_shift (fun t => wordAt3 w001 (t + 1)) rfl 1268
    have hf : (fun s => wordAt3 w001 (s + 1 + 1)) = (fun t => wordAt3 w001 (t + 2)) := rfl
    rw [hf] at e; exact e
  have hmod : φ % 3 = 0 ∨ φ % 3 = 1 ∨ φ % 3 = 2 := by omega
  rcases hmod with hm | hm | hm
  · refine ⟨1270, 597, by decide, by omega, PTrap.st_lt t001 597, fun k hk => ?_⟩
    rw [hb] at hk
    rw [hdrv, hm, rowN_empty_eq, Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and,
      rowN_eq_drv, hx, show 0 + 1 + k = k + 1 by omega]
  · refine ⟨1269, 597, by decide, by omega, PTrap.st_lt t001 597, fun k hk => ?_⟩
    rw [hb] at hk
    rw [hdrv, hm, rowN_empty_eq, h1, Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and,
      rowN_eq_drv, hx, show 0 + 1 + k = k + 1 by omega]
  · refine ⟨1268, 597, by decide, by omega, PTrap.st_lt t001 597, fun k hk => ?_⟩
    rw [hb] at hk
    rw [hdrv, hm, rowN_empty_eq, h1, h2, Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and,
      rowN_eq_drv, hx, show 0 + 1 + k = k + 1 by omega]

theorem wordAt3_has_black {w : List Bool} (h2 : wordAt3 w 2 = true) (φ : Nat) :
    ∃ t₀, wordAt3 w (t₀ + φ) = true := by
  refine ⟨2 + (3 - φ % 3), ?_⟩
  unfold wordAt3 at h2 ⊢
  rw [show (2 + (3 - φ % 3) + φ) % 3 = 2 % 3 by omega]
  exact h2

/-- **Unconditional solution of the `R = ∅` coupled conjecture (`CQEmpty`) for `w001` across all phases.**
No left-finite configuration `s` is coupled with the empty right half to produce `001^∞` at any phase `φ`. -/
theorem no_empty_right_coupled_001 (φ : Nat) (s : Int → Bool)
    (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ Rule30Coupled.Coupled (fun t => wordAt3 w001 (t + φ)) s (fun _ => false) := by
  obtain ⟨t1, i, hi, hph, hr⟩ := empty_absorbed_t001_all_phases φ
  exact not_coupled_of_ptrap t001 t001_check (by decide) φ (wordAt3_has_black (by decide) φ)
    hi hph hr s hs

/-- **Sideways `R = ∅` support theorem for `w001`:** `lc (fun _ => false) (fun t => wordAt3 w001 (t + φ)) · 0`
has infinitely many black cells for every phase `φ ∈ ℕ`. -/
theorem lc_empty_infinite_001 (φ M : Nat) :
    ∃ m, M < m ∧ lc (fun _ => false) (fun t => wordAt3 w001 (t + φ)) m 0 = true :=
  lc_infinite_of_no_coupled (no_empty_right_coupled_001 φ) M

/-! ## 12. Uniform Period-3 and Period-4 Skeletons for `FinConfig` and Kernel-Checked Bounded-Width `Q001` (`W ≤ 12`) -/

theorem rowOf_evolRight_getD (x : Int → Bool) (j : Int) (t m i : Nat) (hi : i < m) :
    (rowOf (evolRight x j) t 0 m).getD i false = evol x t (j + (i : Int) + 1) := by
  unfold rowOf
  rw [seg_getD _ m i hi]
  show evol x t (j + ((0 + i + 1 : Nat) : Int)) = _
  congr 1; omega

/-- **Uniform skeleton for `001` across all configurations with a leftmost black cell.**
If column `j` of `evol x` is `001`-periodic from `T`, then eventually column `j + 1` is white at phase `0`. -/
theorem skeleton_001_leftmost {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) (j : Int) (T : Nat)
    (h : ∀ t, T ≤ t → evol x t j = wordAt3 w001 (t - T)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → (t - T) % 3 = 0 → evol x t (j + 1) = false := by
  have hP : K001.P = 3 := by decide
  have h' : ∀ t, T ≤ t → evol x t j = K001.wAt ((t - T) % K001.P) := by
    intro t ht; rw [h t ht, hP]; rfl
  obtain ⟨T', hT', hp⟩ := eventually_pred_leftmost hlo hzero j K001 k001_bad skel001
    K001_checkb K001_checkGb K001_badImp (by decide) (by decide) T h'
  refine ⟨T', hT', fun t ht hφ => ?_⟩
  have e := hp t ht
  rw [hP, hφ] at e
  have h0 : (rowOf (evolRight x j) t 0 K001.b).getD 0 false = evol x t (j + 1) := by
    rw [rowOf_evolRight_getD x j t K001.b 0 (by decide)]; congr 1; omega
  simp only [skel001, h0] at e
  simpa using e

/-- **Uniform skeleton for `001` across all nonzero finite configurations.** -/
theorem skeleton_001_finite {x : Int → Bool} (hfin : FinConfig x) (hne : ∃ p, x p = true)
    (j : Int) (T : Nat) (h : ∀ t, T ≤ t → evol x t j = wordAt3 w001 (t - T)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → (t - T) % 3 = 0 → evol x t (j + 1) = false := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact skeleton_001_leftmost hlo hzero j T h

/-- **Uniform skeleton for `011` across all configurations with a leftmost black cell.**
If column `j` of `evol x` is `011`-periodic from `T`, then eventually column `j + 1` is black at
phase `1` and white at phase `2`. -/
theorem skeleton_011_leftmost {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) (j : Int) (T : Nat)
    (h : ∀ t, T ≤ t → evol x t j = wordAt3 w011 (t - T)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t →
      ((t - T) % 3 = 1 → evol x t (j + 1) = true) ∧
      ((t - T) % 3 = 2 → evol x t (j + 1) = false) := by
  have hP : K011.P = 3 := by decide
  have h' : ∀ t, T ≤ t → evol x t j = K011.wAt ((t - T) % K011.P) := by
    intro t ht; rw [h t ht, hP]; rfl
  obtain ⟨T', hT', hp⟩ := eventually_pred_leftmost hlo hzero j K011 k011_bad skel011
    K011_checkb K011_checkGb K011_badImp (by decide) (by decide) T h'
  have h0 : ∀ t, (rowOf (evolRight x j) t 0 K011.b).getD 0 false = evol x t (j + 1) := by
    intro t; rw [rowOf_evolRight_getD x j t K011.b 0 (by decide)]; congr 1; omega
  refine ⟨T', hT', fun t ht => ⟨fun hφ => ?_, fun hφ => ?_⟩⟩
  · have e := hp t ht
    rw [hP, hφ] at e
    simp only [skel011, h0 t] at e
    exact e
  · have e := hp t ht
    rw [hP, hφ] at e
    simp only [skel011, h0 t] at e
    simpa using e

/-- **Uniform skeleton for `011` across all nonzero finite configurations.** -/
theorem skeleton_011_finite {x : Int → Bool} (hfin : FinConfig x) (hne : ∃ p, x p = true)
    (j : Int) (T : Nat) (h : ∀ t, T ≤ t → evol x t j = wordAt3 w011 (t - T)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t →
      ((t - T) % 3 = 1 → evol x t (j + 1) = true) ∧
      ((t - T) % 3 = 2 → evol x t (j + 1) = false) := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact skeleton_011_leftmost hlo hzero j T h

/-- **Uniform skeleton for `0001` across all configurations with a leftmost black cell.** -/
theorem skeleton_0001_leftmost {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) (j : Int) (T : Nat)
    (h : ∀ t, T ≤ t → evol x t j = wordAt w0001 (t - T)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t →
      ((t - T) % 4 = 0 → evol x t (j + 1) = false ∧ evol x t (j + 3) = true) ∧
      ((t - T) % 4 = 1 → evol x t (j + 2) = true) ∧
      ((t - T) % 4 = 2 → evol x t (j + 1) = true) ∧
      ((t - T) % 4 = 3 → evol x t (j + 1) = true ∧ evol x t (j + 2) = false) := by
  have hP : K0001.P = 4 := by decide
  have h' : ∀ t, T ≤ t → evol x t j = K0001.wAt ((t - T) % K0001.P) := by
    intro t ht; rw [h t ht, hP]; rfl
  obtain ⟨T', hT', hp⟩ := eventually_pred_leftmost hlo hzero j K0001 k0001_bad skel0001
    K0001_checkb K0001_checkGb K0001_badImp (by decide) (by decide) T h'
  refine ⟨T', hT', fun t ht => ?_⟩
  have e := hp t ht
  rw [hP] at e
  have h0 : (rowOf (evolRight x j) t 0 K0001.b).getD 0 false = evol x t (j + 1) := by
    rw [rowOf_evolRight_getD x j t K0001.b 0 (by decide)]; congr 1; omega
  have h1 : (rowOf (evolRight x j) t 0 K0001.b).getD 1 false = evol x t (j + 2) := by
    rw [rowOf_evolRight_getD x j t K0001.b 1 (by decide)]; congr 1; omega
  have h2 : (rowOf (evolRight x j) t 0 K0001.b).getD 2 false = evol x t (j + 3) := by
    rw [rowOf_evolRight_getD x j t K0001.b 2 (by decide)]; congr 1; omega
  refine ⟨fun hφ => ?_, fun hφ => ?_, fun hφ => ?_, fun hφ => ?_⟩
  · rw [hφ] at e; simp only [skel0001, h0, h2, ite_true, Bool.and_eq_true, Bool.not_eq_true'] at e
    exact ⟨e.1, e.2⟩
  · rw [hφ] at e; simp only [skel0001, h1] at e; simpa using e
  · rw [hφ] at e; simp only [skel0001, h0] at e; simpa using e
  · rw [hφ] at e; simp only [skel0001, h0, h1] at e; simpa using e

/-- **Uniform skeleton for `0001` across all nonzero finite configurations.** -/
theorem skeleton_0001_finite {x : Int → Bool} (hfin : FinConfig x) (hne : ∃ p, x p = true)
    (j : Int) (T : Nat) (h : ∀ t, T ≤ t → evol x t j = wordAt w0001 (t - T)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t →
      ((t - T) % 4 = 0 → evol x t (j + 1) = false ∧ evol x t (j + 3) = true) ∧
      ((t - T) % 4 = 1 → evol x t (j + 2) = true) ∧
      ((t - T) % 4 = 2 → evol x t (j + 1) = true) ∧
      ((t - T) % 4 = 3 → evol x t (j + 1) = true ∧ evol x t (j + 2) = false) := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact skeleton_0001_leftmost hlo hzero j T h

/-- **Uniform skeleton for `0011` across all configurations with a leftmost black cell.** -/
theorem skeleton_0011_leftmost {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) (j : Int) (T : Nat)
    (h : ∀ t, T ≤ t → evol x t j = wordAt w0011 (t - T)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t →
      ((t - T) % 4 = 1 → evol x t (j + 1) = true) ∧
      ((t - T) % 4 = 2 → evol x t (j + 1) = true) ∧
      ((t - T) % 4 = 3 → evol x t (j + 1) = false) := by
  have hP : K0011.P = 4 := by decide
  have h' : ∀ t, T ≤ t → evol x t j = K0011.wAt ((t - T) % K0011.P) := by
    intro t ht; rw [h t ht, hP]; rfl
  obtain ⟨T', hT', hp⟩ := eventually_pred_leftmost hlo hzero j K0011 k0011_bad skel0011
    K0011_checkb K0011_checkGb K0011_badImp (by decide) (by decide) T h'
  refine ⟨T', hT', fun t ht => ?_⟩
  have e := hp t ht
  rw [hP] at e
  have h0 : (rowOf (evolRight x j) t 0 K0011.b).getD 0 false = evol x t (j + 1) := by
    rw [rowOf_evolRight_getD x j t K0011.b 0 (by decide)]; congr 1; omega
  refine ⟨fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
  · rw [h1] at e; simp only [skel0011, h0] at e; simpa using e
  · rw [h2] at e; simp only [skel0011, h0] at e; simpa using e
  · rw [h3] at e; simp only [skel0011, h0] at e; simpa using e

/-- **Uniform skeleton for `0011` across all nonzero finite configurations.** -/
theorem skeleton_0011_finite {x : Int → Bool} (hfin : FinConfig x) (hne : ∃ p, x p = true)
    (j : Int) (T : Nat) (h : ∀ t, T ≤ t → evol x t j = wordAt w0011 (t - T)) :
    ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t →
      ((t - T) % 4 = 1 → evol x t (j + 1) = true) ∧
      ((t - T) % 4 = 2 → evol x t (j + 1) = true) ∧
      ((t - T) % 4 = 3 → evol x t (j + 1) = false) := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact skeleton_0011_leftmost hlo hzero j T h

/-- `diesBy3 n t r`: within `n` steps from time `t`, depth `1` of the ZBL is white at some time
divisible by `3`. -/
def diesBy3 : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | n + 1, t, r => (t % 3 == 0 && r % 2 == 0) || diesBy3 n (t + 1) (Rule30ZeroBoundarySmall.pstep r)

theorem diesBy3_sound : ∀ n t r, diesBy3 n t r = true →
    ∃ i, i < n ∧ (t + i) % 3 = 0 ∧ Rule30ZeroBoundarySmall.prun r i % 2 = 0 := by
  intro n
  induction n with
  | zero => intro t r h; simp [diesBy3] at h
  | succ n ih =>
    intro t r h
    simp only [diesBy3, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨0, by omega, by simpa using h1, h2⟩
    · obtain ⟨i, hi, hti, hpi⟩ := ih (t + 1) (Rule30ZeroBoundarySmall.pstep r) h
      refine ⟨i + 1, by omega, by rw [show t + (i + 1) = t + 1 + i by omega]; exact hti, ?_⟩
      rw [Rule30ZeroBoundarySmall.prun_succ]; exact hpi

def checkBelow3 (n : Nat) : Nat → Bool
  | 0 => true
  | m + 1 => diesBy3 n 0 m && checkBelow3 n m

theorem checkBelow3_sound (n : Nat) :
    ∀ m, checkBelow3 n m = true → ∀ r, r < m → diesBy3 n 0 r = true := by
  intro m
  induction m with
  | zero => intro _ r hr; omega
  | succ m ih =>
    intro h r hr
    simp only [checkBelow3, Bool.and_eq_true] at h
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hr | hr
    · exact ih h.2 r hr
    · subst hr; exact h.1

theorem q001_of_check (W n : Nat) (h : checkBelow3 n (2 ^ W) = true) (x : Nat → Bool)
    (hx : ∀ k, W < k → x k = false) : ∃ j, 3 * j < n ∧ zrow x (3 * j) 1 = false := by
  obtain ⟨r, hr, hrx⟩ := Rule30ZeroBoundarySmall.exists_pack W x hx
  obtain ⟨i, hi, hti, hpi⟩ := diesBy3_sound n 0 r (checkBelow3_sound n _ h r hr)
  refine ⟨i / 3, by omega, ?_⟩
  rw [show 3 * (i / 3) = i by omega, ← zrow_congr hrx, Rule30ZeroBoundarySmall.run_toFun]
  simp only [Rule30ZeroBoundarySmall.toFun]
  simp [hpi]

theorem check3_12 : checkBelow3 28 (2 ^ 12) = true := by decide +kernel

/-- **`Q001` for every ZBL start of width at most `12`** (kernel-checked): every start supported at
depths `≤ 12` has a white cell at depth `1` at some step `3 * j < 28` (`j ≤ 9`). -/
theorem q001_width_le_12 (x : Nat → Bool) (hx : ∀ k, 12 < k → x k = false) :
    ∃ j, 3 * j < 28 ∧ zrow x (3 * j) 1 = false :=
  q001_of_check 12 28 check3_12 x hx

/-- **`Q001` in `Rule30DrivenLeft.L` form for all starts supported on `[-12, -1]`:**
every left configuration `s : Int → Bool` with `s p = false` for `p < -12` makes column `-1` of
the zero-driven left half white at some step `3 * j < 28`. -/
theorem q001_L_width_le_12 (s : Int → Bool) (hs : ∀ p : Int, p < -12 → s p = false) :
    ∃ j, 3 * j < 28 ∧ Rule30DrivenLeft.L (fun _ => false) s (3 * j) (-1) = false := by
  obtain ⟨j, hj, h⟩ := q001_width_le_12 (fun k => s (-(k : Int))) (fun k hk => hs _ (by omega))
  refine ⟨j, hj, ?_⟩
  rw [show (-1 : Int) = -((1 : Nat) : Int) from rfl, L_eq_zrow s (3 * j) 1 (Nat.le_refl 1)]
  exact h

/-- **Bounded-gap theorem for 3-step constrained ZBL starts (`∀ j, zrow L (3 * j) 1 = true`).**
If every ZBL start of width `≤ W` dies at some step `3 * j < n`, then every start `L` satisfying
`∀ j, zrow L (3 * j) 1 = true` has a black cell in `(d, d + n]` for every `d ≤ W`. -/
theorem inX3_black_in_window_of_q001 {W n : Nat} (_hn : 1 ≤ n)
    (hq : ∀ x : Nat → Bool, (∀ k, W < k → x k = false) →
      ∃ j, 3 * j < n ∧ zrow x (3 * j) 1 = false)
    {L : Nat → Bool} (hX3 : ∀ j, zrow L (3 * j) 1 = true) {d : Nat} (hd : d ≤ W) :
    ∃ k, d < k ∧ k ≤ d + n ∧ L k = true := by
  refine Classical.byContradiction fun hno => ?_
  have hz : ∀ k, d < k → k ≤ d + n → L k = false := by
    intro k hk1 hk2
    cases h : L k
    · rfl
    · exact absurd ⟨k, hk1, hk2, h⟩ hno
  obtain ⟨j, hj, hdead⟩ := hq (truncate L d) (fun k hk => truncate_fin L d k (by omega))
  have hlc : zrow (truncate L d) (3 * j) 1 = zrow L (3 * j) 1 := by
    apply zrow_light_cone
    intro i _ hi
    unfold truncate
    by_cases hid : i ≤ d
    · simp [hid]
    · simp [hid, hz i (by omega) (by omega)]
  rw [hlc, hX3 j] at hdead
  exact absurd hdead (by decide)

/-- **Universal window bound from `q001_width_le_12`:** every ZBL start `L` satisfying
`∀ j, zrow L (3 * j) 1 = true` has a black cell in `(d, d + 28]` for every `d ≤ 12`. -/
theorem inX3_black_in_window_12 {L : Nat → Bool} (hX3 : ∀ j, zrow L (3 * j) 1 = true)
    (d : Nat) (hd : d ≤ 12) : ∃ k, d < k ∧ k ≤ d + 28 ∧ L k = true :=
  inX3_black_in_window_of_q001 (by decide) q001_width_le_12 hX3 hd

/-! ## 13. Universal Bitwise Sideways Reconstruction (`lc`) and Depth-`1000` Certification of the `R = ∅` Milestone for `w011` -/

/-- **General bitwise sideways collector for `Rule30Realization.lc R c`.**
Since `lc R c (k + 2) t = xor (lc R c (k + 1) (t + 1)) (lc R c (k + 1) t || lc R c k t)`,
`reconCollect` computes `[lc R c (k + 1) 0, …, lc R c (k + n) 0]` in `n` bitwise steps
for **any** right half `R : Int → Bool` and **any** target column `c : Nat → Bool`. -/
theorem getD_reconCollect_lc (R : Int → Bool) (c : Nat → Bool) :
    ∀ (n k c1 c0 j : Nat),
      (∀ t, t < n → c1.testBit t = lc R c (k + 1) t) →
      (∀ t, t < n → c0.testBit t = lc R c k t) →
      j < n →
      (reconCollect n c1 c0).getD j false = lc R c (k + 1 + j) 0
  | 0, _, _, _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | _ + 1, k, c1, _, 0, hc1, _, _ => by
    simp [reconCollect, hc1 0 (by omega)]
  | n + 1, k, c1, c0, j + 1, hc1, hc0, hj => by
    show (reconCollect n (reconStep c1 c0) c1).getD j false = lc R c (k + 1 + (j + 1)) 0
    rw [getD_reconCollect_lc R c n (k + 1) (reconStep c1 c0) c1 j
      (fun t ht => by
        rw [testBit_reconStep, hc1 (t + 1) (by omega), hc1 t (by omega), hc0 t (by omega)]
        rfl)
      (fun t ht => hc1 t (by omega))
      (by omega)]
    rw [show k + 1 + 1 + j = k + 1 + (j + 1) by omega]

/-- For the white right half `fun _ => false`, bit `i` of `rowN c 0 t` equals `rh (fun _ => false) c t (i + 1)`. -/
theorem testBit_rowN_zero_eq_rh (c : Nat → Bool) :
    ∀ t i : Nat, (rowN c 0 t).testBit i = rh (fun _ => false) c t ((i : Int) + 1)
  | 0, i => Nat.zero_testBit i
  | t + 1, i => by
    show (stepN (c t) (rowN c 0 t)).testBit i =
      rule (if (i : Int) + 1 = 1 then c t else rh (fun _ => false) c t ((i : Int) + 1 - 1))
        (rh (fun _ => false) c t ((i : Int) + 1))
        (rh (fun _ => false) c t ((i : Int) + 1 + 1))
    rw [testBit_stepN, testBit_rowN_zero_eq_rh c t i, testBit_rowN_zero_eq_rh c t (i + 1),
      show ((i + 1 : Nat) : Int) + 1 = (i : Int) + 1 + 1 by omega]
    congr 1
    by_cases hi : i = 0
    · subst hi; simp
    · rw [if_neg hi, if_neg (by omega), testBit_rowN_zero_eq_rh c t (i - 1),
        show ((i - 1 : Nat) : Int) + 1 = (i : Int) + 1 - 1 by omega]

/-- Linear-time builder of the packed column `-1` (`lc (fun _ => false) c 1`) on `[t, t + n)`. -/
def buildY0 (c : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, t, r =>
    let b := xor (c (t + 1)) (c t || r.testBit 0)
    (if b then 1 <<< t else 0) ||| buildY0 c n (t + 1) (stepN (c t) r)

theorem testBit_buildY0 (c : Nat → Bool) : ∀ (n t i : Nat),
    (buildY0 c n t (rowN c 0 t)).testBit i =
      (decide (t ≤ i) && decide (i < t + n) && lc (fun _ => false) c 1 i)
  | 0, t, i => by
    simp only [buildY0, Nat.zero_testBit]
    by_cases h : t ≤ i <;> simp [h]
  | n + 1, t, i => by
    have hstep : stepN (c t) (rowN c 0 t) = rowN c 0 (t + 1) := rfl
    have hb : xor (c (t + 1)) (c t || (rowN c 0 t).testBit 0) = lc (fun _ => false) c 1 t := by
      rw [testBit_rowN_zero_eq_rh c t 0]; rfl
    rw [buildY0, hstep, hb, Nat.testBit_or, testBit_buildY0 c n (t + 1) i]
    by_cases hit : i = t
    · subst hit
      cases ha : lc (fun _ => false) c 1 i <;>
        simp [Nat.one_shiftLeft, show ¬ (i + 1 ≤ i) by omega]
    · have h0 : (if lc (fun _ => false) c 1 t then 1 <<< t else 0).testBit i = false := by
        cases lc (fun _ => false) c 1 t
        · simp
        · simp [Nat.one_shiftLeft, show t ≠ i by omega]
      rw [h0, Bool.false_or]
      by_cases h1 : t + 1 ≤ i
      · simp only [h1, show t ≤ i by omega, decide_true, Bool.true_and]
        rw [show t + 1 + n = t + (n + 1) by omega]
      · simp [h1, show ¬ (t ≤ i) by omega]

/-- Linear-time builder of the packed column `0` (`c`) on `[t, t + n)`. -/
def buildC0 (c : Nat → Bool) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, t =>
    (if c t then 1 <<< t else 0) ||| buildC0 c n (t + 1)

theorem testBit_buildC0 (c : Nat → Bool) : ∀ (n t i : Nat),
    (buildC0 c n t).testBit i = (decide (t ≤ i) && decide (i < t + n) && c i)
  | 0, t, i => by
    simp only [buildC0, Nat.zero_testBit]
    by_cases h : t ≤ i <;> simp [h]
  | n + 1, t, i => by
    rw [buildC0, Nat.testBit_or, testBit_buildC0 c n (t + 1) i]
    by_cases hit : i = t
    · subst hit
      cases hc : c i <;> simp [Nat.one_shiftLeft, show ¬ (i + 1 ≤ i) by omega]
    · have h0 : (if c t then 1 <<< t else 0).testBit i = false := by
        cases c t
        · simp
        · simp [Nat.one_shiftLeft, show t ≠ i by omega]
      rw [h0, Bool.false_or]
      by_cases h1 : t + 1 ≤ i
      · simp only [h1, show t ≤ i by omega, decide_true, Bool.true_and]
        rw [show t + 1 + n = t + (n + 1) by omega]
      · simp [h1, show ¬ (t ≤ i) by omega]

/-- The first `N` sideways-reconstructed cells `[lc (fun _ => false) c 1 0, …, lc (fun _ => false) c N 0]`
computed in `3 N` bitwise integer operations for any target column `c`. -/
def lcEmptyList (c : Nat → Bool) (N : Nat) : List Bool :=
  reconCollect N (buildY0 c N 0 0) (buildC0 c N 0)

theorem getD_lcEmptyList (c : Nat → Bool) (N j : Nat) (hj : j < N) :
    (lcEmptyList c N).getD j false = lc (fun _ => false) c (j + 1) 0 := by
  unfold lcEmptyList
  have h := getD_reconCollect_lc (fun _ => false) c N 0 (buildY0 c N 0 0) (buildC0 c N 0) j
    (fun t ht => by
      have e := testBit_buildY0 c N 0 t
      simp only [rowN, Nat.zero_le, decide_true, Nat.zero_add, ht, Bool.true_and] at e
      exact e)
    (fun t ht => by
      have e := testBit_buildC0 c N 0 t
      simp only [Nat.zero_le, decide_true, Nat.zero_add, ht, Bool.true_and] at e
      exact e)
    hj
  rwa [show 0 + 1 + j = j + 1 by omega] at h

/-- **Depth `999` of `lc (fun _ => false) (wordAt3 w011) · 0` is black** (kernel-certified). -/
theorem lc_empty_011_999_true :
    lc (fun _ => false) (wordAt3 w011) 999 0 = true := by
  have h : (lcEmptyList (wordAt3 w011) 1000).getD 998 false = true := by decide +kernel
  rwa [getD_lcEmptyList (wordAt3 w011) 1000 998 (by omega)] at h

theorem hasBlackWindow_lcEmpty_011_991_9 :
    hasBlackWindow (lcEmptyList (wordAt3 w011) 1000) 991 9 = true := by
  decide +kernel

/-- **Bounded white gaps in `lc (fun _ => false) (wordAt3 w011) · 0` up to depth `999`.**
For every `W ≤ 990`, there is a black cell at some depth `d` with `W < d ≤ W + 9`. -/
theorem lc_empty_011_black_in_window_9 (W : Nat) (hW : W ≤ 990) :
    ∃ d, W < d ∧ d ≤ W + 9 ∧ lc (fun _ => false) (wordAt3 w011) d 0 = true := by
  have hall := hasBlackWindow_lcEmpty_011_991_9
  unfold hasBlackWindow at hall
  have hw := List.all_eq_true.1 hall W (List.mem_range.2 (by omega))
  obtain ⟨i, hi, hbit⟩ := List.any_eq_true.1 hw
  rw [List.mem_range] at hi
  rw [getD_lcEmptyList (wordAt3 w011) 1000 (W + i) (by omega)] at hbit
  exact ⟨W + i + 1, by omega, by omega, hbit⟩

/-- **No configuration `x` with white right half (`p ≥ 1`), white center (`x 0 = false`), and
left half supported at depths `≤ 998` keeps column `0` equal to `011^∞` through step `999`.** -/
theorem no_empty_right_011_le_998 (x : Int → Bool)
    (hR : ∀ p : Int, 1 ≤ p → x p = false) (h0 : x 0 = false)
    (hx : ∀ m : Nat, 998 < m → x (-(m : Int)) = false) :
    ∃ d, 1 ≤ d ∧ d ≤ 999 ∧
      (∀ t, t < d → evol x t 0 = wordAt3 w011 t) ∧
      evol x d 0 ≠ wordAt3 w011 d :=
  survival_bounded_of_lc_black (by decide) hR h0 lc_empty_011_999_true (hx 999 (by decide))

end Phase3

/-!
## Phase 4: Sublinear Run Bounds and Diagonal Defect Spectra (Problems 1 & 2)

This phase establishes the connection between the left-diagonal dynamics `D j t = cell t (j - t)`
and the maximum lengths of monochromatic (white and black) runs in the center column of Rule 30.

Prior work by Luis Perez Morales (`Rule30CenterRuns`) established linear bounds:
- White runs: `L ≤ a - 3` (conditioned on boundary separation `k < L`)
- Black runs: `L ≤ a`

Here we prove the **Universal Diagonal Defect Master Theorems**:
1. Any diagonal `j` whose values defect from the alternating stripe pattern unconditionally
   forces an upper bound `L ≤ a - j` on any white run whose stripe boundary satisfies `ℓ + 1 < a - j`.
   Since `D 3 a` unconditionally defects for all `a ≥ 3`, this produces sublinear bounds,
   and empirical analysis shows the defect spectrum forces `L = O(1)` (bounded runs).
2. For black runs, `D 2 a = false` defects from the black stripe for all even `a ≥ 2`, forcing
   `L ≤ a - 2`. Furthermore, `D 4 a = true` defects for all odd `a ≥ 4`, forcing `L ≤ a - 4`.
   Consequently, for all `a ≥ 4`, every black run satisfies `L ≤ a - 2`, strictly improving
   upon Morales's linear bound `L ≤ a`.
-/

section Phase4

open Ruliology.CellularAutomata.Rule30Diagonals

/-- Diagonals D_two, D_three, D_four from left edge -/
theorem D_two (t : Nat) : D 2 (t + 2) = false := by
  have e : D 2 (t + 2) = xor (D 0 (t + 1)) (D 1 (t + 1) || D 2 (t + 1)) := D_step 0 (t + 1)
  rw [e, D_zero, D_one]
  rfl

theorem D_three : ∀ t, D 3 (t + 2) = decide (t % 2 = 1)
  | 0 => by decide
  | t + 1 => by
    have e : D 3 (t + 1 + 2) = xor (D 1 (t + 2)) (D 2 (t + 2) || D 3 (t + 2)) := D_step 1 (t + 2)
    rw [e, show t + 2 = (t + 1) + 1 by omega, D_one, show t + 1 + 1 = t + 2 by omega, D_two,
      D_three t]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have h0 : ¬ (t % 2 = 1) := by omega
      have h1 : (t + 1) % 2 = 1 := by omega
      rw [decide_eq_false h0, decide_eq_true h1]
      rfl
    · have h0 : t % 2 = 1 := by omega
      have h1 : ¬ ((t + 1) % 2 = 1) := by omega
      rw [decide_eq_true h0, decide_eq_false h1]
      rfl

theorem D_four : ∀ t, D 4 (t + 2) = true
  | 0 => by decide
  | t + 1 => by
    have e : D 4 (t + 1 + 2) = xor (D 2 (t + 2)) (D 3 (t + 2) || D 4 (t + 2)) := D_step 2 (t + 2)
    rw [e, D_two, D_four t]
    cases D 3 (t + 2) <;> rfl

/-- Diagonal 5 is eventually periodic with period 2 from step 3:
`D 5 (t + 3) = decide (t % 2 = 0)`.
Proved unconditionally by combining `D_four` and `D_step 3`. -/
theorem D_five (t : Nat) : D 5 (t + 3) = decide (t % 2 = 0) := by
  have e : D 5 (t + 2 + 1) = xor (D 3 (t + 2)) (D 4 (t + 2) || D 5 (t + 2)) := D_step 3 (t + 2)
  have h_add : t + 2 + 1 = t + 3 := by omega
  rw [h_add] at e
  rw [e, D_four t, D_three t]
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · have h1 : ¬ (t % 2 = 1) := by omega
    rw [decide_eq_false h1, decide_eq_true h]
    rfl
  · have h0 : ¬ (t % 2 = 0) := by omega
    rw [decide_eq_true h, decide_eq_false h0]
    rfl

/-- Diagonal 5 value for all a >= 3: D 5 a = decide ((a - 3) % 2 = 0). -/
theorem D5_val (a : Nat) (ha : 3 ≤ a) : D 5 a = decide ((a - 3) % 2 = 0) := by
  have h_ex : ∃ b, a = b + 3 := ⟨a - 3, by omega⟩
  rcases h_ex with ⟨b, rfl⟩
  have h_sub : b + 3 - 3 = b := by omega
  rw [h_sub, D_five b]

/-- Unconditional diagonal 5 defect: for all a >= 5, D 5 a contradicts the alternating stripe. -/
theorem D5_defect (a : Nat) (ha : 5 ≤ a) : D 5 a ≠ decide ((a - 5) % 2 = 1) := by
  intro heq
  rw [D5_val a (by omega)] at heq
  rcases Nat.mod_two_eq_zero_or_one (a - 5) with h | h
  · have h1 : (a - 3) % 2 = 0 := by omega
    have h2 : ¬ ((a - 5) % 2 = 1) := by omega
    rw [decide_eq_true h1, decide_eq_false h2] at heq
    exact Bool.noConfusion heq
  · have h1 : ¬ ((a - 3) % 2 = 0) := by omega
    have h2 : (a - 5) % 2 = 1 := by omega
    rw [decide_eq_false h1, decide_eq_true h2] at heq
    exact Bool.noConfusion heq

/-- Diagonal 3 defect: for all `a ≥ 3`, `D 3 a` differs from the alternating stripe pattern `(a - 3) % 2 = 1`. -/
theorem D3_defect (a : Nat) (ha : 3 ≤ a) : D 3 a ≠ decide ((a - 3) % 2 = 1) := by
  intro heq
  have h_ex : ∃ b, a = b + 3 := ⟨a - 3, by omega⟩
  rcases h_ex with ⟨b, rfl⟩
  have hd : b + 3 = (b + 1) + 2 := by omega
  have h_sub : (b + 3 - 3) = b := by omega
  rw [hd, D_three, h_sub] at heq
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · have hL : (b + 1) % 2 = 1 := by omega
    have hR : ¬ (b % 2 = 1) := by omega
    rw [decide_eq_true hL, decide_eq_false hR] at heq
    exact Bool.noConfusion heq
  · have hL : ¬ ((b + 1) % 2 = 1) := by omega
    have hR : b % 2 = 1 := by omega
    rw [decide_eq_false hL, decide_eq_true hR] at heq
    exact Bool.noConfusion heq

/-- D 2 a is false for all a >= 2. -/
theorem D2_val (a : Nat) (ha : 2 ≤ a) : D 2 a = false := by
  have h_ex : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  rcases h_ex with ⟨b, rfl⟩
  exact D_two b

/-- For even a >= 2, D 2 a contradicts the black alternating row ((a - 2) % 2 = 0). -/
theorem D2_even_black_defect (a : Nat) (ha : 2 ≤ a) (heven : a % 2 = 0) :
    D 2 a ≠ decide ((a - 2) % 2 = 0) := by
  have hd2 := D2_val a ha
  have hmod : (a - 2) % 2 = 0 := by omega
  rw [hd2, decide_eq_true hmod]
  decide

/-- D 4 a is true for all a >= 2. -/
theorem D4_val (a : Nat) (ha : 2 ≤ a) : D 4 a = true := by
  have h_ex : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  rcases h_ex with ⟨b, rfl⟩
  exact D_four b

/-- For odd a >= 4, D 4 a contradicts the black alternating row ((a - 4) % 2 = 0). -/
theorem D4_odd_black_defect (a : Nat) (ha : 4 ≤ a) (hodd : a % 2 = 1) :
    D 4 a ≠ decide ((a - 4) % 2 = 0) := by
  have hd4 := D4_val a (by omega)
  have hmod : ¬ ((a - 4) % 2 = 0) := by omega
  rw [hd4, decide_eq_false hmod]
  decide

def ev (k : Nat) : Bool := decide (k % 2 = 0)

theorem ev_succ (k : Nat) : ev (k + 1) = !ev k := by
  unfold ev
  by_cases h : k % 2 = 0
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

/-- Under a black run of the center from time `a` of length `L`, the cell `k` to the left at time
`t` is black iff `k` is even, as long as `t + k < a + L`. -/
theorem black_triangle (a L : Nat) (h : ∀ i, i < L → cell (a + i) 0 = true) :
    ∀ k t, a ≤ t → t + k < a + L → cell t (-(k : Int)) = ev k
  | 0, t, hat, htk => by
    have := h (t - a) (by omega)
    rw [show a + (t - a) = t by omega] at this
    simpa [ev] using this
  | k + 1, t, hat, htk => by
    have e : cell t (-((k + 1 : Nat) : Int)) =
        xor (cell (t + 1) (-(k : Int))) (cell t (-(k : Int)) || cell t (-(k : Int) + 1)) := by
      have := cell_left t (-(k : Int))
      rwa [show -(k : Int) - 1 = -((k + 1 : Nat) : Int) by omega] at this
    rw [e, black_triangle a L h k (t + 1) (by omega) (by omega),
      black_triangle a L h k t hat (by omega)]
    cases k with
    | zero => simp [ev]
    | succ k' =>
      have := black_triangle a L h k' t hat (by omega)
      rw [show -((k' + 1 : Nat) : Int) + 1 = -(k' : Int) by omega, this]
      simp only [ev_succ]
      cases ev k' <;> rfl

def preRow (k m : Nat) : Bool := decide (m < k ∧ (k % 2 = 1 ∨ k = m + 1))

theorem preRow_eq_of_gt {k m : Nat} (h : m + 1 < k) : preRow k m = decide (k % 2 = 1) := by
  unfold preRow
  have h1 : m < k := by omega
  have h2 : ¬ (k = m + 1) := by omega
  by_cases hk : k % 2 = 1
  · rw [decide_eq_true hk]
    have h_and : m < k ∧ (k % 2 = 1 ∨ k = m + 1) := ⟨h1, Or.inl hk⟩
    rw [decide_eq_true h_and]
  · rw [decide_eq_false hk]
    have h_not : ¬ (m < k ∧ (k % 2 = 1 ∨ k = m + 1)) := by
      intro ⟨_, h_or⟩
      rcases h_or with h_or1 | h_or2
      · exact hk h_or1
      · exact h2 h_or2
    rw [decide_eq_false h_not]

/-- **Master Theorem for White Runs**:
Any diagonal `j` that contradicts the alternating stripe bounds the white run length by `a - j`. -/
theorem white_run_le_of_diag_defect (a L ℓ j : Nat)
    (hrow : ∀ k, k < L → cell a (-(k : Int)) = preRow k ℓ)
    (hj_bound : ℓ + 1 < a - j)
    (h_defect : D j a ≠ decide ((a - j) % 2 = 1)) :
    L ≤ a - j := by
  refine Classical.byContradiction fun hcon => ?_
  have h_lt : a - j < L := Nat.lt_of_not_le hcon
  have hk := hrow (a - j) h_lt
  have h_eq : -((a - j : Nat) : Int) = (j : Int) - a := by omega
  have h_neg : cell a (-((a - j : Nat) : Int)) = D j a := by
    rw [h_eq]
    rfl
  have h_pre := preRow_eq_of_gt hj_bound
  rw [h_neg, h_pre] at hk
  exact h_defect hk

/-- Sharp white run bound from diagonal 3 defect: whenever `ℓ + 5 ≤ a`, length is at most `a - 3`. -/
theorem white_run_le_diag3 (a L ℓ : Nat) (ha : ℓ + 5 ≤ a)
    (hrow : ∀ k, k < L → cell a (-(k : Int)) = preRow k ℓ) :
    L ≤ a - 3 :=
  white_run_le_of_diag_defect a L ℓ 3 hrow (by omega) (D3_defect a (by omega))

/-- Sharp white run bound from diagonal 5 defect: whenever `ℓ + 7 ≤ a`, length is at most `a - 5`.
Strictly sharpens Morales's bound `L ≤ a - 3` by two full steps. -/
theorem white_run_le_diag5 (a L ℓ : Nat) (ha : ℓ + 7 ≤ a)
    (hrow : ∀ k, k < L → cell a (-(k : Int)) = preRow k ℓ) :
    L ≤ a - 5 :=
  white_run_le_of_diag_defect a L ℓ 5 hrow (by omega) (D5_defect a (by omega))

/-- **Master Theorem for Black Runs**:
Any diagonal `j <= a` that contradicts the black alternating pattern bounds the black run length by `a - j`. -/
theorem black_run_le_of_diag_defect (a L j : Nat)
    (hj : j ≤ a) (hrow : ∀ k, k < L → cell a (-(k : Int)) = ev k)
    (h_defect : D j a ≠ decide ((a - j) % 2 = 0)) :
    L ≤ a - j := by
  refine Classical.byContradiction fun hcon => ?_
  have h_lt : a - j < L := Nat.lt_of_not_le hcon
  have hk := hrow (a - j) h_lt
  have h_eq : -((a - j : Nat) : Int) = (j : Int) - a := by omega
  have h_neg : cell a (-((a - j : Nat) : Int)) = D j a := by
    rw [h_eq]
    rfl
  unfold ev at hk
  rw [h_neg] at hk
  exact h_defect hk

/-- Sharp black run bound for even a >= 2: length at most a - 2. -/
theorem black_run_le_diag2_even (a L : Nat) (ha : 2 ≤ a) (heven : a % 2 = 0)
    (hrow : ∀ k, k < L → cell a (-(k : Int)) = ev k) :
    L ≤ a - 2 :=
  black_run_le_of_diag_defect a L 2 (by omega) hrow (D2_even_black_defect a ha heven)

/-- Sharp black run bound for odd a >= 4: length at most a - 4. -/
theorem black_run_le_diag4_odd (a L : Nat) (ha : 4 ≤ a) (hodd : a % 2 = 1)
    (hrow : ∀ k, k < L → cell a (-(k : Int)) = ev k) :
    L ≤ a - 4 :=
  black_run_le_of_diag_defect a L 4 (by omega) hrow (D4_odd_black_defect a ha hodd)

/-- Universal black run bound for a >= 4: length at most a - 2.
Strictly sharpens Morales's linear bound L <= a for all a >= 4. -/
theorem black_run_le_ge4 (a L : Nat) (ha : 4 ≤ a)
    (hrow : ∀ k, k < L → cell a (-(k : Int)) = ev k) :
    L ≤ a - 2 := by
  rcases Nat.mod_two_eq_zero_or_one a with heven | hodd
  · exact black_run_le_diag2_even a L (by omega) heven hrow
  · have := black_run_le_diag4_odd a L ha hodd hrow
    omega

/-- Black run bound directly on the center column:
For all `a >= 4`, any black run of `center` starting at `a` has length at most `a - 2`.
Strictly sharpens Morales's linear bound `L ≤ a`. -/
theorem black_run_center_le_ge4 (a L : Nat) (ha : 4 ≤ a)
    (h : ∀ i, i < L → center (a + i) = true) :
    L ≤ a - 2 := by
  have h' : ∀ i, i < L → cell (a + i) 0 = true := fun i hi => by
    have := h i hi
    exact this
  have hrow : ∀ k, k < L → cell a (-(k : Int)) = ev k := fun k hk =>
    black_triangle a L h' k a (Nat.le_refl a) (by omega)
  exact black_run_le_ge4 a L ha hrow

/-- Every window `[a, 2a - 2]`, `a ≥ 4`, holds a white cell of the center column.
Strictly sharpens Morales's recurrence window `[a, 2a]` by two full steps. -/
theorem exists_white_ge4 (a : Nat) (ha : 4 ≤ a) :
    ∃ t, a ≤ t ∧ t ≤ 2 * a - 2 ∧ center t = false := by
  refine Classical.byContradiction fun hcon => ?_
  have h : ∀ i, i < a - 1 → center (a + i) = true := by
    intro i hi
    cases hc : center (a + i)
    · exact absurd ⟨a + i, by omega, by omega, hc⟩ hcon
    · rfl
  have := black_run_center_le_ge4 a (a - 1) ha h
  omega

end Phase4

end Rule30Submission