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


end Phase2
end Rule30Submission
