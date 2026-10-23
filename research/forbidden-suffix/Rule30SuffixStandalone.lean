import Ruliology.CellularAutomata.Rule30StripCertificates
import Ruliology.CellularAutomata.Rule30FiniteMaskedJen
import Ruliology.CellularAutomata.Rule30FiniteBlackRuns
import Ruliology.CellularAutomata.Rule30LightCone

/- Source: lean/Ruliology/CellularAutomata/Rule30FiniteStripsResearch.lean -/
/-!
# Bitmask strip certificates for arbitrary left-finite configurations

The certificate checker has no initial-state dependence. Its soundness extends
from the single seed to every column of any configuration with a leftmost
black cell, by the existing uniform masked Jen theorem. In particular every
concrete bitmask certificate in the catalog has this stronger conclusion.
-/

namespace Ruliology.CellularAutomata
namespace Rule30FiniteStripsResearch

open Rule30Jen Rule30Realization Rule30FiniteConfigs Rule30StripCertificates

/-- Column i eventually reads the nonempty word w, starting at an arbitrary transient. -/
def EventuallyWord (x : Int → Bool) (i : Int) (w : List Bool) : Prop :=
  ∃ T, ∀ t, T ≤ t → evol x t i = w.getD ((t - T) % w.length) false

/-- Strip encoding: `r < 2 ^ K` and bit `k < K` of `r` is `evol x t (j + 1 + k)`. -/
def Enc (x : Int → Bool) (K t : Nat) (j : Int) (r : Nat) : Prop :=
  r < 2 ^ K ∧ ∀ k, k < K → r.testBit k = evol x t (j + 1 + k)

theorem enc_step {x : Int → Bool} {K t : Nat} {j : Int} {r : Nat} (h : Enc x K t j r) :
    Enc x K (t + 1) j (stripStep K (evol x t j) (evol x t (j + 1 + K)) r) := by
  refine ⟨stripStep_lt _ _ _ _, fun k hk => ?_⟩
  rw [testBit_stripStep K _ _ r h.1 k hk]
  show _ = rule (evol x t (j + 1 + (k : Int) - 1)) (evol x t (j + 1 + k)) (evol x t (j + 1 + k + 1))
  have hc : r.testBit k = evol x t (j + 1 + k) := h.2 k hk
  have hl : (if k = 0 then evol x t j else r.testBit (k - 1)) = evol x t (j + 1 + (k : Int) - 1) := by
    split
    · rename_i h0; subst h0; congr 1; omega
    · rename_i h0; rw [h.2 (k - 1) (by omega)]; congr 1; omega
  have hr : (if k + 1 = K then evol x t (j + 1 + K) else r.testBit (k + 1)) =
      evol x t (j + 1 + k + 1) := by
    split
    · rename_i h1; congr 1; omega
    · rename_i h1; rw [h.2 (k + 1) (by omega)]; congr 1; omega
  rw [hl, hc, hr]

/-- The encoding of the actual strip. -/
def encRow (x : Int → Bool) (t : Nat) (j : Int) : Nat → Nat
  | 0 => 0
  | K + 1 => encRow x t j K ||| ((evol x t (j + 1 + K)).toNat <<< K)

theorem testBit_encRow {x : Int → Bool} (t : Nat) (j : Int) :
    ∀ K k, (encRow x t j K).testBit k = (decide (k < K) && evol x t (j + 1 + k))
  | 0, k => by simp [encRow]
  | K + 1, k => by
    rw [encRow, Nat.testBit_or, testBit_encRow t j K k, Nat.testBit_shiftLeft, testBit_toNat]
    by_cases hk : k < K
    · simp [hk, show k < K + 1 by omega, show ¬ K ≤ k by omega]
    · by_cases hk' : k = K
      · subst hk'; simp
      · simp [hk, show ¬ k < K + 1 by omega, show k - K ≠ 0 by omega]

theorem enc_encRow {x : Int → Bool} (K t : Nat) (j : Int) : Enc x K t j (encRow x t j K) := by
  refine ⟨Nat.lt_pow_two_of_testBit _ fun i hi => ?_, fun k hk => ?_⟩
  · rw [testBit_encRow]; simp [show ¬ i < K by omega]
  · rw [testBit_encRow]; simp [hk]

/-- **Soundness of the strip sets.** If the actual strip is in `S` at time `t` and column `j` carries
the word `u` from `t` on, the actual strip at time `t + u.length` is in `applyWord K u S`. -/
theorem enc_applyWord {x : Int → Bool} {K : Nat} {j : Int} :
    ∀ (u : List Bool) (t r S : Nat), Enc x K t j r → S.testBit r = true →
      (∀ s, s < u.length → evol x (t + s) j = u.getD s false) →
      ∃ r', Enc x K (t + u.length) j r' ∧ (applyWord K u S).testBit r' = true
  | [], t, r, S, he, hS, _ => ⟨r, he, hS⟩
  | a :: u, t, r, S, he, hS, hu => by
    have ha : evol x t j = a := by simpa using hu 0 (by simp)
    have he1 := enc_step he
    rw [ha] at he1
    have hS1 : (image K a S).testBit (stripStep K a (evol x t (j + 1 + K)) r) = true :=
      mem_imageAux hS _ (2 ^ K) he.1
    obtain ⟨r', he', hS'⟩ := enc_applyWord u (t + 1) _ _ he1 hS1 (fun s hs => by
      have := hu (s + 1) (by simp; omega)
      rw [show t + (s + 1) = t + 1 + s by omega] at this
      simpa using this)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (a :: u).length = t + 1 + u.length by simp; omega]
    exact he'

theorem enc_iterW {x : Int → Bool} {K : Nat} {j : Int} (w : List Bool) :
    ∀ (k t r S : Nat), Enc x K t j r → S.testBit r = true →
      (∀ m s, m < k → s < w.length → evol x (t + m * w.length + s) j = w.getD s false) →
      ∃ r', Enc x K (t + k * w.length) j r' ∧ (iterW K w k S).testBit r' = true
  | 0, t, r, S, he, hS, _ => ⟨r, by simpa using he, hS⟩
  | k + 1, t, r, S, he, hS, hw => by
    obtain ⟨r1, he1, hS1⟩ := enc_applyWord w t r S he hS (fun s hs => by
      simpa using hw 0 s (by omega) hs)
    obtain ⟨r', he', hS'⟩ := enc_iterW w k (t + w.length) r1 _ he1 hS1 (fun m s hm hs => by
      rw [show t + w.length + m * w.length + s = t + (m + 1) * w.length + s by
        rw [Nat.succ_mul]; omega]
      exact hw (m + 1) s (by omega) hs)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (k + 1) * w.length = t + w.length + k * w.length by rw [Nat.succ_mul]; omega]
    exact he'

/-- A bitmask strip certificate forces the effective right boundary to be eventually periodic,
in the evolution of an arbitrary configuration, provided column i reads w eventually. -/
theorem orCol_exact_period_of_word_strip {x : Int → Bool} (i : Int) (w : List Bool)
    (K k : Nat) (hK : 1 ≤ K) (hw : 0 < w.length)
    (hcert : stripCert w K k = true) (hword : EventuallyWord x i w) :
    ∃ T, ∀ t, T ≤ t →
      Rule30FiniteMaskedJen.orCol x i (t + w.length) = Rule30FiniteMaskedJen.orCol x i t := by
  obtain ⟨T, hT⟩ := hword
  unfold stripCert at hcert
  rw [Bool.and_eq_true] at hcert
  obtain ⟨hsub, hforce⟩ := hcert
  have hsub' := allBelow_spec hsub
  -- the driver is `w` on every period from `T`
  have hblock : ∀ m s, s < w.length → evol x (T + m * w.length + s) i = w.getD s false := by
    intro m s hs
    rw [hT _ (by omega), show T + m * w.length + s - T = s + m * w.length by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  let S0 := iterW K w k (fullSet K)
  -- after `k` periods the strip is in `S0`
  have hstart : ∃ r, Enc x K (T + k * w.length) i r ∧ S0.testBit r = true := by
    have h0 := enc_encRow (x := x) K T i
    have hfull : (fullSet K).testBit (encRow x T i K) = true := by
      unfold fullSet; rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true h0.1
    exact enc_iterW w k T _ _ h0 hfull (fun m s _ hs => hblock m s hs)
  -- and it stays in `S0` at every later period start
  have hinv : ∀ m, ∃ r, Enc x K (T + (k + m) * w.length) i r ∧ S0.testBit r = true := by
    intro m
    induction m with
    | zero => simpa using hstart
    | succ m ih =>
      obtain ⟨r, he, hS⟩ := ih
      obtain ⟨r', he', hS'⟩ := enc_applyWord w _ r S0 he hS (fun s hs => by
        rw [show T + (k + m) * w.length + s = T + (k + m) * w.length + s from rfl]
        exact hblock (k + m) s hs)
      refine ⟨r', ?_, ?_⟩
      · have hm : (k + (m + 1)) * w.length = (k + m) * w.length + w.length := by
          rw [show k + (m + 1) = (k + m) + 1 by omega, Nat.succ_mul]
        rw [hm, ← Nat.add_assoc]
        exact he'
      · have hlt : r' < 2 ^ K := he'.1
        have := hsub' r' hlt
        rw [hS', Bool.not_true, Bool.false_or] at this
        exact this
  -- the forced value at each white phase
  let g : Nat → Bool := fun φ => w.getD φ false ||
    !colConst K (applyWord K (w.take φ) S0) false
  have hform : ∀ t, T + k * w.length ≤ t → Rule30FiniteMaskedJen.orCol x i t = g ((t - T) % w.length) := by
    intro t ht
    have hφ : (t - T) % w.length < w.length := Nat.mod_lt _ hw
    have hdec : t = T + (k + ((t - T) / w.length - k)) * w.length + (t - T) % w.length := by
      have hd := Nat.div_add_mod (t - T) w.length
      have hq : k ≤ (t - T) / w.length := (Nat.le_div_iff_mul_le hw).2 (by omega)
      rw [show k + ((t - T) / w.length - k) = (t - T) / w.length by omega, Nat.mul_comm]
      omega
    obtain ⟨r, he, hS⟩ := hinv ((t - T) / w.length - k)
    obtain ⟨r', he', hS'⟩ := enc_applyWord (w.take ((t - T) % w.length)) _ r S0 he hS
      (fun s hs => by
        rw [List.length_take] at hs
        have hs' : s < (t - T) % w.length := by omega
        rw [hblock _ s (by omega)]
        simp [List.getD_eq_getElem?_getD, hs'])
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hφ), ← hdec] at he'
    have hcell : evol x t (i + 1) = r'.testBit 0 := by
      simpa using (he'.2 0 (by omega)).symm
    unfold Rule30FiniteMaskedJen.orCol g
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
  refine ⟨T + k * w.length, fun t ht => ?_⟩
  show Rule30FiniteMaskedJen.orCol x i (t + w.length) = Rule30FiniteMaskedJen.orCol x i t
  rw [hform t ht, hform (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
    Nat.add_mod_right]


/-- Eventual periodicity version of the exact-period implication. -/
theorem orCol_periodic_of_word_strip {x : Int → Bool} (i : Int) (w : List Bool)
    (K k : Nat) (hK : 1 ≤ K) (hw : 0 < w.length)
    (hcert : stripCert w K k = true) (hword : EventuallyWord x i w) :
    EventuallyPeriodic (Rule30FiniteMaskedJen.orCol x i) := by
  obtain ⟨T, hT⟩ := orCol_exact_period_of_word_strip i w K k hK hw hcert hword
  exact ⟨T, w.length, hw, hT⟩

/-- **Uniform strip soundness.** Every bitmask certificate excludes its word at every column
of every configuration having a leftmost black cell, for every transient. -/
theorem not_eventually_word_strip {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (i : Int)
    (w : List Bool) (K k : Nat) (hK : 1 ≤ K) (hw : 0 < w.length)
    (hcert : stripCert w K k = true) : ¬ EventuallyWord x i w := by
  intro hword
  have hcper : EventuallyPeriodic (fun t => evol x t i) := by
    obtain ⟨T, hT⟩ := hword
    refine ⟨T, w.length, hw, fun t ht => ?_⟩
    change evol x (t + w.length) i = evol x t i
    rw [hT t ht, hT (t + w.length) (by omega),
      show t + w.length - T = (t - T) + w.length by omega, Nat.add_mod_right]
  exact Rule30FiniteMaskedJen.orCol_not_eventuallyPeriodic hlo hzero i hcper
    (orCol_periodic_of_word_strip i w K k hK hw hcert hword)

/-- In particular, the certificate excludes the word in every column of every nonzero finite
configuration. Neither the column nor the transient is bounded. -/
theorem not_eventually_word_strip_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true) (i : Int)
    (w : List Bool) (K k : Nat) (hK : 1 ≤ K) (hw : 0 < w.length)
    (hcert : stripCert w K k = true) : ¬ EventuallyWord x i w := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact not_eventually_word_strip hlo hzero i w K k hK hw hcert


end Rule30FiniteStripsResearch
end Ruliology.CellularAutomata

/- Source: lean/Ruliology/CellularAutomata/Rule30WhitePaddingResearch.lean -/
/-!
# Pumping a white run in a Rule 30 strip certificate

Finite stabilization of three zero-driven reachable sets proves a strip certificate
for every sufficiently long white prefix, rather than just one finite word.
The checks and the pumping argument use the existing sound strip abstraction.
-/

namespace Ruliology.CellularAutomata.Rule30WhitePaddingResearch

open Rule30StripCertificates

def zeros (K n S : Nat) : Nat := applyWord K (List.replicate n false) S

def Forces (K S : Nat) : Bool := colConst K S false || colConst K S true

theorem applyWord_append (K : Nat) (u v : List Bool) (S : Nat) :
    applyWord K (u ++ v) S = applyWord K v (applyWord K u S) := by
  induction u generalizing S with
  | nil => rfl
  | cons a u ih => exact ih (image K a S)

theorem zeros_add (K a b S : Nat) : zeros K (a + b) S = zeros K b (zeros K a S) := by
  have hrep : List.replicate (a + b) false = List.replicate a false ++ List.replicate b false := by
    induction a with
    | zero => simp
    | succ a ih => simpa [Nat.succ_add, List.replicate_succ] using congrArg (false :: ·) ih
  unfold zeros
  rw [hrep, applyWord_append]

theorem zeros_succ (K n S : Nat) : zeros K (n + 1) S = image K false (zeros K n S) := by
  simpa [zeros, applyWord] using zeros_add K n 1 S

theorem zeros_stable (K N S : Nat)
    (h : zeros K (N + 1) S = zeros K N S) :
    ∀ r, N ≤ r → zeros K r S = zeros K N S := by
  intro r hr
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show N + (d + 1) = (N + d) + 1 by omega, zeros_succ, ih (by omega)]
    exact (zeros_succ K N S).symm.trans h

/-- A finite check for the family `0^r u`, for all `r ≥ N`.
Two periods reach `S2`; the three zero-driven sets stabilize by `N`.
The white-phase forcing checks cover the finite prefix, the stable zero tail,
and the finitely many phases of `u`. -/
theorem padding_strip (u : List Bool) (K N S1 S2 : Nat)
    (hS1 : applyWord K u (zeros K N (fullSet K)) = S1)
    (hS2 : applyWord K u (zeros K N S1) = S2)
    (h0 : zeros K (N + 1) (fullSet K) = zeros K N (fullSet K))
    (h1 : zeros K (N + 1) S1 = zeros K N S1)
    (h2 : zeros K (N + 1) S2 = zeros K N S2)
    (hret : subsetB K (applyWord K u (zeros K N S2)) S2 = true)
    (hpref : (List.range (N + 1)).all (fun j => Forces K (zeros K j S2)) = true)
    (htail : (List.range u.length).all (fun j =>
      u.getD j false || Forces K (applyWord K (u.take j) (zeros K N S2))) = true)
    (r : Nat) (hr : N ≤ r) :
    stripCert (List.replicate r false ++ u) K 2 = true := by
  let w := List.replicate r false ++ u
  have hpump (S : Nat) (hs : zeros K (N + 1) S = zeros K N S) :
      applyWord K w S = applyWord K u (zeros K N S) := by
    rw [show w = List.replicate r false ++ u from rfl, applyWord_append]
    rw [← zeros, zeros_stable K N S hs r hr]
  have hreach : iterW K w 2 (fullSet K) = S2 := by
    simp only [iterW]
    rw [hpump _ h0, hS1, hpump _ h1, hS2]
  change stripCert w K 2 = true
  unfold stripCert
  rw [hreach, Bool.and_eq_true]
  refine ⟨?_, List.all_eq_true.mpr ?_⟩
  · rw [hpump _ h2]
    exact hret
  · intro j hj
    have hjlt : j < r + u.length := by simpa [w] using List.mem_range.mp hj
    by_cases hjr : j < r
    · have hwj : w.getD j false = false := by
        change (List.replicate r false ++ u).getD j false = false
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_left (l₁ := List.replicate r false) (l₂ := u) (by simpa using hjr)]
        simp [List.getElem?_replicate_of_lt hjr]
      have htake : w.take j = List.replicate j false := by
        rw [List.take_append_of_le_length (by simpa using Nat.le_of_lt hjr)]
        simp [Nat.min_eq_left (Nat.le_of_lt hjr)]
      rw [hwj, Bool.false_or, htake]
      change Forces K (zeros K j S2) = true
      by_cases hjN : j ≤ N
      · exact List.all_eq_true.mp hpref j (List.mem_range.mpr (by omega))
      · rw [zeros_stable K N S2 h2 j (by omega)]
        exact List.all_eq_true.mp hpref N (List.mem_range.mpr (by omega))
    · have hrj : r ≤ j := by omega
      have hju : j - r < u.length := by omega
      have hwj : w.getD j false = u.getD (j - r) false := by
        change (List.replicate r false ++ u).getD j false = u.getD (j - r) false
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (l₁ := List.replicate r false) (l₂ := u) (by simpa using hrj)]
        simp [List.getD_eq_getElem?_getD]
      have htake : w.take j = List.replicate r false ++ u.take (j - r) := by
        simpa [w, show r + (j - r) = j by omega] using
          (List.take_length_add_append (l₁ := List.replicate r false) (l₂ := u) (j - r))
      rw [hwj, htake, applyWord_append, ← zeros, zeros_stable K N S2 h2 r hr]
      simpa only [Forces, Bool.or_assoc] using
        List.all_eq_true.mp htail (j - r) (List.mem_range.mpr hju)

/-- Every word in a finitely checked white-padding family is excluded forever. -/
theorem no_padding_word (u : List Bool) (K N S1 S2 : Nat)
    (hS1 : applyWord K u (zeros K N (fullSet K)) = S1)
    (hS2 : applyWord K u (zeros K N S1) = S2)
    (h0 : zeros K (N + 1) (fullSet K) = zeros K N (fullSet K))
    (h1 : zeros K (N + 1) S1 = zeros K N S1)
    (h2 : zeros K (N + 1) S2 = zeros K N S2)
    (hret : subsetB K (applyWord K u (zeros K N S2)) S2 = true)
    (hpref : (List.range (N + 1)).all (fun j => Forces K (zeros K j S2)) = true)
    (htail : (List.range u.length).all (fun j =>
      u.getD j false || Forces K (applyWord K (u.take j) (zeros K N S2))) = true)
    (hK : 1 ≤ K) (hN : 0 < N) (r : Nat) (hr : N ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ u) := by
  exact not_eventually_word_strip _ K 2 hK (by simp; omega)
    (padding_strip u K N S1 S2 hS1 hS2 h0 h1 h2 hret hpref htail r hr)

end Ruliology.CellularAutomata.Rule30WhitePaddingResearch

/- Source: lean/Ruliology/CellularAutomata/Rule30WhitePulseResearch.lean -/
/-!
# A shield survives every short pulse

A black run in the first right column creates a striped block. An interior black
cell of that block survives an arbitrary boundary pulse of length m by locality.
These lemmas quantify the absorbing, synchronized regime without enumerating tails.
They do not prove every periodic history enters that regime.
-/
namespace Ruliology.CellularAutomata.Rule30WhitePulseResearch
open Rule30Jen Rule30Realization Rule30FiniteBlackRuns Rule30ZeroBoundaryBarriers

/-- A spatially stationary stripe, black at odd offsets from column i. -/
def stripe (i p : Int) : Bool := decide ((p - i) % 2 = 1)

theorem stripe_step (i p : Int) :
    rule (stripe i (p - 1)) (stripe i p) (stripe i (p + 1)) = stripe i p := by
  have hp : (p - i) % 2 = 0 ∨ (p - i) % 2 = 1 := by omega
  rcases hp with hp | hp
  · have hl : (p - 1 - i) % 2 = 1 := by omega
    have hr : (p + 1 - i) % 2 = 1 := by omega
    simp [stripe, rule, hp, hl, hr]
  · have hl : (p - 1 - i) % 2 = 0 := by omega
    have hr : (p + 1 - i) % 2 = 0 := by omega
    simp [stripe, rule, hp, hl, hr]

theorem evol_stripe (i : Int) : ∀ t p, evol (stripe i) t p = stripe i p
  | 0, p => rfl
  | t+1, p => by
    change rule (evol (stripe i) t (p-1)) (evol (stripe i) t p)
      (evol (stripe i) t (p+1)) = stripe i p
    rw [evol_stripe i t (p-1), evol_stripe i t p, evol_stripe i t (p+1), stripe_step]

/-- The nine-black shield is a whole stripe on its forced interval. -/
theorem shield_stripe (x : Int → Bool) (i : Int) (a j : Nat)
    (hblack : ∀ s, s < 9*j → evol x (a+s) (i+1) = true)
    (p : Int) (hlo : i+2 ≤ p) (hhi : p ≤ i+2*j+1) :
    evol x (a+9*j) p = stripe i p := by
  have hs := black_shield x (i+1) j a hblack
  let k : Nat := ((p-i)/2).toNat
  have hk : (k : Int) = (p-i)/2 := by
    dsimp [k]
    exact Int.toNat_of_nonneg (by omega)
  have hklo : 1 ≤ k := by omega
  have hkhi : k ≤ j := by omega
  have hp : (p-i)%2 = 0 ∨ (p-i)%2 = 1 := by omega
  rcases hp with hp | hp
  · have he : p = (i+1)+2*(k:Int)-1 := by omega
    rw [he, (hs k hklo hkhi).1]
    simp [stripe, show ((i+1)+2*(k:Int)-1-i)%2 = 0 by omega]
  · have he : p = (i+1)+2*(k:Int) := by omega
    rw [he, (hs k hklo hkhi).2]
    simp [stripe, show ((i+1)+2*(k:Int)-i)%2 = 1 by omega]

/-- **An arbitrary m-step pulse cannot erase the entire shield.** After 9(m+1) black steps
of column i+1, a black cell survives any following m steps at an explicitly bounded distance.
There is no hypothesis on the boundary column during those m steps. -/
theorem black_survives_pulse (x : Int → Bool) (i : Int) (a m : Nat)
    (hblack : ∀ s, s < 9*(m+1) → evol x (a+s) (i+1) = true) :
    evol x (a+9*(m+1)+m) (i+(2*(m/2)+3 : Nat)) = true := by
  let q : Nat := 2*(m/2)+3
  have hqlo : m+2 ≤ q := by dsimp [q]; omega
  have hqhi : q ≤ m+3 := by dsimp [q]; omega
  have hloc := Rule30LightCone.evol_window (x := stripe i)
    (x' := fun p => evol x (a+9*(m+1)) p) (t := m) (p := i+q)
    (fun p hp1 hp2 => shield_stripe x i a (m+1) hblack p (by omega) (by omega))
  rw [evol_restart, evol_stripe] at hloc
  rw [hloc]
  simp only [stripe, decide_eq_true_eq]
  dsimp [q]
  omega

/-- During n white boundary steps, any black cell initially n+1 places to the right forces
column i+1 to be black by the end. No assumption is needed on the intervening cells. -/
theorem black_reaches_boundary (x : Int → Bool) : ∀ (n : Nat) (i : Int) (a : Nat),
    (∀ s, s < n → evol x (a+s) i = false) →
    evol x a (i+(n+1 : Nat)) = true → evol x (a+n) (i+1) = true
  | 0, i, a, _, hb => by simpa using hb
  | n+1, i, a, hw, hb => by
    cases hf : evol x (a+(n+1)) (i+1)
    · have h1 : ∀ s, s ≤ n+1 → evol x (a+s) (i+1) = false := by
        intro s hs
        cases hb1 : evol x (a+s) (i+1)
        · rfl
        · have hm := Rule30FiniteBlackRuns.black_stays x i (a+s) (n+1-s)
            (fun k hk => by
              have hh := hw (s+k) (by omega)
              rwa [show a+(s+k) = (a+s)+k by omega] at hh)
            hb1 (n+1-s) (Nat.le_refl _)
          rw [show a+s+(n+1-s) = a+(n+1) by omega, hf] at hm
          exact absurd hm (by decide)
      have hb' : evol x a ((i+1)+(n+1 : Nat)) = true := by
        rw [show (i+1)+((n+1 : Nat) : Int) = i+((n+1+1 : Nat) : Int) by omega]
        exact hb
      have ih := black_reaches_boundary x n (i+1) a (fun s hs => h1 s (by omega)) hb'
      have hstep : evol x (a+(n+1)) (i+1) =
          rule (evol x (a+n) i) (evol x (a+n) (i+1)) (evol x (a+n) (i+2)) := by
        rw [show a+(n+1) = (a+n)+1 by omega]
        change rule (evol x (a+n) (i+1-1)) (evol x (a+n) (i+1))
          (evol x (a+n) (i+1+1)) = _
        congr 2 <;> omega
      rw [hw n (by omega), h1 n (by omega),
        show i+2 = (i+1)+1 by omega, ih, hf] at hstep
      exact absurd hstep (by decide)
    · rfl

/-- **One absorbing step.** Once a white interval has a sufficiently early black neighbour,
any following m-step pulse leaves a black cell close enough that the next white interval
has a black neighbour after at most m+2 steps. The pulse is entirely arbitrary. -/
theorem white_pulse_return (x : Int → Bool) (i : Int) (a r m s : Nat)
    (hw : ∀ k, k < r → evol x (a+k) i = false)
    (hearly : evol x (a+s) (i+1) = true) (hs : s+9*(m+1) ≤ r)
    (hnext : ∀ k, k < r → evol x (a+r+m+k) i = false) :
    ∀ k, m+2 ≤ k → k ≤ r → evol x (a+r+m+k) (i+1) = true := by
  have hhold := Rule30FiniteBlackRuns.black_stays x i (a+s) (r-s)
    (fun k hk => by
      have hh := hw (s+k) (by omega)
      rwa [show a+(s+k) = (a+s)+k by omega] at hh) hearly
  have hlast : ∀ k, k < 9*(m+1) → evol x (a+r-9*(m+1)+k) (i+1) = true := by
    intro k hk
    have hh := hhold (r-9*(m+1)-s+k) (by omega)
    rwa [show a+s+(r-9*(m+1)-s+k) = a+r-9*(m+1)+k by omega] at hh
  have hsurv := black_survives_pulse x i (a+r-9*(m+1)) m hlast
  rw [show a+r-9*(m+1)+9*(m+1)+m = a+r+m by omega] at hsurv
  let q : Nat := 2*(m/2)+3
  have hqlo : 1 ≤ q := by dsimp [q]; omega
  have hqhi : q-1 ≤ m+2 := by dsimp [q]; omega
  have hqr : q-1 ≤ r := by omega
  have harr := black_reaches_boundary x (q-1) i (a+r+m)
    (fun k hk => hnext k (by omega)) (by simpa only [show q-1+1 = q by omega] using hsurv)
  have hstay := Rule30FiniteBlackRuns.black_stays x i ((a+r+m)+(q-1)) (r-(q-1))
    (fun k hk => by
      have hh := hnext (q-1+k) (by omega)
      rwa [show a+r+m+(q-1+k) = ((a+r+m)+(q-1))+k by omega] at hh) harr
  intro k hk hkr
  have hh := hstay (k-(q-1)) (by omega)
  rwa [show (a+r+m)+(q-1)+(k-(q-1)) = a+r+m+k by omega] at hh

/-- **The absorbing regime persists for arbitrary pulses.** If every cycle starts with r white
steps, r≥10m+11, one early black neighbour forces all later white intervals to have a black
neighbour from phase m+2 on. No periodicity or restriction on the m pulse bits is assumed. -/
theorem absorbing_white_cycles (x : Int → Bool) (i : Int) (a r m s : Nat)
    (hr : 10*m+11 ≤ r)
    (hw : ∀ n k, k < r → evol x (a+n*(r+m)+k) i = false)
    (hearly : evol x (a+s) (i+1) = true) (hs : s+9*(m+1) ≤ r) :
    ∀ n, 1 ≤ n → ∀ k, m+2 ≤ k → k ≤ r →
      evol x (a+n*(r+m)+k) (i+1) = true := by
  have hcycle : ∀ n, ∀ k, m+2 ≤ k → k ≤ r →
      evol x (a+(n+1)*(r+m)+k) (i+1) = true := by
    intro n
    induction n with
    | zero =>
      simpa only [Nat.zero_add, Nat.one_mul, Nat.add_assoc] using
        white_pulse_return x i a r m s (by simpa using hw 0) hearly hs
          (by simpa [Nat.one_mul, Nat.add_assoc] using hw 1)
    | succ n ih =>
      have h := white_pulse_return x i (a+(n+1)*(r+m)) r m (m+2)
        (hw (n+1)) (ih (m+2) (Nat.le_refl _) (by omega)) (by omega)
        (fun k hk => by
          have hh := hw (n+2) k hk
          rwa [show a+(n+2)*(r+m)+k = a+(n+1)*(r+m)+r+m+k by
            rw [show n+2 = (n+1)+1 by omega, Nat.succ_mul]; omega] at hh)
      intro k hk hkr
      have hh := h k hk hkr
      rwa [show a+(n+1)*(r+m)+r+m+k = a+(n+1+1)*(r+m)+k by
        rw [Nat.succ_mul (n+1) (r+m)]; omega] at hh
  intro n hn k hk hkr
  have hh := hcycle (n-1) k hk hkr
  rwa [show n-1+1 = n by omega] at hh

/-- **Synchronization of the neighbour.** For a periodic boundary with r white phases and m
arbitrary pulse phases, r≥10m+11, entering the early-black regime forces the entire neighbour
column to be eventually periodic. This statement is independent of the initial configuration. -/
theorem periodic_neighbour_of_early_black (x : Int → Bool) (i : Int) (a r m s : Nat)
    (hr : 10*m+11 ≤ r)
    (hper : ∀ t, a ≤ t → evol x (t+(r+m)) i = evol x t i)
    (hw : ∀ n k, k < r → evol x (a+n*(r+m)+k) i = false)
    (hearly : evol x (a+s) (i+1) = true) (hs : s+9*(m+1) ≤ r) :
    EventuallyPeriodic (fun t => evol x t (i+1)) := by
  let b : Nat → Nat := fun n => a+(n+1)*(r+m)+r
  have hb (n : Nat) : b (n+1) = b n+(r+m) := by
    dsimp [b]
    rw [Nat.succ_mul (n+1) (r+m)]
    omega
  have hbounds (n : Nat) : a ≤ b n ∧ r ≤ b n := by dsimp [b]; omega
  have habs := absorbing_white_cycles x i a r m s hr hw hearly hs
  have hend (n : Nat) : evol x (b n) (i+1) = true := by
    exact habs (n+1) (by omega) r (by omega) (Nat.le_refl _)
  have hlast (n : Nat) : ∀ k, k < 9*(m+1) →
      evol x (b n-9*(m+1)+k) (i+1) = true := by
    intro k hk
    have hh := habs (n+1) (by omega) (r-9*(m+1)+k) (by omega) (by omega)
    rwa [show a+(n+1)*(r+m)+(r-9*(m+1)+k) = b n-9*(m+1)+k by
      dsimp [b]; omega] at hh
  have hstripe (n : Nat) (p : Int) (hlo : i+2 ≤ p) (hhi : p ≤ i+2*(m+1)+1) :
      evol x (b n) p = stripe i p := by
    have hh := shield_stripe x i (b n-9*(m+1)) (m+1) (hlast n) p hlo hhi
    rwa [show b n-9*(m+1)+9*(m+1) = b n by have := (hbounds n).2; omega] at hh
  have hrow (n : Nat) (p : Int) (hlo : i+1 ≤ p) (hhi : p ≤ i+(2*m+3 : Nat)) :
      evol x (b n) p = evol x (b (n+1)) p := by
    by_cases hp : p = i+1
    · rw [hp, hend n, hend (n+1)]
    · rw [hstripe n p (by omega) (by omega), hstripe (n+1) p (by omega) (by omega)]
  have hdriver (n : Nat) : ∀ k, evol x (b n+k) i = evol x (b (n+1)+k) i := by
    intro k
    have hh := hper (b n+k) (by have := (hbounds n).1; omega)
    rw [hb]
    rw [show b n+k+(r+m) = b n+(r+m)+k by omega] at hh
    exact hh.symm
  have hlate (n k : Nat) (hk : m ≤ k) :
      b n+k = a+((n+1)+1)*(r+m)+(k-m) := by
    dsimp [b]
    rw [Nat.succ_mul (n+1) (r+m)]
    omega
  have hblock (n k : Nat) (hk : k < r+m) :
      evol x (b n+k) (i+1) = evol x (b (n+1)+k) (i+1) := by
    by_cases he : k ≤ 2*m+2
    · exact Rule30FiniteBlackRuns.cone_agree x i (b n) (b (n+1)) (2*m+3)
        (hdriver n) (hrow n) k (i+1) (by omega) (by omega)
    · rw [hlate n k (by omega), hlate (n+1) k (by omega),
        habs ((n+1)+1) (by omega) (k-m) (by omega) (by omega),
        habs (((n+1)+1)+1) (by omega) (k-m) (by omega) (by omega)]
  refine ⟨b 0, r+m, by omega, fun t ht => ?_⟩
  let n := (t-b 0)/(r+m)
  let k := (t-b 0)%(r+m)
  have hk : k < r+m := Nat.mod_lt _ (by omega)
  have hb0 : b n = b 0+n*(r+m) := by
    dsimp [b]
    rw [Nat.succ_mul n (r+m)]
    omega
  have heq : t = b n+k := by
    have hd := Nat.div_add_mod (t-b 0) (r+m)
    rw [Nat.mul_comm] at hd
    dsimp [n, k] at hb0 ⊢
    omega
  have hh := hblock n k hk
  rw [← heq, hb, show b n+(r+m)+k = (b n+k)+(r+m) by omega, ← heq] at hh
  exact hh.symm

/-- **General early-arrival exclusion.** A periodic boundary column in a left-finite nonzero
configuration cannot enter the synchronized early-black regime. Any hypothetical periodic
word 0^r u with r≥10|u|+11 must therefore keep its right neighbour white through the early
part of every white run. This reduces the unbounded-tail question to the late-arrival regime. -/
theorem no_periodic_boundary_early_black {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (a r m s : Nat) (hr : 10*m+11 ≤ r)
    (hper : ∀ t, a ≤ t → evol x (t+(r+m)) i = evol x t i)
    (hw : ∀ n k, k < r → evol x (a+n*(r+m)+k) i = false)
    (hearly : evol x (a+s) (i+1) = true) (hs : s+9*(m+1) ≤ r) : False :=
  Rule30FiniteConfigs.not_adjacent hlo hzero i ⟨a, r+m, by omega, hper⟩
    (periodic_neighbour_of_early_black x i a r m s hr hper hw hearly hs)

/-- **Necessary early-white condition, in every cycle.** A periodic boundary with a sufficiently
long white block forces its right neighbour to remain white until the final 9(m+1) white steps. -/
theorem periodic_white_cycles_force_early_white {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (a r m : Nat) (hr : 10*m+11 ≤ r)
    (hper : ∀ t, a ≤ t → evol x (t+(r+m)) i = evol x t i)
    (hw : ∀ n k, k < r → evol x (a+n*(r+m)+k) i = false) :
    ∀ n s, s+9*(m+1) ≤ r → evol x (a+n*(r+m)+s) (i+1) = false := by
  intro n s hs
  cases hb : evol x (a+n*(r+m)+s) (i+1)
  · rfl
  · exact False.elim (no_periodic_boundary_early_black hlo hzero i (a+n*(r+m)) r m s hr
      (fun t ht => hper t (by omega))
      (fun q k hk => by
        have hh := hw (n+q) k hk
        simpa only [Nat.add_mul, Nat.add_assoc] using hh) hb hs)

/-- **A wide spatial white prefix is necessary at every period start.** Any closer black cell
would reach the right neighbour in a forbidden early phase. -/
theorem periodic_white_cycles_force_empty_prefix {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (a r m : Nat) (hr : 10*m+11 ≤ r)
    (hper : ∀ t, a ≤ t → evol x (t+(r+m)) i = evol x t i)
    (hw : ∀ n k, k < r → evol x (a+n*(r+m)+k) i = false) :
    ∀ n q, 1 ≤ q → q-1+9*(m+1) ≤ r → evol x (a+n*(r+m)) (i+q) = false := by
  intro n q hq hqr
  cases hb : evol x (a+n*(r+m)) (i+q)
  · rfl
  · have harr := black_reaches_boundary x (q-1) i (a+n*(r+m))
      (fun k hk => hw n k (by omega)) (by simpa only [show q-1+1 = q by omega] using hb)
    have hz := periodic_white_cycles_force_early_white hlo hzero i a r m hr hper hw n (q-1) hqr
    rw [hz] at harr
    exact absurd harr (by decide)

/-- **Arbitrary-tail reduction.** For every finite tail u, an eventual word 0^r u with
r≥10|u|+11 forces column i+1 white throughout every early phase of its white block.
No bound is placed on |u|, and no certificate or finite case split is used here. -/
theorem white_padding_forces_early_white {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (r : Nat) (hr : 10*u.length+11 ≤ r)
    (hword : Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ u)) :
    ∃ T, (∀ t, T ≤ t → evol x t i =
      (List.replicate r false ++ u).getD ((t-T)%(r+u.length)) false) ∧
      ∀ n s, s+9*(u.length+1) ≤ r →
        evol x (T+n*(r+u.length)+s) (i+1) = false := by
  obtain ⟨T, hT⟩ := hword
  have hlen : (List.replicate r false ++ u).length = r+u.length := by simp
  have hT' : ∀ t, T ≤ t → evol x t i =
      (List.replicate r false ++ u).getD ((t-T)%(r+u.length)) false := by
    simpa only [hlen] using hT
  refine ⟨T, hT', periodic_white_cycles_force_early_white hlo hzero i T r u.length hr ?_ ?_⟩
  · intro t ht
    rw [hT' t ht, hT' (t+(r+u.length)) (by omega),
      show t+(r+u.length)-T = (t-T)+(r+u.length) by omega, Nat.add_mod_right]
  · intro n k hk
    rw [hT' _ (by omega), show T+n*(r+u.length)+k-T = k+n*(r+u.length) by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (l₁ := List.replicate r false) (l₂ := u) (by simpa using hk),
      List.getElem?_replicate_of_lt hk]
    rfl

end Ruliology.CellularAutomata.Rule30WhitePulseResearch

/- Source: lean/Ruliology/CellularAutomata/Rule30WhitePaddingVacuumCriterionResearch.lean -/
/-!
# A finite vacuum-avoidance criterion for arbitrary white-padding families

A stable zero-driven reachable set G and the single finite check that a pulse u
cannot send G to the vacuum imply exclusions of 0^r u for all sufficiently large r.
The length and contents of u are unrestricted. This does not establish that such
vacuum-avoidance certificates exist for every pulse.
-/
namespace Ruliology.CellularAutomata.Rule30WhitePaddingVacuumCriterionResearch
open Rule30Jen Rule30Realization Rule30FiniteConfigs Rule30StripCertificates
open Rule30WhitePaddingResearch Rule30WhitePulseResearch

/-- A nonzero encoded strip contains a black cell within its width. -/
theorem enc_nonzero_has_black {x : Int → Bool} {K t : Nat} {i : Int} {v : Nat}
    (he : Rule30FiniteStripsResearch.Enc x K t i v) (hv : v ≠ 0) :
    ∃ j, j < K ∧ evol x t (i + (j + 1 : Nat)) = true := by
  obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero hv
  have hjK : j < K := by
    by_cases h : j < K
    · exact h
    · have hh := Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le he.1 (Nat.pow_le_pow_right (by decide) (show K ≤ j by omega)))
      rw [hj] at hh
      contradiction
  refine ⟨j, hjK, ?_⟩
  have hh := he.2 j hjK
  rw [hj] at hh
  have hpos : i + 1 + (j : Int) = i + ((j + 1 : Nat) : Int) := by omega
  rw [hpos] at hh
  exact hh.symm

/-- **Generic arbitrary-tail criterion.** Once G is the stabilized zero-driven full strip set,
only vacuum avoidance by u needs a finite check. No tail-length bound is imposed. -/
theorem no_padding_of_vacuum_avoidance {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (K n G : Nat)
    (hG : zeros K n (fullSet K) = G)
    (hstable : image K false G = G)
    (hsafe : (applyWord K u G).testBit 0 = false)
    (r : Nat) (hrn : n ≤ r)
    (hrpulse : 10*u.length+11 ≤ r)
    (hrwidth : K+9*(u.length+1) ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ u) := by
  intro hword
  obtain ⟨T, hT, hwhite⟩ := white_padding_forces_early_white hlo hzero i u r hrpulse hword
  let w := List.replicate r false ++ u
  have hlen : w.length = r+u.length := by simp [w]
  have hblock : ∀ s, s < w.length → evol x (T+s) i = w.getD s false := by
    intro s hs
    rw [hT _ (by omega), show T+s-T=s by omega,
      Nat.mod_eq_of_lt (by simpa only [hlen] using hs)]
  have hstab : zeros K (n+1) (fullSet K) = zeros K n (fullSet K) := by
    rw [zeros_succ, hG, hstable]
  have hpump : applyWord K w (fullSet K) = applyWord K u G := by
    rw [show w=List.replicate r false++u from rfl, applyWord_append,
      ← zeros, zeros_stable K n (fullSet K) hstab r hrn, hG]
  have he0 := Rule30FiniteStripsResearch.enc_encRow (x := x) K T i
  have hfull : (fullSet K).testBit (Rule30FiniteStripsResearch.encRow x T i K) = true := by
    unfold fullSet
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true he0.1
  obtain ⟨v, he, hv⟩ := Rule30FiniteStripsResearch.enc_applyWord w T _ (fullSet K) he0 hfull hblock
  rw [hpump] at hv
  have hv0 : v ≠ 0 := by
    intro hz
    subst v
    rw [hsafe] at hv
    contradiction
  rw [hlen] at he
  obtain ⟨j, hjK, hjblack⟩ := enc_nonzero_has_black he hv0
  have hboundary : ∀ s, s < j → evol x (T+(r+u.length)+s) i = false := by
    intro s hs
    have hsr : s < r := by omega
    rw [hT _ (by omega),
      show T+(r+u.length)+s-T=s+1*(r+u.length) by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (l₁ := List.replicate r false) (l₂ := u) (by simpa using hsr),
      List.getElem?_replicate_of_lt hsr]
    rfl
  have hblack := black_reaches_boundary x j i (T+(r+u.length)) hboundary hjblack
  have hwh := hwhite 1 j (by omega)
  simp only [Nat.one_mul] at hwh
  rw [hblack] at hwh
  contradiction

/-- Single-seed version of the same generic finite criterion. -/
theorem no_padding_seed_of_vacuum_avoidance
    (u : List Bool) (K n G : Nat)
    (hG : zeros K n (fullSet K) = G)
    (hstable : image K false G = G)
    (hsafe : (applyWord K u G).testBit 0 = false)
    (r : Nat) (hrn : n ≤ r)
    (hrpulse : 10*u.length+11 ≤ r)
    (hrwidth : K+9*(u.length+1) ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate r false ++ u) := by
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed, show p ≠ 0 by omega]
  have h := no_padding_of_vacuum_avoidance (x := seed) (lo := 0) (by decide) hzero
    0 u K n G hG hstable hsafe r hrn hrpulse hrwidth
  simpa only [Rule30FiniteStripsResearch.EventuallyWord, Rule30StripCertificates.EventuallyWord,
    evol_seed] using h

end Ruliology.CellularAutomata.Rule30WhitePaddingVacuumCriterionResearch

/- Source: lean/Ruliology/CellularAutomata/Rule30ForbiddenSuffixResearch.lean -/
/-!
# Forbidden suffixes give white-padding exclusions with arbitrary prefixes

If a finite driver word cannot send any width-K strip to the all-white strip,
then it cannot be the suffix of a sufficiently white-padded eventual period.
The part of the tail preceding that suffix is arbitrary and has unbounded length.
This strengthens the vacuum-avoidance interface: no stabilized reachable set is
needed, and a single certificate works for infinitely many different tails.

The analytic white-pulse estimate remains essential. These results do not exclude
every periodic word, in particular the alternating period is still open.
-/
namespace Ruliology.CellularAutomata.Rule30ForbiddenSuffixResearch
open Rule30Jen Rule30Realization Rule30StripCertificates
open Rule30WhitePulseResearch Rule30WhitePaddingVacuumCriterionResearch

/-- A vacuum-free image of the full strip set excludes every white-padded tail
ending in the certified suffix, regardless of the preceding tail bits. -/
theorem no_padding_of_forbidden_suffix {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (lead suffix : List Bool) (K : Nat)
    (hsafe : (applyWord K suffix (fullSet K)).testBit 0 = false)
    (r : Nat) (hrpulse : 10*(lead.length+suffix.length)+11 ≤ r)
    (hrwidth : K+9*(lead.length+suffix.length+1) ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i
      (List.replicate r false ++ (lead ++ suffix)) := by
  intro hword
  obtain ⟨T, hT, hwhite⟩ := white_padding_forces_early_white hlo hzero i
    (lead ++ suffix) r (by simpa using hrpulse) hword
  have hdriver : ∀ s, s < suffix.length →
      evol x (T+r+lead.length+s) i = suffix.getD s false := by
    intro s hs
    rw [hT _ (by omega), List.length_append,
      show T+r+lead.length+s-T = r+lead.length+s by omega,
      Nat.mod_eq_of_lt (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (l₁ := List.replicate r false)
      (l₂ := lead ++ suffix) (by simp; omega)]
    simp only [List.length_replicate]
    rw [show r+lead.length+s-r = lead.length+s by omega,
      List.getElem?_append_right (l₁ := lead) (l₂ := suffix) (by omega),
      show lead.length+s-lead.length = s by omega]
  have he0 := Rule30FiniteStripsResearch.enc_encRow (x := x) K (T+r+lead.length) i
  have hfull : (fullSet K).testBit
      (Rule30FiniteStripsResearch.encRow x (T+r+lead.length) i K) = true := by
    unfold fullSet
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true he0.1
  obtain ⟨v, he, hv⟩ := Rule30FiniteStripsResearch.enc_applyWord suffix
    (T+r+lead.length) _ (fullSet K) he0 hfull hdriver
  have hv0 : v ≠ 0 := by
    intro hz
    subst v
    rw [hsafe] at hv
    contradiction
  obtain ⟨j, hjK, hjblack⟩ := enc_nonzero_has_black he hv0
  have hboundary : ∀ s, s < j →
      evol x (T+r+lead.length+suffix.length+s) i = false := by
    intro s hs
    have hsr : s < r := by omega
    rw [hT _ (by omega), List.length_append,
      show T+r+lead.length+suffix.length+s-T =
        s+1*(r+(lead.length+suffix.length)) by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (l₁ := List.replicate r false)
      (l₂ := lead ++ suffix) (by simpa using hsr),
      List.getElem?_replicate_of_lt hsr]
    rfl
  have hblack := black_reaches_boundary x j i
    (T+r+lead.length+suffix.length) hboundary hjblack
  have hwh := hwhite 1 j (by simp; omega)
  simp only [List.length_append, Nat.one_mul] at hwh
  rw [show T+(r+(lead.length+suffix.length))+j =
    T+r+lead.length+suffix.length+j by omega, hblack] at hwh
  contradiction

/-- The same arbitrary-lead criterion for every nonzero finite initial pattern. -/
theorem no_padding_of_forbidden_suffix_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (lead suffix : List Bool) (K : Nat)
    (hsafe : (applyWord K suffix (fullSet K)).testBit 0 = false)
    (r : Nat) (hrpulse : 10*(lead.length+suffix.length)+11 ≤ r)
    (hrwidth : K+9*(lead.length+suffix.length+1) ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i
      (List.replicate r false ++ (lead ++ suffix)) := by
  obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_padding_of_forbidden_suffix hlo hzero i lead suffix K hsafe r hrpulse hrwidth

/-- Single-seed version, with arbitrary transient and arbitrary lead length. -/
theorem no_padding_of_forbidden_suffix_seed
    (lead suffix : List Bool) (K : Nat)
    (hsafe : (applyWord K suffix (fullSet K)).testBit 0 = false)
    (r : Nat) (hrpulse : 10*(lead.length+suffix.length)+11 ≤ r)
    (hrwidth : K+9*(lead.length+suffix.length+1) ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord
      (List.replicate r false ++ (lead ++ suffix)) := by
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed, show p ≠ 0 by omega]
  have h := no_padding_of_forbidden_suffix (x := seed) (lo := 0) (by decide) hzero
    0 lead suffix K hsafe r hrpulse hrwidth
  simpa only [Rule30FiniteStripsResearch.EventuallyWord,
    Rule30StripCertificates.EventuallyWord, evol_seed] using h

end Ruliology.CellularAutomata.Rule30ForbiddenSuffixResearch

/- Source: lean/Ruliology/CellularAutomata/Rule30Certificates/ForbiddenSuffixResearch.lean -/
/-! Small vacuum-free suffix certificates, starting from every strip state.
Both values of the unknown right boundary are included at every step.
These finite facts are replayed by Lean's kernel, without native evaluation. -/
namespace Ruliology.CellularAutomata.Rule30ForbiddenSuffixCertificatesResearch
open Rule30StripCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def suffix011 : List Bool := [false, true, true]
def suffix001001 : List Bool := [false, false, true, false, false, true]
def suffix111001 : List Bool := [true, true, true, false, false, true]

theorem safe011 : (applyWord 5 suffix011 (fullSet 5)).testBit 0 = false := by
  decide +kernel

theorem safe001001 : (applyWord 6 suffix001001 (fullSet 6)).testBit 0 = false := by
  decide +kernel

theorem safe111001 : (applyWord 6 suffix111001 (fullSet 6)).testBit 0 = false := by
  decide +kernel

end Ruliology.CellularAutomata.Rule30ForbiddenSuffixCertificatesResearch

/- Source: lean/Ruliology/CellularAutomata/Rule30SuffixFamiliesResearch.lean -/
/-!
# White-padding exclusions for tails of unbounded length

For every Boolean word v, no column of a configuration with a leftmost black cell
eventually repeats `0^r v 011` when r ≥ 10|v|+41. Two further suffixes, `001001`
and `111001`, give the sufficient bound r ≥ 10|v|+71. The prefix v and the
transient are unrestricted. Unlike a finite list of fixed tails, each statement
covers infinitely many tails, with arbitrarily many black bits and alternations.
These are partial results; none settles the alternating period or Problem 1.
-/
namespace Ruliology.CellularAutomata.Rule30SuffixFamiliesResearch
open Rule30Jen Rule30Realization Rule30StripCertificates
open Rule30ForbiddenSuffixResearch Rule30ForbiddenSuffixCertificatesResearch

/-- An arbitrary prefix before `011`, not merely a bounded-length tail. -/
theorem no_padding_suffix011_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10*v.length+41 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i
      (List.replicate r false ++ (v ++ suffix011)) := by
  exact no_padding_of_forbidden_suffix hlo hzero i v suffix011 5 safe011 r
    (by simp [suffix011]; omega) (by simp [suffix011]; omega)

theorem no_padding_suffix001001_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10*v.length+71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i
      (List.replicate r false ++ (v ++ suffix001001)) := by
  exact no_padding_of_forbidden_suffix hlo hzero i v suffix001001 6 safe001001 r
    (by simp [suffix001001]; omega) (by simp [suffix001001]; omega)

theorem no_padding_suffix111001_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10*v.length+71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i
      (List.replicate r false ++ (v ++ suffix111001)) := by
  exact no_padding_of_forbidden_suffix hlo hzero i v suffix111001 6 safe111001 r
    (by simp [suffix111001]; omega) (by simp [suffix111001]; omega)

theorem no_padding_suffix011_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10*v.length+41 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i
      (List.replicate r false ++ (v ++ suffix011)) := by
  obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_padding_suffix011_leftFinite hlo hzero i v r hr

theorem no_padding_suffix011_seed (v : List Bool) (r : Nat) (hr : 10*v.length+41 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord
      (List.replicate r false ++ (v ++ suffix011)) := by
  exact no_padding_of_forbidden_suffix_seed v suffix011 5 safe011 r
    (by simp [suffix011]; omega) (by simp [suffix011]; omega)

theorem no_padding_suffix001001_seed (v : List Bool) (r : Nat) (hr : 10*v.length+71 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord
      (List.replicate r false ++ (v ++ suffix001001)) := by
  exact no_padding_of_forbidden_suffix_seed v suffix001001 6 safe001001 r
    (by simp [suffix001001]; omega) (by simp [suffix001001]; omega)

theorem no_padding_suffix111001_seed (v : List Bool) (r : Nat) (hr : 10*v.length+71 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord
      (List.replicate r false ++ (v ++ suffix111001)) := by
  exact no_padding_of_forbidden_suffix_seed v suffix111001 6 safe111001 r
    (by simp [suffix111001]; omega) (by simp [suffix111001]; omega)

end Ruliology.CellularAutomata.Rule30SuffixFamiliesResearch

namespace Rule30Submission
open Ruliology.CellularAutomata
open Rule30ForbiddenSuffixCertificatesResearch

theorem no_padding_suffix011 {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10*v.length+41 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i
      (List.replicate r false ++ (v ++ suffix011)) :=
  Rule30SuffixFamiliesResearch.no_padding_suffix011_leftFinite hlo hzero i v r hr

theorem no_padding_suffix001001 {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10*v.length+71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i
      (List.replicate r false ++ (v ++ suffix001001)) :=
  Rule30SuffixFamiliesResearch.no_padding_suffix001001_leftFinite hlo hzero i v r hr

theorem no_padding_suffix111001 {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10*v.length+71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i
      (List.replicate r false ++ (v ++ suffix111001)) :=
  Rule30SuffixFamiliesResearch.no_padding_suffix111001_leftFinite hlo hzero i v r hr

end Rule30Submission
