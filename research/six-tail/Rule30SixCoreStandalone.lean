import Ruliology.CellularAutomata.Rule30FiniteBlackRuns
import Ruliology.CellularAutomata.Rule30LightCone
import Ruliology.CellularAutomata.Rule30StripCertificates
import Ruliology.CellularAutomata.Rule30FiniteMaskedJen

/- Source: Ruliology.CellularAutomata.Rule30FiniteStripsResearch -/
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

/- Source: Ruliology.CellularAutomata.Rule30WhitePulseResearch -/
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

/- Source: Ruliology.CellularAutomata.Rule30WhitePaddingResearch -/
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

/- Source: Ruliology.CellularAutomata.Rule30ZeroPredecessorResearch -/
/-! The vacuum has a unique predecessor under a white boundary, uniformly in width. -/
namespace Ruliology.CellularAutomata.Rule30ZeroPredecessorResearch
open Rule30Jen Rule30StripCertificates Rule30WhitePaddingResearch

theorem stripStep_zero_predecessor {K r : Nat} {z : Bool}
    (hr : r < 2^K) (hstep : stripStep K false z r = 0) : r = 0 := by
  have hbits : ∀ k, k < K → r.testBit k = false := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk
      have hl : (if k = 0 then false else r.testBit (k-1)) = false := by
        split
        · rfl
        · exact ih (k-1) (by omega) (by omega)
      have h := testBit_stripStep K false z r hr k hk
      rw [hstep, Nat.zero_testBit, hl] at h
      cases hc : r.testBit k
      · rfl
      · simp [rule, hc] at h
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.zero_testBit]
  by_cases hk : k < K
  · exact hbits k hk
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by omega)))

theorem stripStep_zero_iff {K r : Nat} {z : Bool} (hK : 1 ≤ K) (hr : r < 2^K) :
    stripStep K false z r = 0 ↔ r = 0 ∧ z = false := by
  constructor
  · intro h
    have hzero := stripStep_zero_predecessor hr h
    subst r
    have hb := testBit_stripStep K false z 0 (by exact Nat.two_pow_pos K) (K-1) (by omega)
    rw [h, Nat.zero_testBit] at hb
    have hz : z = false := by simpa [rule, show K-1+1=K by omega] using hb.symm
    exact ⟨rfl, hz⟩
  · rintro ⟨rfl,rfl⟩
    simp [stripStep]

end Ruliology.CellularAutomata.Rule30ZeroPredecessorResearch

/- Source: Ruliology.CellularAutomata.Rule30BackwardTubeResearch -/
/-! Endpoint-conditioned backward strip certificates. -/
namespace Ruliology.CellularAutomata.Rule30BackwardTubeResearch
open Rule30Jen Rule30Realization Rule30StripCertificates Rule30FiniteStripsResearch
open Rule30WhitePulseResearch Rule30ZeroPredecessorResearch Rule30WhitePaddingResearch

def preCheck (K : Nat) (a : Bool) (Q R : Nat) : Bool :=
  allBelow (fun s =>
    (! R.testBit (stripStep K a false s) || Q.testBit s) &&
    (! R.testBit (stripStep K a true s) || Q.testBit s)) (2^K)

theorem preCheck_sound {K Q R s : Nat} {a z : Bool}
    (h : preCheck K a Q R = true) (hs : s < 2^K)
    (ht : R.testBit (stripStep K a z s) = true) : Q.testBit s = true := by
  have hh := allBelow_spec h s hs
  rw [Bool.and_eq_true] at hh
  cases z
  · have hh := hh.1
    rw [ht, Bool.not_true, Bool.false_or] at hh
    exact hh
  · have hh := hh.2
    rw [ht, Bool.not_true, Bool.false_or] at hh
    exact hh

theorem enc_unique {x : Int → Bool} {K t : Nat} {i : Int} {r s : Nat}
    (hr : Rule30FiniteStripsResearch.Enc x K t i r) (hs : Rule30FiniteStripsResearch.Enc x K t i s) : r = s := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < K
  · rw [hr.2 j hj, hs.2 j hj]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr.1 (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hs.1 (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem encRow_step (x : Int → Bool) (K t : Nat) (i : Int) :
    Rule30FiniteStripsResearch.encRow x (t+1) i K =
      stripStep K (evol x t i) (evol x t (i+1+K)) (Rule30FiniteStripsResearch.encRow x t i K) :=
  enc_unique (Rule30FiniteStripsResearch.enc_encRow K (t+1) i) (Rule30FiniteStripsResearch.enc_step (Rule30FiniteStripsResearch.enc_encRow K t i))

theorem enc_backward {x : Int → Bool} {K t Q R : Nat} {i : Int} {a : Bool}
    (h : preCheck K a Q R = true) (ha : evol x t i = a)
    (hR : R.testBit (Rule30FiniteStripsResearch.encRow x (t+1) i K) = true) :
    Q.testBit (Rule30FiniteStripsResearch.encRow x t i K) = true := by
  rw [encRow_step, ha] at hR
  exact preCheck_sound h (Rule30FiniteStripsResearch.enc_encRow K t i).1 hR

theorem encRow_zero_of_prefix {x : Int → Bool} {K t : Nat} {i : Int}
    (h : ∀ j, j < K → evol x t (i+1+j) = false) : Rule30FiniteStripsResearch.encRow x t i K = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.zero_testBit]
  by_cases hj : j < K
  · rw [(Rule30FiniteStripsResearch.enc_encRow K t i).2 j hj, h j hj]
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le
      (Rule30FiniteStripsResearch.enc_encRow K t i).1 (Nat.pow_le_pow_right (by decide) (by omega)))

theorem colConst_intersection {K Z Q s : Nat} {b : Bool}
    (h : colConst K (Z &&& Q) b = true) (hs : s < 2^K)
    (hZ : Z.testBit s = true) (hQ : Q.testBit s = true) : s.testBit 0 = b := by
  have hh := allBelow_spec h s hs
  rw [Nat.testBit_and, hZ, hQ] at hh
  simpa using hh

theorem white_tube_forces (K r L Z : Nat) (Q : Nat → Nat) (b : Nat → Bool)
    (f : Nat → Nat) (z : Nat → Bool) (hL : L ≤ r)
    (hf : ∀ t, t ≤ r → f t < 2^K)
    (hstep : ∀ t, t < r → f (t+1) = stripStep K false (z t) (f t))
    (hZ : ∀ t, t ≤ r → Z.testBit (f t) = true)
    (hend : (Q 0).testBit (f r) = true)
    (hpre : ∀ d, d < L → preCheck K false (Q (d+1)) (Q d) = true)
    (hzero : Q L = 1)
    (hforce : ∀ d, d ≤ L → colConst K (Z &&& Q d) (b d) = true) :
    ∀ s, s < r → (f s).testBit 0 = if r-s ≤ L then b (r-s) else false := by
  have hQ : ∀ d, d ≤ L → (Q d).testBit (f (r-d)) = true := by
    intro d
    induction d with
    | zero => simpa using hend
    | succ d ih =>
      intro hd
      have hi := ih (by omega)
      have hs : r-(d+1)+1 = r-d := by omega
      rw [← hs, hstep (r-(d+1)) (by omega)] at hi
      exact preCheck_sound (hpre d (by omega)) (hf _ (by omega)) hi
  have hz : f (r-L) = 0 := by
    have hh := hQ L (by omega)
    rw [hzero] at hh
    exact Nat.testBit_one_eq_true_iff_self_eq_zero.mp hh
  have hzbefore : ∀ s, s ≤ r-L → f s = 0 := by
    have hrec : ∀ d, d ≤ r-L → f (r-L-d) = 0 := by
      intro d
      induction d with
      | zero => simpa using hz
      | succ d ih =>
        intro hd
        have hi := ih (by omega)
        have hs : r-L-(d+1)+1 = r-L-d := by omega
        rw [← hs, hstep _ (by omega)] at hi
        exact stripStep_zero_predecessor (hf _ (by omega)) hi
    intro s hs
    have hh := hrec (r-L-s) (by omega)
    simpa only [show r-L-(r-L-s)=s by omega] using hh
  intro s hs
  split
  · rename_i hd
    have hh := colConst_intersection (hforce (r-s) hd) (hf s (by omega)) (hZ s (by omega))
      (by simpa only [show r-(r-s)=s by omega] using hQ (r-s) hd)
    exact hh
  · rw [hzbefore s (by omega), Nat.zero_testBit]

theorem tail_tube_forces (K a : Nat) (u : List Bool) (P S : Nat → Nat)
    (c : Nat → Bool) (f : Nat → Nat) (z : Nat → Bool)
    (hf : ∀ t, t ≤ a+u.length → f t < 2^K)
    (hstep : ∀ j, j < u.length →
      f (a+j+1) = stripStep K (u.getD j false) (z (a+j)) (f (a+j)))
    (hend : (P u.length).testBit (f (a+u.length)) = true)
    (hpre : ∀ j, j < u.length → preCheck K (u.getD j false) (P j) (P (j+1)) = true)
    (hstart : (S 0).testBit (f a) = true)
    (hforward : ∀ j, j < u.length →
      subsetB K (image K (u.getD j false) (S j)) (S (j+1)) = true)
    (hforce : ∀ j, j < u.length → u.getD j false = false →
      colConst K (S j &&& P j) (c j) = true) :
    (P 0).testBit (f a) = true ∧
    ∀ j, j < u.length → u.getD j false = false → (f (a+j)).testBit 0 = c j := by
  have hP : ∀ d, d ≤ u.length → (P (u.length-d)).testBit (f (a+(u.length-d))) = true := by
    intro d
    induction d with
    | zero => simpa using hend
    | succ d ih =>
      intro hd
      have hi := ih (by omega)
      have hs : a+(u.length-(d+1))+1 = a+(u.length-d) := by omega
      rw [← hs, hstep _ (by omega)] at hi
      have hs' : u.length-d = u.length-(d+1)+1 := by omega
      rw [hs'] at hi
      exact preCheck_sound (hpre (u.length-(d+1)) (by omega)) (hf (a+(u.length-(d+1))) (by omega)) hi
  have hS : ∀ j, j ≤ u.length → (S j).testBit (f (a+j)) = true := by
    intro j
    induction j with
    | zero => simpa using hstart
    | succ j ih =>
      intro hj
      have hi := ih (by omega)
      have hmem := mem_imageAux (K := K) (a := u.getD j false) hi (z (a+j)) (2^K) (hf _ (by omega))
      change (image K (u.getD j false) (S j)).testBit
        (stripStep K (u.getD j false) (z (a+j)) (f (a+j))) = true at hmem
      have hs := allBelow_spec (hforward j (by omega)) _
        (stripStep_lt K (u.getD j false) (z (a+j)) (f (a+j)))
      rw [hmem, Bool.not_true, Bool.false_or] at hs
      rw [show a+(j+1)=a+j+1 by omega, hstep j (by omega)]
      exact hs
  constructor
  · simpa using hP u.length (by omega)
  · intro j hj ha
    exact colConst_intersection (hforce j hj ha) (hf _ (by omega)) (hS j (by omega))
      (by simpa only [show u.length-(u.length-j)=j by omega] using hP (u.length-j) (by omega))

theorem padding_getD (u : List Bool) (r s : Nat) :
    (List.replicate r false ++ u).getD s false =
      if s < r then false else u.getD (s-r) false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases hs : s < r
  · rw [if_pos hs, List.getElem?_append_left (by simpa using hs),
      List.getElem?_replicate_of_lt hs]
    rfl
  · rw [if_neg hs, List.getElem?_append_right (by simpa using Nat.le_of_not_lt hs)]
    simp

theorem subsetB_self (K S : Nat) : subsetB K S S = true := by
  have h : ∀ n, allBelow (fun s => !S.testBit s || S.testBit s) n = true := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [allBelow, ih, Bool.true_and]
      cases S.testBit n <;> rfl
  exact h (2^K)

/-- A stable white set plus a backward tube from the vacuum excludes an arbitrary tail.
Unlike a forward forcing certificate, the tube may condition on the next period's vacuum. -/
theorem no_padding_of_endpoint_tube {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (K L Z : Nat) (Q P S : Nat → Nat)
    (b c : Nat → Bool) (hK : 1 ≤ K)
    (hZzero : Z.testBit 0 = true) (hZfixed : image K false Z = Z)
    (hSzero : S 0 = Z) (hPend : P u.length = 1) (hQstart : Q 0 = P 0)
    (hQend : Q L = 1)
    (hQpre : ∀ d, d < L → preCheck K false (Q (d+1)) (Q d) = true)
    (hPpre : ∀ j, j < u.length → preCheck K (u.getD j false) (P j) (P (j+1)) = true)
    (hSforward : ∀ j, j < u.length → image K (u.getD j false) (S j) = S (j+1))
    (hQforce : ∀ d, d ≤ L → colConst K (Z &&& Q d) (b d) = true)
    (hPforce : ∀ j, j < u.length → u.getD j false = false →
      colConst K (S j &&& P j) (c j) = true)
    (r : Nat) (hrpulse : 10*u.length+11 ≤ r)
    (hrwidth : K-1+9*(u.length+1) ≤ r) (hrL : L ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ u) := by
  intro hword
  obtain ⟨T, hT, _⟩ := white_padding_forces_early_white hlo hzero i u r hrpulse hword
  have hperiod : ∀ t, T ≤ t → evol x (t+(r+u.length)) i = evol x t i := by
    intro t ht
    rw [hT t ht, hT (t+(r+u.length)) (by omega),
      show t+(r+u.length)-T=(t-T)+(r+u.length) by omega, Nat.add_mod_right]
  have hblock : ∀ n s, s < r+u.length → evol x (T+n*(r+u.length)+s) i =
      if s < r then false else u.getD (s-r) false := by
    intro n s hs
    rw [hT _ (by omega), show T+n*(r+u.length)+s-T=s+n*(r+u.length) by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs, padding_getD]
  have hwhite : ∀ n s, s < r → evol x (T+n*(r+u.length)+s) i = false := by
    intro n s hs
    rw [hblock n s (by omega), if_pos hs]
  have hstarts : ∀ n, Rule30FiniteStripsResearch.encRow x (T+n*(r+u.length)) i K = 0 := by
    intro n
    apply encRow_zero_of_prefix
    intro j hj
    have hh := periodic_white_cycles_force_empty_prefix hlo hzero i T r u.length hrpulse
      hperiod hwhite n (j+1) (by omega) (by omega)
    simpa only [show i+1+(j:Int)=i+((j+1:Nat):Int) by omega] using hh
  let g : Nat → Bool := fun s =>
    if s < r then (if r-s ≤ L then b (r-s) else false)
    else u.getD (s-r) false || c (s-r)
  have hphase : ∀ n s, s < r+u.length →
      Rule30FiniteMaskedJen.orCol x i (T+n*(r+u.length)+s) = g s := by
    intro n s hs
    let a := T+n*(r+u.length)
    let f : Nat → Nat := fun t => Rule30FiniteStripsResearch.encRow x (a+t) i K
    let z : Nat → Bool := fun t => evol x (a+t) (i+1+K)
    have hf : ∀ t, f t < 2^K := fun t => (Rule30FiniteStripsResearch.enc_encRow K (a+t) i).1
    have hstep : ∀ t, f (t+1) = stripStep K (evol x (a+t) i) (z t) (f t) := by
      intro t
      simpa only [f, z, Nat.add_assoc] using encRow_step x K (a+t) i
    have hfzero : f 0 = 0 := by simpa only [f, a, Nat.add_zero] using hstarts n
    have hfend : f (r+u.length) = 0 := by
      have hh := hstarts (n+1)
      simpa only [f, a, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hh
    have hfZ : ∀ t, t ≤ r → Z.testBit (f t) = true := by
      intro t
      induction t with
      | zero => intro _; rw [hfzero]; exact hZzero
      | succ t ih =>
        intro ht
        have hi := ih (by omega)
        have hmem := mem_imageAux (K := K) (a := false) hi (z t) (2^K) (hf t)
        change (image K false Z).testBit (stripStep K false (z t) (f t))=true at hmem
        rw [hZfixed] at hmem
        rw [hstep, show evol x (a+t) i=false by exact hwhite n t (by omega)]
        exact hmem
    have htube := tail_tube_forces K r u P S c f z (fun t _ => hf t)
      (fun j hj => by
        rw [hstep]
        have hh := hblock n (r+j) (by omega)
        simp only [show ¬r+j<r by omega, if_false, Nat.add_sub_cancel_left] at hh
        exact congrArg (fun a' => stripStep K a' (z (r+j)) (f (r+j))) hh)
      (by rw [hPend, hfend]; exact Nat.testBit_one_zero)
      hPpre (by rw [hSzero]; exact hfZ r (by omega))
      (fun j hj => by rw [hSforward j hj]; exact subsetB_self K (S (j+1))) hPforce
    have hwhitebits := white_tube_forces K r L Z Q b f z hrL (fun t _ => hf t)
      (fun t ht => by rw [hstep, show evol x (a+t) i=false by exact hwhite n t ht])
      hfZ (by rw [hQstart]; exact htube.1) hQpre hQend hQforce
    have hcell : ∀ t, evol x (a+t) (i+1) = (f t).testBit 0 := by
      intro t
      simpa only [f, Int.ofNat_zero, Int.add_zero] using
        ((Rule30FiniteStripsResearch.enc_encRow K (a+t) i).2 0 (by omega)).symm
    unfold Rule30FiniteMaskedJen.orCol
    rw [hblock n s hs]
    change ((if s<r then false else u.getD (s-r) false) || evol x (a+s) (i+1)) = g s
    by_cases hsr : s < r
    · rw [if_pos hsr, Bool.false_or, hcell, hwhitebits s hsr]
      simp only [g, if_pos hsr]
    · rw [if_neg hsr]
      rw [show g s = (u.getD (s-r) false || c (s-r)) by simp only [g, if_neg hsr]]
      cases hu : u.getD (s-r) false
      · simp only [Bool.false_or]
        rw [hcell]
        have hh := htube.2 (s-r) (by omega) hu
        simpa only [show r+(s-r)=s by omega] using hh
      · rfl
  have hor : ∀ t, T ≤ t → Rule30FiniteMaskedJen.orCol x i t = g ((t-T)%(r+u.length)) := by
    intro t ht
    have hd := Nat.div_add_mod (t-T) (r+u.length)
    have hh := hphase ((t-T)/(r+u.length)) ((t-T)%(r+u.length)) (Nat.mod_lt _ (by omega))
    have heq : T+(t-T)/(r+u.length)*(r+u.length)+(t-T)%(r+u.length)=t := by
      rw [Nat.mul_comm ((t-T)/(r+u.length))]
      omega
    rwa [heq] at hh
  exact Rule30FiniteMaskedJen.orCol_not_eventuallyPeriodic hlo hzero i
    ⟨T, r+u.length, by omega, hperiod⟩
    ⟨T, r+u.length, by omega, fun t ht => by
      rw [hor t ht, hor (t+(r+u.length)) (by omega),
        show t+(r+u.length)-T=(t-T)+(r+u.length) by omega, Nat.add_mod_right]⟩

end Ruliology.CellularAutomata.Rule30BackwardTubeResearch

/- Source: Ruliology.CellularAutomata.Rule30WhitePaddingVacuumCriterionResearch -/
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

/- Source: Ruliology.CellularAutomata.Rule30BackwardVacuumResearch -/
/-!
# Backward vacuum obstructions for white-padding families

A finite chain of predecessor implications, starting with the empty set and
ending at the vacuum, proves that no strip can follow a fixed terminal block
and end white. Placing that block at the end of an arbitrarily long white run
and a fixed pulse gives a padding exclusion, without forward reachable-set
stabilization or enumeration of padding lengths.
-/
namespace Ruliology.CellularAutomata.Rule30BackwardVacuumResearch
open Rule30Jen Rule30Realization Rule30StripCertificates
open Rule30WhitePulseResearch Rule30BackwardTubeResearch
open Rule30WhitePaddingVacuumCriterionResearch

/-- Replay predecessor implications along an actual driven strip. -/
theorem enc_backwards {x : Int → Bool} {K : Nat} {i : Int} :
    ∀ (w : List Bool) (t : Nat) (Q : Nat → Nat),
      (∀ j, j < w.length → preCheck K (w.getD j false) (Q j) (Q (j+1)) = true) →
      (∀ j, j < w.length → evol x (t+j) i = w.getD j false) →
      (Q w.length).testBit (Rule30FiniteStripsResearch.encRow x (t+w.length) i K) = true →
      (Q 0).testBit (Rule30FiniteStripsResearch.encRow x t i K) = true
  | [], t, Q, _, _, h => by simpa using h
  | a :: w, t, Q, hpre, hdriver, hend => by
    have hnext := enc_backwards (x := x) (K := K) (i := i) w (t+1) (fun j => Q (j+1))
      (fun j hj => by simpa [List.getD_cons_succ, Nat.add_assoc] using hpre (j+1) (by simp; omega))
      (fun j hj => by
        have h := hdriver (j+1) (by simp; omega)
        simpa only [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend)
    exact enc_backward (by simpa using hpre 0 (by simp))
      (by simpa using hdriver 0 (by simp)) (by simpa using hnext)

/-- Empty initial predecessor set certifies that the block cannot end at the vacuum. -/
theorem no_vacuum_of_backward_certificate {x : Int → Bool} (i : Int)
    (w : List Bool) (K : Nat) (Q : Nat → Nat)
    (hstart : Q 0 = 0) (hend : Q w.length = 1)
    (hpre : ∀ j, j < w.length → preCheck K (w.getD j false) (Q j) (Q (j+1)) = true)
    (t : Nat) (hdriver : ∀ j, j < w.length → evol x (t+j) i = w.getD j false) :
    Rule30FiniteStripsResearch.encRow x (t+w.length) i K ≠ 0 := by
  intro hz
  have hlast : (Q w.length).testBit
      (Rule30FiniteStripsResearch.encRow x (t+w.length) i K) = true := by
    rw [hend, hz]
    decide
  have h := enc_backwards w t Q hpre hdriver hlast
  rw [hstart, Nat.zero_testBit] at h
  contradiction

/-- A finite obstruction for `0^N u` excludes every `0^r u` with sufficiently large r.
No stable forward set is needed; all boundary histories and all initial strips are covered. -/
theorem no_padding_of_backward_certificate {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (K N : Nat) (Q : Nat → Nat)
    (hstart : Q 0 = 0) (hend : Q (N+u.length) = 1)
    (hpre : ∀ j, j < N+u.length →
      preCheck K ((List.replicate N false ++ u).getD j false) (Q j) (Q (j+1)) = true)
    (r : Nat) (hrN : N ≤ r) (hrpulse : 10*u.length+11 ≤ r)
    (hrwidth : K+9*(u.length+1) ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ u) := by
  intro hword
  obtain ⟨T, hT, hwhite⟩ := white_padding_forces_early_white hlo hzero i u r hrpulse hword
  let w := List.replicate N false ++ u
  have hlen : w.length = N+u.length := by simp [w]
  have hdriver : ∀ s, s < w.length → evol x (T+(r-N)+s) i = w.getD s false := by
    intro s hs
    rw [hT _ (by omega), show T+(r-N)+s-T = r-N+s by omega,
      Nat.mod_eq_of_lt (by rw [hlen] at hs; omega), padding_getD, padding_getD]
    by_cases hsN : s < N
    · simp [hsN, show r-N+s < r by omega]
    · simp [hsN, show ¬r-N+s < r by omega, show r-N+s-r = s-N by omega]
  have hnz := no_vacuum_of_backward_certificate i w K Q hstart
    (by simpa only [hlen] using hend) (by simpa only [hlen] using hpre) (T+(r-N)) hdriver
  have htime : T+(r-N)+w.length = T+(r+u.length) := by rw [hlen]; omega
  rw [htime] at hnz
  have he := Rule30FiniteStripsResearch.enc_encRow (x := x) K (T+(r+u.length)) i
  obtain ⟨j, hjK, hjblack⟩ := enc_nonzero_has_black he hnz
  have hboundary : ∀ s, s < j → evol x (T+(r+u.length)+s) i = false := by
    intro s hs
    rw [hT _ (by omega), show T+(r+u.length)+s-T = s+1*(r+u.length) by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega), padding_getD]
    simp [show s < r by omega]
  have hb := black_reaches_boundary x j i (T+(r+u.length)) hboundary hjblack
  have hw := hwhite 1 j (by omega)
  simp only [Nat.one_mul] at hw
  rw [hb] at hw
  contradiction

end Ruliology.CellularAutomata.Rule30BackwardVacuumResearch

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100001DefsResearch -/
/-! Generated exact predecessor sets for `0^12 100001` at width 11.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 11
def N : Nat := 12
def tail : List Bool := [true,false,false,false,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 1317989400684132247985462012217008492691201352246603794343706666106002621345561402409288057184803891421955702295376321167301153177543164830484060369180090017640453495090693794266442291580023684417164027872494288824460186556094461377712526642456239223829354337386792673889867678111635871950739338192516214902167506932502668247458716151002211656322019560292365041312606140162746987742145281007848629457461482662396370400050857265093955131417747864622795962383692493719340178441553202898291525157677655586689669236231444940542635973249732161923962974338102025256960
  | 2 => 1751908409537131537220509645351687597690304110853111572994449976845956819751541616602568796259317428464425605223064365804210081422215355425149431390635151955247955156636234741221447435733643262808668929902091770093793903262101427020667245404086806376697406385616626656709576385194849683752141293079934664734130970765878715171136162413072204924748873679065711426447998850066778333718121991964513739512673072339149010837460911739847867210523319581621310970316642246779308497122238906298733418426677374861649143537026598176315370698624028790832359356342725644751882551273418615338243510404238335279104
  | 3 => 27373568899017680269070463208620118713911001732079868345900368032400627398718725292926268515275851627369364831330611136320742589481102451961246789098172553796310440059930898937831532899140431697171996589133372471298476111108549982396631949032816042695338510810450306688361361341374187746597130687730785433918035877307301201106010546800269207441184151848083044844303430585173620321866859358449430993512509965788634300449476566452937846926468905379725292059362881641023577917146879476653395984596381509820407536177924414733086977494570204801516147034391649652224148646014048795380196145249967407104
  | 4 => 2830360686206494015618260612961201965531482417425069711887864957172916206599794486414315782576699888824556990922729544316721005326280942714130736553281220605850220879759521892631204991795510498766854180024563807712780964482489126000367039514864275232218049309336693170010183686314883550041185613819885718530151534752233734599534650355749042532377018848119517090447662054959434547496636676416064070556996847636463649993555483457119191347189016081390518293520439276270554224449952689924981210638426984079698226366130714716757286084027081508215918264722236709263864517099520
  | 5 => 1593375729078624757834311285001526599239683186684251774969581917460247882416775459467729816104120843283852369170877115390986064722139528607288195340735039504592972721064074653105784049741096097203529696892371133786586341040034582622191081752466667455207243968322294712819735780160185363709119737418408925362049216839850670171528013069776779806535708934815713683122307015609784909439068218467984800170799506292306562754867660108573992190874872086852000300810531658481141782231079706261516811971912210821616689124451049910811102070019864820610282075891119598576153701166643239162057064448
  | 6 => 2019812879927269695613778158893852118390193932184884169330400842536360511893303688708883175411331825373449152297652616112775356600017716672122884917828526732719753555478493975704922126600471118222486536967484669092991959316674880811796692224832047175220689896161960929390130199367541192940215261419604488471375611583581058129598537930637734853402721520805713313419533382680613906910021484959699342212577464066211683532652466710055031688217906696524524607917542306644685496490691327395379778286261955338321480196855004102422073736833122866441729016826043160173602112978086501469171658339862002975324536438520731926528
  | 7 => 505939456621781934182333634262711907723457786510614666702623247608958432828961229629170052401352843063304833797108182197240487785100483631355172060168818570002500441461660283223929116715087128073061495400438903707492336731580555441582045701300990582485412814383512484312848985549011221308746612487502741102968009902776019813253842167705620865892699313341877923170745709359194414733039710890254395680040380733763588402229843144029568297994650436808391462690767427205660215894342879588368381589993953108201414428725717925962777241424396136997374870267200708853195210496731855839994504982316700812617672310194540905540
  | 8 => 1009921849677805655225254357077489938146191822121588806868201500524550573448193004328724958002615625331404071737897323981654162684115458824432464128529597219200397118068895536435884805070325813758820581627543053543453842986212552146092355020385681425497659370193976100491742320612630459033107954455537721141518009503268422745401285553931348182057017460061368651354148456044250017145109099486428100134439066631947684388580153036472869707463700120141612825757511010159647112092272933537436840100902753041220177504414685346630591378278970157520096476549435752021173022630313927549285822303016111742200212229507931703424
  | 9 => 1972473515094665972944023235392453122585699625837126710945455653535440377128167168774243250215021573711469602107049439764163021080099563470025651739763740444058521001518386462215310814495305163478574112609874223312128151189635089053992185973495524787023921700533499026425388397061497358404760372959632548679801455471819096320843650858518863340052021255430261145898979253761549615526244139707783754325870462549774469639943459598820907235336832665409791113128963946854181388843912570405317273021186370422831888782765863268725037733750233357483987831773113937857583047095362241513749976816850895043503907293567648256
  | 10 => 246559189386833246618002904424056640346398767971044437844205305923353721326884737972088398179181625952391585344234323973285353864258029785682259204724273073597407738807842275606582135946962245378390103032097460789847522003189594174891680586826420491519968853131627906189734625984040426066727338297659926022487073893672833801092980733532938775779034357733565374209031747996072849505491072212103550671273919406725717414261079770780384834268732515426723904768350380442150641388100633098617297770558007055764080895297501874134621834990018375355320612171405830890492677232368552636823944100558567737658916539318992896
  | 11 => 28703274225248587860240897297057851755587621029967813031908150430214378589581920526192182724891406339481426807256947066629220304248533733167513788959496673492964260134865600219034330380914610977078080141289898597726869584683415635384000362852907650881640438611102775213230872427219883869342612965973874165649826778203406694488326666924691466871541626497031899050487929281529433379840931762485318641860592098023494269930183318087115704742279863533651596777818891671248812825360119267838522680347285861397556024324796370832440833190287544892258524849757080987807583546805464360284314387456169567556993024
  | 12 => 213856007023575627102112993817344677452429701031873971312867207894190981995160798577930288867813623576064124652033302683157633938723065777897569881568516501091772495715321587590954279962874156307868271422755888165618541122588710089953350157619489476458875169256662749859788536092771915015168817978984603026852523165723365611206807065226702155868858523483404475445065903425598236306175238049571458475783762100294437273949870662860301108011928454444745527490200455490515753234728805730997210095575395109465733580133584092252619513974493134338434166406877891818646831406589803732665538850516369424
  | 13 => 63119152483029311134208743532558499922742388026788054750254580913134092068101349400775784006880690358767027267425582069324452263965802580263844067848947909939171524277967751204727309931880629493052765259975288332760053917097130950328367609215699072651551763020763561149847707824718829676511346343302733681546072348037553882961182317625683135884466224597774042155451614037851309531164820339911551456875797023580899353910008359664207006616463745096348849301413262110625416495270841626044754631658390983576283341312813449794672160373154548036741182251054030066653459377613962178359692849381476228694163205918482792448
  | 14 => 157116580091015368459875823523641645037079018622232775651791514674285674485261122730377591974181566269709146733693208801868779954374066038959587047164187945587589305244576910023937953327072539218243905702460144669954918486219555720532173395667103935610549145058165657002716035583194357997901607959950386793095812407332950240925825308105618911502768423083330841525583287057491932048768979126041244698978214457646966894301225383105373575423336244962119140903159838026092434001036943447715849860529464190001853824803704259455893376738401107802378923367596032
  | 15 => 2030684202530045705555113628492582013902486762858899984101222940720833585354594068410377813909696557106868748039287806440327756032912128284695211906920520342013207884701066631582134258521945358626603732205641463607185100031672051229116235490597863813854851788309325872133508186377795228505841685013845492411677703316134923376236733581269153875124534380113883712554707558946274649125223296912298659973934033352297156342401790425641982883703750601121688798865165442793585729649675936444892108805080509772897461425651584812126830592
  | 16 => 22764757236272150845448608801544890529699448070214573731542130224001885731721805946360208679001072341752808202824217284477494812905121433368607413453405435241035171026302307078844081862378898986287227723031901649882194160845698588267699583066325683519210396334860609957459378162416780929141270829595389495389133348556933419291404463361528399509576771317627518967750592485867313959666142869543658007128819325087866638628344845905209826777292546113606776832405698212781255130446003437568
  | 17 => 16158503035655503650357438344334975980222051334857742016065172713762327569433945446598600705761456731844358980460949009747059779575245460547544076193224141560315438683650498045875098875194826053398028819192033784138396109321309878080919047169238085235290822926018152521443787945770532904303776199561965192761047051351577287005728952652821735984108986866610276357675617870244379434256980638641483535093292326373531858799166625357628570460558031263448272521936380677802446789067842847500729660664088708794565812766370851851942073975347730759844719138465132286353476323058907951442632862271715932249195604970341910183936
  | 18 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100001Steps0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100001Steps1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100001Steps2Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step8 : preCheck K ((List.replicate N false ++ tail).getD 8 false) (Q 8) (Q 9) = true := by decide +kernel
theorem step9 : preCheck K ((List.replicate N false ++ tail).getD 9 false) (Q 9) (Q 10) = true := by decide +kernel
theorem step10 : preCheck K ((List.replicate N false ++ tail).getD 10 false) (Q 10) (Q 11) = true := by decide +kernel
theorem step11 : preCheck K ((List.replicate N false ++ tail).getD 11 false) (Q 11) (Q 12) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100001Steps3Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step12 : preCheck K ((List.replicate N false ++ tail).getD 12 false) (Q 12) (Q 13) = true := by decide +kernel
theorem step13 : preCheck K ((List.replicate N false ++ tail).getD 13 false) (Q 13) (Q 14) = true := by decide +kernel
theorem step14 : preCheck K ((List.replicate N false ++ tail).getD 14 false) (Q 14) (Q 15) = true := by decide +kernel
theorem step15 : preCheck K ((List.replicate N false ++ tail).getD 15 false) (Q 15) (Q 16) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100001Steps4Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step16 : preCheck K ((List.replicate N false ++ tail).getD 16 false) (Q 16) (Q 17) = true := by decide +kernel
theorem step17 : preCheck K ((List.replicate N false ++ tail).getD 17 false) (Q 17) (Q 18) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100001Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9
  · exact step10
  · exact step11
  · exact step12
  · exact step13
  · exact step14
  · exact step15
  · exact step16
  · exact step17

/-- Uniform column exclusion, for every padding length at least 74. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 74 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100011DefsResearch -/
/-! Generated exact predecessor sets for `0^0 100011` at width 5.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100011
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 5
def N : Nat := 0
def tail : List Bool := [true,false,false,false,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 16
  | 5 => 2147516416
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100011Steps0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100011
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100011Steps1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100011
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100011Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100011
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100101DefsResearch -/
/-! Generated exact predecessor sets for `0^4 100101` at width 7.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100101
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 7
def N : Nat := 4
def tail : List Bool := [true,false,false,true,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 4722366482869645213696
  | 2 => 21267647932558653967613834469092360192
  | 3 => 5316911983139663565690434912111296576
  | 4 => 10141204801825835212523381458944
  | 5 => 309485009893402662762708992
  | 6 => 75557863725914324467728
  | 7 => 332306998946228968243966163579584512
  | 8 => 9444732965739290689536
  | 9 => 170141183460469231740910675752738881536
  | 10 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100101Steps0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100101
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100101Steps1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100101
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100101Steps2Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100101
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step8 : preCheck K ((List.replicate N false ++ tail).getD 8 false) (Q 8) (Q 9) = true := by decide +kernel
theorem step9 : preCheck K ((List.replicate N false ++ tail).getD 9 false) (Q 9) (Q 10) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100101Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100101
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100111DefsResearch -/
/-! Generated exact predecessor sets for `0^5 100111` at width 8.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100111
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 8
def N : Nat := 5
def tail : List Bool := [true,false,false,true,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 1606938044258990275541962092341162602526925360265662480515072
  | 2 => 7237005577332262213973186563042994240850641689535093906432559913459056115712
  | 3 => 25206486656162139942283408814551425115726423286211848175680
  | 4 => 3450873173395281893717377931835411013689777664060010308813497034604544
  | 5 => 210624583337114373395836142479626796398655807444784530366809505792
  | 6 => 3370096177428662549712438821866328563869674290033663802344229306368
  | 7 => 14134776518227275503921912379727790871922952195198546151671126788784783360
  | 8 => 220855883097298041197912187592864814479084524216769223218767087739600896
  | 9 => 68719476736
  | 10 => 57896044618658097711785492504343953926805133516280751251460479307672448925696
  | 11 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100111Steps0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100111
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100111Steps1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100111
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100111Steps2Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100111
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step8 : preCheck K ((List.replicate N false ++ tail).getD 8 false) (Q 8) (Q 9) = true := by decide +kernel
theorem step9 : preCheck K ((List.replicate N false ++ tail).getD 9 false) (Q 9) (Q 10) = true := by decide +kernel
theorem step10 : preCheck K ((List.replicate N false ++ tail).getD 10 false) (Q 10) (Q 11) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100111Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100111
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9
  · exact step10

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C100111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101001DefsResearch -/
/-! Generated exact predecessor sets for `0^8 101001` at width 8.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101001
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 8
def N : Nat := 8
def tail : List Bool := [true,false,true,false,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 1606938044258990275541962092341162602526925360265662480515072
  | 2 => 392318858461667547761004486883037804972858128243487670272
  | 3 => 421249191782635688338395187855910905047545647780953685456731504640
  | 4 => 1766847064791239833937556495156832568144945707417758698693990480212918272
  | 5 => 904632706752666235962034791112005348677772482317568746437442502369545814272
  | 6 => 226156424344289340020940673535407586574198466656875044685142784755575586816
  | 7 => 1725437409449919607461710043402296785520141325815789610988888494571524
  | 8 => 842498333348457493583344265025506424433759966595489862602920558592
  | 9 => 1606938044258990275541962092341162602526925360265662480515072
  | 10 => 392318858461667547761004486883037804972858128243487670272
  | 11 => 842498333348457493583344265025506424433759966595489862602920558592
  | 12 => 3213876088517980640286904978804817771196723811124770984951808
  | 13 => 57896044618658097711785492504343953926805133516280751251460479307672448925696
  | 14 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101001Steps0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101001Steps1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101001Steps2Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step8 : preCheck K ((List.replicate N false ++ tail).getD 8 false) (Q 8) (Q 9) = true := by decide +kernel
theorem step9 : preCheck K ((List.replicate N false ++ tail).getD 9 false) (Q 9) (Q 10) = true := by decide +kernel
theorem step10 : preCheck K ((List.replicate N false ++ tail).getD 10 false) (Q 10) (Q 11) = true := by decide +kernel
theorem step11 : preCheck K ((List.replicate N false ++ tail).getD 11 false) (Q 11) (Q 12) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101001Steps3Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step12 : preCheck K ((List.replicate N false ++ tail).getD 12 false) (Q 12) (Q 13) = true := by decide +kernel
theorem step13 : preCheck K ((List.replicate N false ++ tail).getD 13 false) (Q 13) (Q 14) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101001Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101001
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9
  · exact step10
  · exact step11
  · exact step12
  · exact step13

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101011DefsResearch -/
/-! Generated exact predecessor sets for `0^0 101011` at width 5.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101011
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 5
def N : Nat := 0
def tail : List Bool := [true,false,true,false,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 16
  | 5 => 2147516416
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101011Steps0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101011
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101011Steps1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101011
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101011Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101011
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101101DefsResearch -/
/-! Generated exact predecessor sets for `0^0 101101` at width 10.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101101
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 10
def N : Nat := 0
def tail : List Bool := [true,false,true,true,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 4249103942534136789516705652419749018636744941816255385595553105603228478886817941913300018121834285351114635889972008122772634701221663761282709153744371630289981031815224393163866112
  | 3 => 9516908214257811601907599988159363584840065290620124537956939899622020205826587990689077212775400643774711832257235027522909345571487396529861315719055326314814455073792347245307224163568933595697422149216092441761606229067073230804364931451679374391341388606002756129612438214868467712
  | 4 => 126633165554229521438977290762059361297987250739820462036000284719563379254544315991201997343356439034674007770120263341747898897565145822484177753904735444846393260786157879296
  | 5 => 89884656743115795386465259539451236680898848947115328636715040578866337902750481566354238661203768010560056939935696678829394884407208311246423715319737068892787911683731292425163608903546110799409451772239191746199797202053246477510444956207562702033389100358222242362999049846181264125702651381636615110656
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101101Steps0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101101
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101101Steps1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101101
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101101Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101101
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

/-- Uniform column exclusion, for every padding length at least 73. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 73 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101111DefsResearch -/
/-! Generated exact predecessor sets for `0^6 101111` at width 6.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101111
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 6
def N : Nat := 6
def tail : List Bool := [true,false,true,true,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 256
  | 2 => 1152921504875282432
  | 3 => 288230376218820676
  | 4 => 549755815936
  | 5 => 144115205289279488
  | 6 => 36028797027385344
  | 7 => 281474976776192
  | 8 => 1099528405248
  | 9 => 35184908959752
  | 10 => 68719476736
  | 11 => 9223372039002259456
  | 12 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101111Steps0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101111
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101111Steps1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101111
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101111Steps2Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101111
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step8 : preCheck K ((List.replicate N false ++ tail).getD 8 false) (Q 8) (Q 9) = true := by decide +kernel
theorem step9 : preCheck K ((List.replicate N false ++ tail).getD 9 false) (Q 9) (Q 10) = true := by decide +kernel
theorem step10 : preCheck K ((List.replicate N false ++ tail).getD 10 false) (Q 10) (Q 11) = true := by decide +kernel
theorem step11 : preCheck K ((List.replicate N false ++ tail).getD 11 false) (Q 11) (Q 12) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101111Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101111
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9
  · exact step10
  · exact step11

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C101111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110011DefsResearch -/
/-! Generated exact predecessor sets for `0^0 110011` at width 5.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110011
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 5
def N : Nat := 0
def tail : List Bool := [true,true,false,false,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 16
  | 5 => 2147516416
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110011Steps0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110011
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110011Steps1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110011
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110011Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110011
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110101DefsResearch -/
/-! Generated exact predecessor sets for `0^2 110101` at width 7.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110101
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 7
def N : Nat := 2
def tail : List Bool := [true,true,false,true,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 65536
  | 2 => 1329227995784920595342347523963486208
  | 3 => 42701449364590422419349652019974512680
  | 4 => 75557863725914324467728
  | 5 => 332306998946228968243966163579584512
  | 6 => 9444732965739290689536
  | 7 => 170141183460469231740910675752738881536
  | 8 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110101Steps0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110101
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110101Steps1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110101
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110101Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110101
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110111DefsResearch -/
/-! Generated exact predecessor sets for `0^0 110111` at width 8.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110111
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 8
def N : Nat := 0
def tail : List Bool := [true,true,false,true,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 14134776518227275503921912379727790871922952195198546151671126788784783360
  | 3 => 220855883097298041197912187592864814479084524216769223218767087739600896
  | 4 => 68719476736
  | 5 => 57896044618658097711785492504343953926805133516280751251460479307672448925696
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110111Steps0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110111
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110111Steps1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110111
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110111Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110111
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C110111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111001DefsResearch -/
/-! Generated exact predecessor sets for `0^0 111001` at width 5.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111001
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 5
def N : Nat := 0
def tail : List Bool := [true,true,true,false,false,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 524320
  | 2 => 268439552
  | 3 => 134219904
  | 4 => 33817088
  | 5 => 2147516416
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111001Steps0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111001Steps1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111001
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111001Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111001
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111011DefsResearch -/
/-! Generated exact predecessor sets for `0^0 111011` at width 5.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111011
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 5
def N : Nat := 0
def tail : List Bool := [true,true,true,false,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 16
  | 5 => 2147516416
  | 6 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111011Steps0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111011
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111011Steps1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111011
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111011Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111011
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111011

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111111DefsResearch -/
/-! Generated exact predecessor sets for `0^2 111111` at width 6.
The target is the vacuum; the initial predecessor set is empty. -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111111
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 6
def N : Nat := 2
def tail : List Bool := [true,true,true,true,true,true]
def Q : Nat → Nat
  | 0 => 0
  | 1 => 256
  | 2 => 1152921504875282432
  | 3 => 576469548530665600
  | 4 => 1099528405248
  | 5 => 35184908959752
  | 6 => 68719476736
  | 7 => 9223372039002259456
  | 8 => 1
  | _ => 0
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111111Steps0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111111
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step0 : preCheck K ((List.replicate N false ++ tail).getD 0 false) (Q 0) (Q 1) = true := by decide +kernel
theorem step1 : preCheck K ((List.replicate N false ++ tail).getD 1 false) (Q 1) (Q 2) = true := by decide +kernel
theorem step2 : preCheck K ((List.replicate N false ++ tail).getD 2 false) (Q 2) (Q 3) = true := by decide +kernel
theorem step3 : preCheck K ((List.replicate N false ++ tail).getD 3 false) (Q 3) (Q 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111111Steps1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111111
open Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step4 : preCheck K ((List.replicate N false ++ tail).getD 4 false) (Q 4) (Q 5) = true := by decide +kernel
theorem step5 : preCheck K ((List.replicate N false ++ tail).getD 5 false) (Q 5) (Q 6) = true := by decide +kernel
theorem step6 : preCheck K ((List.replicate N false ++ tail).getD 6 false) (Q 6) (Q 7) = true := by decide +kernel
theorem step7 : preCheck K ((List.replicate N false ++ tail).getD 7 false) (Q 7) (Q 8) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111111

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111111Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111111
open Rule30BackwardTubeResearch Rule30BackwardVacuumResearch
theorem pre (j : Nat) (hj : j < N+tail.length) :
    preCheck K ((List.replicate N false ++ tail).getD j false) (Q j) (Q (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by simp [N, tail] at hj; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7

/-- Uniform column exclusion, for every padding length at least 71. -/
theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 71 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  exact no_padding_of_backward_certificate hlo hzero i tail K N Q (by rfl) (by rfl) pre
    r (by simp [N]; omega) (by simp [tail]; omega) (by simp [K, tail]; omega)
end Ruliology.CellularAutomata.Rule30SixTailCertificatesResearch.C111111

/- Source: Ruliology.CellularAutomata.Rule30RestrictedBackwardTubeResearch -/
/-! Backward white transitions need only be checked on the invariant white set. -/
namespace Ruliology.CellularAutomata.Rule30RestrictedBackwardTubeResearch
open Rule30Jen Rule30Realization Rule30StripCertificates Rule30FiniteStripsResearch
open Rule30WhitePulseResearch Rule30ZeroPredecessorResearch Rule30WhitePaddingResearch
open Rule30BackwardTubeResearch

def restrictedPreCheck (K : Nat) (a : Bool) (Z Q R : Nat) : Bool :=
  allBelow (fun s => !Z.testBit s ||
    ((! R.testBit (stripStep K a false s) || Q.testBit s) &&
    (! R.testBit (stripStep K a true s) || Q.testBit s))) (2^K)

theorem restrictedPreCheck_sound {K Z Q R s : Nat} {a z : Bool}
    (h : restrictedPreCheck K a Z Q R = true) (hs : s < 2^K)
    (hZ : Z.testBit s = true)
    (ht : R.testBit (stripStep K a z s) = true) : Q.testBit s = true := by
  have hh := allBelow_spec h s hs
  rw [hZ, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hh
  cases z
  · have hh := hh.1
    rw [ht, Bool.not_true, Bool.false_or] at hh
    exact hh
  · have hh := hh.2
    rw [ht, Bool.not_true, Bool.false_or] at hh
    exact hh

theorem white_tube_forces (K r L Z : Nat) (Q : Nat → Nat) (b : Nat → Bool)
    (f : Nat → Nat) (z : Nat → Bool) (hL : L ≤ r)
    (hf : ∀ t, t ≤ r → f t < 2^K)
    (hstep : ∀ t, t < r → f (t+1) = stripStep K false (z t) (f t))
    (hZ : ∀ t, t ≤ r → Z.testBit (f t) = true)
    (hend : (Q 0).testBit (f r) = true)
    (hpre : ∀ d, d < L → restrictedPreCheck K false Z (Q (d+1)) (Q d) = true)
    (hzero : Q L = 1)
    (hforce : ∀ d, d ≤ L → colConst K (Z &&& Q d) (b d) = true) :
    ∀ s, s < r → (f s).testBit 0 = if r-s ≤ L then b (r-s) else false := by
  have hQ : ∀ d, d ≤ L → (Q d).testBit (f (r-d)) = true := by
    intro d
    induction d with
    | zero => simpa using hend
    | succ d ih =>
      intro hd
      have hi := ih (by omega)
      have hs : r-(d+1)+1 = r-d := by omega
      rw [← hs, hstep (r-(d+1)) (by omega)] at hi
      exact restrictedPreCheck_sound (hpre d (by omega)) (hf _ (by omega)) (hZ _ (by omega)) hi
  have hz : f (r-L) = 0 := by
    have hh := hQ L (by omega)
    rw [hzero] at hh
    exact Nat.testBit_one_eq_true_iff_self_eq_zero.mp hh
  have hzbefore : ∀ s, s ≤ r-L → f s = 0 := by
    have hrec : ∀ d, d ≤ r-L → f (r-L-d) = 0 := by
      intro d
      induction d with
      | zero => simpa using hz
      | succ d ih =>
        intro hd
        have hi := ih (by omega)
        have hs : r-L-(d+1)+1 = r-L-d := by omega
        rw [← hs, hstep _ (by omega)] at hi
        exact stripStep_zero_predecessor (hf _ (by omega)) hi
    intro s hs
    have hh := hrec (r-L-s) (by omega)
    simpa only [show r-L-(r-L-s)=s by omega] using hh
  intro s hs
  split
  · rename_i hd
    have hh := colConst_intersection (hforce (r-s) hd) (hf s (by omega)) (hZ s (by omega))
      (by simpa only [show r-(r-s)=s by omega] using hQ (r-s) hd)
    exact hh
  · rw [hzbefore s (by omega), Nat.zero_testBit]

/-- A stable white set plus a backward tube from the vacuum excludes an arbitrary tail.
Unlike a forward forcing certificate, the tube may condition on the next period's vacuum. -/
theorem no_padding_of_endpoint_tube {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (K L Z : Nat) (Q P S : Nat → Nat)
    (b c : Nat → Bool) (hK : 1 ≤ K)
    (hZzero : Z.testBit 0 = true) (hZfixed : image K false Z = Z)
    (hSzero : S 0 = Z) (hPend : P u.length = 1) (hQstart : Q 0 = P 0)
    (hQend : Q L = 1)
    (hQpre : ∀ d, d < L → restrictedPreCheck K false Z (Q (d+1)) (Q d) = true)
    (hPpre : ∀ j, j < u.length → preCheck K (u.getD j false) (P j) (P (j+1)) = true)
    (hSforward : ∀ j, j < u.length → image K (u.getD j false) (S j) = S (j+1))
    (hQforce : ∀ d, d ≤ L → colConst K (Z &&& Q d) (b d) = true)
    (hPforce : ∀ j, j < u.length → u.getD j false = false →
      colConst K (S j &&& P j) (c j) = true)
    (r : Nat) (hrpulse : 10*u.length+11 ≤ r)
    (hrwidth : K-1+9*(u.length+1) ≤ r) (hrL : L ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ u) := by
  intro hword
  obtain ⟨T, hT, _⟩ := white_padding_forces_early_white hlo hzero i u r hrpulse hword
  have hperiod : ∀ t, T ≤ t → evol x (t+(r+u.length)) i = evol x t i := by
    intro t ht
    rw [hT t ht, hT (t+(r+u.length)) (by omega),
      show t+(r+u.length)-T=(t-T)+(r+u.length) by omega, Nat.add_mod_right]
  have hblock : ∀ n s, s < r+u.length → evol x (T+n*(r+u.length)+s) i =
      if s < r then false else u.getD (s-r) false := by
    intro n s hs
    rw [hT _ (by omega), show T+n*(r+u.length)+s-T=s+n*(r+u.length) by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs, padding_getD]
  have hwhite : ∀ n s, s < r → evol x (T+n*(r+u.length)+s) i = false := by
    intro n s hs
    rw [hblock n s (by omega), if_pos hs]
  have hstarts : ∀ n, Rule30FiniteStripsResearch.encRow x (T+n*(r+u.length)) i K = 0 := by
    intro n
    apply encRow_zero_of_prefix
    intro j hj
    have hh := periodic_white_cycles_force_empty_prefix hlo hzero i T r u.length hrpulse
      hperiod hwhite n (j+1) (by omega) (by omega)
    simpa only [show i+1+(j:Int)=i+((j+1:Nat):Int) by omega] using hh
  let g : Nat → Bool := fun s =>
    if s < r then (if r-s ≤ L then b (r-s) else false)
    else u.getD (s-r) false || c (s-r)
  have hphase : ∀ n s, s < r+u.length →
      Rule30FiniteMaskedJen.orCol x i (T+n*(r+u.length)+s) = g s := by
    intro n s hs
    let a := T+n*(r+u.length)
    let f : Nat → Nat := fun t => Rule30FiniteStripsResearch.encRow x (a+t) i K
    let z : Nat → Bool := fun t => evol x (a+t) (i+1+K)
    have hf : ∀ t, f t < 2^K := fun t => (Rule30FiniteStripsResearch.enc_encRow K (a+t) i).1
    have hstep : ∀ t, f (t+1) = stripStep K (evol x (a+t) i) (z t) (f t) := by
      intro t
      simpa only [f, z, Nat.add_assoc] using encRow_step x K (a+t) i
    have hfzero : f 0 = 0 := by simpa only [f, a, Nat.add_zero] using hstarts n
    have hfend : f (r+u.length) = 0 := by
      have hh := hstarts (n+1)
      simpa only [f, a, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hh
    have hfZ : ∀ t, t ≤ r → Z.testBit (f t) = true := by
      intro t
      induction t with
      | zero => intro _; rw [hfzero]; exact hZzero
      | succ t ih =>
        intro ht
        have hi := ih (by omega)
        have hmem := mem_imageAux (K := K) (a := false) hi (z t) (2^K) (hf t)
        change (image K false Z).testBit (stripStep K false (z t) (f t))=true at hmem
        rw [hZfixed] at hmem
        rw [hstep, show evol x (a+t) i=false by exact hwhite n t (by omega)]
        exact hmem
    have htube := tail_tube_forces K r u P S c f z (fun t _ => hf t)
      (fun j hj => by
        rw [hstep]
        have hh := hblock n (r+j) (by omega)
        simp only [show ¬r+j<r by omega, if_false, Nat.add_sub_cancel_left] at hh
        exact congrArg (fun a' => stripStep K a' (z (r+j)) (f (r+j))) hh)
      (by rw [hPend, hfend]; exact Nat.testBit_one_zero)
      hPpre (by rw [hSzero]; exact hfZ r (by omega))
      (fun j hj => by rw [hSforward j hj]; exact subsetB_self K (S (j+1))) hPforce
    have hwhitebits := white_tube_forces K r L Z Q b f z hrL (fun t _ => hf t)
      (fun t ht => by rw [hstep, show evol x (a+t) i=false by exact hwhite n t ht])
      hfZ (by rw [hQstart]; exact htube.1) hQpre hQend hQforce
    have hcell : ∀ t, evol x (a+t) (i+1) = (f t).testBit 0 := by
      intro t
      simpa only [f, Int.ofNat_zero, Int.add_zero] using
        ((Rule30FiniteStripsResearch.enc_encRow K (a+t) i).2 0 (by omega)).symm
    unfold Rule30FiniteMaskedJen.orCol
    rw [hblock n s hs]
    change ((if s<r then false else u.getD (s-r) false) || evol x (a+s) (i+1)) = g s
    by_cases hsr : s < r
    · rw [if_pos hsr, Bool.false_or, hcell, hwhitebits s hsr]
      simp only [g, if_pos hsr]
    · rw [if_neg hsr]
      rw [show g s = (u.getD (s-r) false || c (s-r)) by simp only [g, if_neg hsr]]
      cases hu : u.getD (s-r) false
      · simp only [Bool.false_or]
        rw [hcell]
        have hh := htube.2 (s-r) (by omega) hu
        simpa only [show r+(s-r)=s by omega] using hh
      · rfl
  have hor : ∀ t, T ≤ t → Rule30FiniteMaskedJen.orCol x i t = g ((t-T)%(r+u.length)) := by
    intro t ht
    have hd := Nat.div_add_mod (t-T) (r+u.length)
    have hh := hphase ((t-T)/(r+u.length)) ((t-T)%(r+u.length)) (Nat.mod_lt _ (by omega))
    have heq : T+(t-T)/(r+u.length)*(r+u.length)+(t-T)%(r+u.length)=t := by
      rw [Nat.mul_comm ((t-T)/(r+u.length))]
      omega
    rwa [heq] at hh
  exact Rule30FiniteMaskedJen.orCol_not_eventuallyPeriodic hlo hzero i
    ⟨T, r+u.length, by omega, hperiod⟩
    ⟨T, r+u.length, by omega, fun t ht => by
      rw [hor t ht, hor (t+(r+u.length)) (by omega),
        show t+(r+u.length)-T=(t-T)+(r+u.length) by omega, Nat.add_mod_right]⟩

end Ruliology.CellularAutomata.Rule30RestrictedBackwardTubeResearch

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001DefsResearch -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30RestrictedBackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 12
def L : Nat := 14
def tail : List Bool := [true,true,false,false,false,true]
def Z : Nat := 131060557730316447329503898206217727879809761597069271913733996279475874809589763070620424643249843930828430085325515782572983618980255281804402574258690246265579053621183691975513708814581801320904968364298039898284142128732017505232010433577410141464383504269579672948791041504789797804752468755337361369327302083757877237700776994810434602288285043826396843836604515327838789710005369973928148844671303507338194926882164864862093242088737631559790761848607113680361226254522505458347687448072597701529629652895419624174140614633122644223908591751723156660329855433551436534427232836907698121287433454905155523501035314522045395129437197217029981059285545149281047125292176264022890340737912904724136335982668278136374703146851777960823557795902610987040001525452649495276308240281517288349394511855511064679480737762293117266181518962363632956329178984238663931907777287952308128905021043175143069957610950498414871355529021895538657990485067830386122752057927529168873922112781876945938248468036047072894449953467292938552845870188548788871317691929127711805134859846987502736026245029063505612163408690222197092189309949017854352804309777502110478155445354738505399513688918214126360864398957702157126871831852913767327566143521
def P : Nat → Nat
  | 0 => 57975229141213356085478346878882020388159566714183304668618033065467661117576574055066927279717479627574162376930294085295046840174772305974211875891259863682639647052008765230415733657198252148944842946754668521707098377633669057827006813325383060026598042729894942658078878226098386050500065432335298805042807626663431413302348828329396253198175083550506980772930870797887910166691493315898287376624028280229149909914884153896555051183452379572910245304783381882291570992608002956145909847438173028279674556705209547136406922874529712471478583751500723356062353420657127047983241303624668788759621457701201480651309106508205317377428077492977538965015076846205054993107809277706375948692583515287644519740035819972355122624157592051977062677520300681040876450378723558474396031590436199418709511052972125796483372251720307367183152935328193580334254462474561332352024340490103808712240221262981640916842799974094535467016628688723865231725452315617413220883723663937280049381674730913797146699840935204727026018354457611260025812656004113875198902606427419458466062452741891539490670261039869844361699116390600397283858659188198538249680120718037299937365536283746933826614670119100521788893993837499575066047807488
  | 1 => 884631792303004538966103260724113936154909488552025335759523501210048328097827480852819662435218856360940939291516351481997219441959744260755718683712880134148828754036215187834462631004129337597977129450907404510292942014355412451002750782561671810988070996709718352286750159799524053444843662451160776526231414766920313826287794884023532031305723084098891035380823559139667567350758521195562081320091005605321188839541434166682096886141218213595952390513573170386103614056438438660825430795298293605123218811532208744125453101663396921268013117065874539135416652020546536978485013380456399478587519471855433321896748888124102758888853954637814901894176240057745653716704431987180199192969463038785195814787139711215097348188045536116248221843061194101820983683790215988657487006336372688936426267394688564604785825180179959976394218171135634214834288042792718004476149951235146359079318436627948359857933384682547888516274685729096898890326055958249550200619092993544302279741181658795550202932041757172004594841972071235284687752003816042571049833452126275853419480098862611535955199023602070734059481473754552758922996741538887593324395284520106839095456400851509537903919487588318256049183444096498295373824
  | 2 => 5077537472704965798543768333233475158913018245888587880176891079882195134751694301570565540936749739572080123312001924711077206108403185135259175012715601904825512855929145452358081567672788570071897505548256649059906747308644856930980666417098763144765125749225092351957134657827484783768049501887439283043992127752344196571830619767462476125718997459601405221760413855603602198024240073696494786390904503427401106587602406176364216332718702419602293044288859851868728823623112775656286829731205879567345985759937278354926736786265636740894987733339336980020100570824514036878980030482370160864434073869288952518914008242815441639208450330923523554258598885472921231335511691894532817500347309879405730585915440375156159990209830581071448240739107864876269390018138882263031330324717896508695906574233761892785918472830434274373098260206715593756794148762827851091769622008884011927196246586762388599157811278778113670258701647432218251165800330539565415693917075187325192974563880383065861144942647987898396960391603856071035812881101741459036022191818708080562967169912118809418354971491874837792806034249660814537217727524893165497953985551477313172870665220768399360
  | 3 => 65625633702078838238765297039289963569546488306699905671820415068609176261488512965683331300344712288802679077419358547103474716881746131862677810176328593617235529690735086359820002734053565608422218312974208973790527458518081863688012116757304729632605119283656921163853111587568506002909481895404354991929970892383477776965875400515698400007360414372460722030523880522229854944725618474168600264943832798296593833709492726965291161986213892266148623791707112581108563349831286549590678438738405815180871721778102955640574704166799126867744670482029484719869176033722552111058433741776614016823307353502859473637052080738888176794852251944265143990785473025760551292221303052255473222420969328033443769584951492265961751035932872851222805198573011640252327268356851843620088780665311669217429923285884659725867905208490775868974420338377471671723021996006726498115314900553109453985689168154487739903326956315225102073223153725143510153598667171719479368489401653241777388062630383418812195974821859841641391993572037371321663361635215005883044387602591685099120237570916205966246367889789070394653661739338505841563749171456420853166368620544
  | 4 => 518234172026405255552493535844883061883637775106250854607949846323748038533172724172402419033600966813101390483466388354883379018477614034820755419195024084626133248165832707035904622372309724531209095382255191697551221137515862382035422817652504307698071660802370144232849494923646062942796680458576149091355815882074576471641411784702136867765973777233317300561855384160679211738617581000819007419751804238036743983241988005137870226273097659478225313594606483973034500232825407019410855546955944699643352886893336766238645080199297988103580483248113038108967381619232123251486084723443726678831704852862417474533199960082125356399965465659077517832213897820464762420691893262824564345544065233223852688208675237003402143556665250847651599085932384204954677229781076801910376828099394558437681207824205913169739382662056070475685082098052281145876116917164214954819757987485365372380938075589069890017078194070263933161019410215682672236386532456737942244473123635200
  | 5 => 522194440706576253345876355358312191289982124523691890192116741641976953985778728424413405967498779170445053357219631418993786719092896803631618043925682638972978488271854999170180795067191859157214035005927973113188159419698856372836167342172293308748403954352901852035642024370059304557233988891799014503343469488440893892973452815095130470299789726716411734651513348221529512507986199933857107770846917779942645743159118957217248367043905936319748237550094520674504208530837546834166925275516486044134775384991808184705966507606898412918594045916828375610659246423184062775112999150206172392431297837246097308511919411459658460916516275128388139287031639186433706843172649681552765665167176485407416810390904144294236366434040516739738455036275051236444679629608791186852451880823546275470766576036962084586009663349889486777984897170803007721972358521389546088941763660385929677807264976523178693594619299151020033656115128594915199395160328438284015166484040013151289690978936900875065247697241542565934354230159918183452136337095790645261574579360261746238075035455059100025373721570856630568171033987937658200940804173551819277637011822685739542270608413789928313531108409313472180603783050108319194119218680280975731375210496
  | 6 => 1
  | _ => 0
def S : Nat → Nat
  | 0 => 131060557730316447329503898206217727879809761597069271913733996279475874809589763070620424643249843930828430085325515782572983618980255281804402574258690246265579053621183691975513708814581801320904968364298039898284142128732017505232010433577410141464383504269579672948791041504789797804752468755337361369327302083757877237700776994810434602288285043826396843836604515327838789710005369973928148844671303507338194926882164864862093242088737631559790761848607113680361226254522505458347687448072597701529629652895419624174140614633122644223908591751723156660329855433551436534427232836907698121287433454905155523501035314522045395129437197217029981059285545149281047125292176264022890340737912904724136335982668278136374703146851777960823557795902610987040001525452649495276308240281517288349394511855511064679480737762293117266181518962363632956329178984238663931907777287952308128905021043175143069957610950498414871355529021895538657990485067830386122752057927529168873922112781876945938248468036047072894449953467292938552845870188548788871317691929127711805134859846987502736026245029063505612163408690222197092189309949017854352804309777502110478155445354738505399513688918214126360864398957702157126871831852913767327566143521
  | 1 => 65530278866583022896106970831985484478223393415316050193237635792374434470805318473939479237554270409851063180407381780411874313985938391010809148880942504757522442178476168735476364322525545874604913478570179590374473124215014744809273180640969849291456999774039497766928685808076017183848914877049862926950525318000959655229172352646361789687896649400057682413631052243892021447229609051513913676399024768691322339166263495641748576846705289290499315275183628141173210257412484857737759578987210449785501987093781258634664302051994732743922335010657019303830892720594131303353260764405265256828950240706983245792868512510077437067644970960862457935378004907043978323614667204118004488954500597994102682111252230230299818347557985019160432251181245393577114684943302600721765955091077180349460577433530992432703156254563786657641220884279127338856494946873711351011183965817161452370434065339525287302926354486990549280290812817385998464065375715171637633108609817079480382479352887326635274842450562338434001607045383332179500557475588988243331604470891440381224202541094428070676975121649704613513752598677255585170025945739410464842517001336872502404198664248547699371646231666624093137119692172016665728112819327422096963801106
  | 2 => 524242230860474355432769179844922973625675062051895082206979009081593841176045557506419699542862096269793153894114881723709058430002280562251272787663402822227045287256143213611180479516078220189566961125016590109494250447544821389090220324997177575231525764118656491578472150272258452528159595682699447560887978343735335571621064579641809483474404903394485589455860152417091078041185870716346225689269039375423399500358063055344867707168900902363243589370735282734743090152359540720200397126769973234669716334985416010654038724985037935719002439861953588563647740003076289308341674197511850633182790865688479076278508691419036092756433164683815102251989479961609817296834956414931682563915376087492371461723543738158499289881637642444991586730328173287518068030653921370504566882263465328097947045458855283387142511200357175601339943988830570558559885782498950792327637015348739515371422643542752260010328913422176580419289244153295326242121436550218590344532181128145989938937541534648200174860137488888946070095406262140424613384381384337931560003462433653997764620924641564383216024711837122098662621601858125909427930495273164085882741860846948195817018809481850198967109601788010022196447325912252021765728516530542472555692164
  | 3 => 8191284985367475990943134174679740341977903446486252262330940139565006903444236414152891605305778272769098016177782030066301241723506998810664204113770413501430587214519180373879551995390600309657610986785844098331341156499097813699808140882914494087825961726420281856818674836880804593274147483985183570433649524440667372791892024008960352718133584360084753467670726694937987131118566521081631150656038637541304128432823215410651571646700831226077571335684292106859726075700614066339514584066619026222088570765263239016407105922500902256211992806234602535580647987513519318187944939037251947490964159502468248873688386170422633795532286827749102200986930777227127111857787206429489572504485156854654470644597470793240624367734394269722184338452706336534218915806127672582674574378001166968276789164100698459607614674711540478688372490249453459910197408752323775911620550710431878874465252864905775105665350528549350949603791840966353033742617740437949983103962595502528757835608494515709387100258275903753574830069788872883310990976108405297961777553284374853676167717768459534670279850247104280658729319540047460819112396984006491811332281933199251045458182875266706425325665129201745385712779417583475563086225809859126956786306
  | 4 => 32764649210196532179195579047385314652523552240480998751103465573196352047098046910307350971971412710986107214064837783567831925840799798290812892299783655115594555704123004211370260807503252601225229872164802003816067009451410075645463005786022197124888295041167223597622705837087930679932061847385235599352167350761669525728141408809975898369287435056563686227394544036652805949344493907576408931779689847258633018921674306883520325036010610876918529882693584392056259757661591455000972733367314772215161931660549386166625046074445080602234545354650758723008558479631474169580455445055593057139843948483807646425498300776691529514706201818068998787311106616354827533785609982230022668908913781399511389279400331896540370701417781714938352790726541326648866900461337063681569019871659437401460285530409192175382672406198698882267909045186337224204424217549637261380471462961407191458205565875090056962505861460280023154995096958144786366170359044604277843301137099319070868371356392950318117749753925553536620419626841391178682605611628172261539841059242257659203580578741709282995204108673444346915230282099843410709574588604819394461277937388598291249928858217946798544141695020023739853359790982287981585120480333291809914520072
  | 5 => 522194565694003644863963372140655547818319907263450735965478894413110854815075629112206937719100043217777501293556612032130019831139853551493913597141610258261390340263726836442891051167709597127839182114911725149432338372794633939832786305402048073241145106281553576450911281149007630886776702372961313540194558398589131637788220581825234497573685109174765040869331964666078067860873549357734939295838244818135186582348287237676003341301317659195297778054929224614406917934300715458668788942483446338297725415786114575831339536486946200272533268169892653151721642771807601670983172024814638505243909484132373177340220594188790070884346790416483549092414350889940429603884341338954713123984674885199300959020379073725652861954511216105338324534083179185078047777545277334989270581126331704780661872839706678749663094828723723393647836683623588013308953085304653248007687871982560375818873281215133314062934408774220052643026744531417282819829121687776364031316883273689677317959899359874101744809656562892249114983080310100914603749475559110723631285319534553127738334544195214315642535099114468298226086013258116389838034299835618781527623257401296431581863432899282893827511660585889647730943076760169463163605781027815739244020256
  | 6 => 261098220554749623157846515682332952171310771712559973770549682907690089131948204219143695603244879032715724574813830878784575242759305469702294699778086435847845484361262396126448158386186331947166325213246279181138936706554675901297779061631013180674467252432211635539003848177701634367660938829534635146670079818050407224194995115780496590794701979106075784702700756675605662968273029245804754728843573336553944856958097610295937571644427430924169238932726719780521369889836523668912953728052173146710077949058655841624551735162160615415840005802405013154520165293504936584962506404719138640265265596615168860494546373377426632398930329230363947817139090700151163108036176532010564654731010542180042343228495780393418200806992134955996654410003831211091788596194237887890311282330575679118030600527066316869455566733606713890388310448025783415201077228498000569275253652976137679684448461611814447554901515868329267686586375760363510914976542140719466571625759663320465768740627422540348227630695057287005107182468284837490308440843136640054554844718443207825078820072286987995778821991879244850553431919693368152019000281420449161540919014757061066329361345632264188190335783848472743318712458766896371699108262067190275929804801
  | _ => 0
def Q : Nat → Nat
  | 0 => 57975229141213356085478346878882020388159566714183304668618033065467661117576574055066927279717479627574162376930294085295046840174772305974211875891259863682639647052008765230415733657198252148944842946754668521707098377633669057827006813325383060026598042729894942658078878226098386050500065432335298805042807626663431413302348828329396253198175083550506980772930870797887910166691493315898287376624028280229149909914884153896555051183452379572910245304783381882291570992608002956145909847438173028279674556705209547136406922874529712471478583751500723356062353420657127047983241303624668788759621457701201480651309106508205317377428077492977538965015076846205054993107809277706375948692583515287644519740035819972355122624157592051977062677520300681040876450378723558474396031590436199418709511052972125796483372251720307367183152935328193580334254462474561332352024340490103808712240221262981640916842799974094535467016628688723865231725452315617413220883723663937280049381674730913797146699840935204727026018354457611260025812656004113875198902606427419458466062452741891539490670261039869844361699116390600397283858659188198538249680120718037299937365536283746933826614670119100521788893993837499575066047807488
  | 1 => 344425684914956986200095595822463282216999954420086032235623865430944931914773230565973620144954914358786266973361342536225717079501357692213358265009907209274490371996413303850051426281849053005164497996426490514068958903653329814384516071134802277203968858080369717598559039800155201771987294741081753663730172375877756171485545476413078096715180186831587955453883888158604312263708638731235176333337735951773047324114646096718651338659781162553434777922500254685755931962694361551277598272290535173501600874645068312741316459539167840468071786731981840512292791931204371085691602222800718483278144728185564111545110632707792278463873135633095227238558320136778993003872046901633810514163217139943528806107287991788785779101660954080007216248893389038356773179129422936587363351441984069335370997918152629445091684329058082210403855299750585198133580039562699607133929498516223860690003886479306082129744635376275720734704532467872024810138539592882127186461434958304040901246793927699636709947464482816
  | 2 => 95911971106466306089997654943478945874377616644289284092723642988258283593519769427655789500365223161795735042547434736031913909349827599957141955765198392608324316420380556929223316858202407675246552047059591237403453730726438751848909372965300346157972224891666540594199911855562281460518946167464336296622232839638504168196733373120435167861356497066969697398745627760989925772143744411548463549688642040599345542392359162005719945618567749918172200093439964609313752390997939633191033813408740162315393287517412904752745945322068799086317106226977322757701216590614955506721757695937083145112090802433186649950419339750233130701109501766817082891254947610532291778591871748513343018424586250000170851373804250170154483174077176187620545113597856208743551985577069525704936411305885367582564924972912530512928068762630227249131792871595057023654268323454939092826947857828288157686518548016071179175109848499068141062738202501732361804684059902916018532243084606844597205398913448242115066245532537881011565562956610550552419992828010512196913172163155221466698754163268797533559555643430395454015618025587981931272970291251815583318147676804850598535972831036414673310424021199669663105024
  | 3 => 21411362040570479758900850176843451130610118930738662834643180830469168145492823861053919560259290108446277021030826436470849182279437466601768660185850800694588601019549662068087495546211256782393861251486070449688658017613566333906407772595489901405712164493102424276968085541977752729589879845089390797873773383496211586725419818108793302547665669035336370070962605220162197164827647684015205903162142266983787201539500687933188798681710840756085628075429543096167573861114237169613231088054965470662935401774744277850733519823687361595693635016224727761360525183540311948530878509654783582385206992944941578510755901645785538017939990692489931807473517965600713255230395320436236500187938506536935477031535685070624680755719009975474681238715789298349761318403613758566192351680167404404313484292223330203911199139677010288347479584317331474761186497946602182519317413222714235428989845192075826921461080336353195094242822129241049189289495680107928669911167667470828686909599628321257178614269478322913340294815356807315387177249081773678345737553660330515110917907834418281078669180928
  | 4 => 413227281832625178624377940173273591162540363609555784489470831439111381486194876550285338753179320693352183457033261460565796003933757322282888709282358577312513939120446315576231148108859493216413341027169237372115363544179845288985904433192052619877412342601513254544295652949760674229616122921354596217662669309385806591839498810517485707682200613072674749103940787996690502580885234518306098511895758195295239409116307928293960249779652700423679921149373740344780413416331510276717357383624056374575210619075299138393701733481503577483501306439476763864299693796509476513406611481071073809885811399883711261598519892390240017892292573238083630255091986882199279340229040586626197701078119892154210671963772400635791972614897879709606683656754090892775938588672
  | 5 => 5708990770823839524233143877797980545530986496
  | 6 => 863898234670902870084085215550892515776278797414087241952659669150437820408027188499562635144208189563924693416720257714647650644409750734879526908887838493150063784387339154641975420044705394198877736332443616181540105970608755990568632928496688099892333024297227250123763936040263718407401088436443783921062631834112937929766921844207721151731432511713584919925235368919441469922239955722218327328603847622970349125272473071466384838081426439555212955872537434414435498243921974191325658688301470114552418522397856930603009156275009600383041724387637181395424001174753990525300365015250022814217409135919358566152748056105533528577322749270863042905765051127152327190866584333275407075274440596168667406926801116775822792852386604291688132919889278664209292389629301464332360970022960089985565185918323663928826340124259281484789254250502180877055150491010781693059843724399880901078943130087968257008474377968182576734483656051574321324665744495363110473795619895653241051948664178653966515843026542764629243582111778939871651539991061133784761932340005871777795435149065911128125245294020364202276972931703534821056843265367101706543453157021876510036832120691795006483338731268437076491506742920732475392
  | 7 => 1062275985633534197379176413104937254659186235454063846398888276400807119721704485478325004530458571337778658972493002030693158675305414478819039957533174703887662541670786438063456256
  | 8 => 488949073121539043178895838851406898867685260673611653386208527301320256750945098442460084709113182789107256214464892052884956575049058585335894004824225556978848052700870382486432811126512032810019093103514678580988403100655092773497194921652262878660895819095201202957727846410635903499346091564032100080922029110666198856874372068909543752725127446446275130141704384403153173213642973260347547120927518593494548154693042687813126757638259919480596660015785042800818110628659177941014457037586017066097793890372685757581701160719984224943404424801688527463891923678834379546779645545606419569427574824563111913480237499286872496822079247464512671595600027881545516790726794520875456846025695904828856824122680691695622222780388482248652558345646407544371724549307907546148267185543556530668197490478774267191002528938567372851525085232721844598755176527243119768654561142351728852269053413174476938571816914419435443895662361267309023154705765158795604804766486473731465844362909575530822196003981963565054860681271890620405191718478159479477685388913902388171544282368568608479247952664643776459165494556000797676507398085908822491136
  | 9 => 1273354873470714314603996529093742060556242791128509813564818755779932493929566881027149217983747776331113579759221415768466399579844861801138924719295311172280990493890826905231570275481894045159031841844753539499427359566374367278466914773950886573319867924057787914344736025553566591127872829539761106556435962266272389386006412489403977892537755892835617232692218950202970514117424902303226210785530617321771892570524302232948923811854411586161286034365457162025720344501512166372612399256602513034221576628663652719826911148242554067484194324137857503349070857903401345135662004248692666575359555209574733230927820189047131359707619040506055554872664177683148766382464363570501684500163710341226582210393818519116486738544951296
  | 10 => 50172736614702193476010968685027850385725009984025754056752351897843540836727791310381960450640875187526127726743042077209009344297825833306791007079122302230257203282437017967319010464223403411666028891130176909178099340433873790449696141722887908379766592991480784511678588901194608305160012368897433073139024954535368556203311682248348132318295329821383241290835531777849305693041041567149516614437907351900261582473684954345924071473123034130274134722954297790455372889453739340801985909201900859696589364708551884000815765385640619922267443118020140789791084738002770787452810244806002844531297159666640599398253866669734555265873912487067788750536758461265538846803163989987905143549491955559219046972218912619029970610724339486044100503651037465691797221960390994444244006704352888836634150488713713548412324761281525404083023713782816833536
  | 11 => 2410312426921032588580116606028314112912093247945688951359675039065257391591803200669085024107346049663448766280888004787862416978794958324969612987890774651455213339381625224770782077917681499676845543137387820057597345857904599109461387122099507964997815641342300677629473355281617428411794163967785870370368969109221591943054232011562758450080579587850900993714892283476646631181515063804873375182260506246992837898705971012525843324401232986857004760339316736
  | 12 => 5809605995369958062859502533304574370686975176362895236661486152287203730997110225737336044533118407251326157754980517443990529594540047121662885672187032401032111639706440498844049850989051627200244765807041812394729680540024104827976584369381522292361208779044769892743225751738076979568811309579125511333093243519553784816306381580161860200247492568448150242515304449577187604136428738580990172551573934146255830366405915000869643732053218566832545291107903722831634138599586406690325959725187447169059540805012310209639011750748760017095360734234945757416272994856013308616958529958304677637019181594088528345061285863898271763457294883546638879554311615446446330199254382340016292057090751175533888161918987295591531536698701292267685465517437915790823154844634780260102891718032495396075041899485513811126977307478969074857043710716150121315922024556759241239013152919710956468406379442914941614357107914462567329693696
  | 13 => 32317006071311007300714876688669951960444102669715484032130345427524655138867890893197201411522913463688717960921898019494119559150490921095088152386448283120630877367300996091750197750389652106796057638384067568276792218642619756161838094338476170470581645852036305042887575891541065808607552399123930385521914333389668342420684974786564569494856176035326322058077805659331026192708460314150258592864177116725943603718461857357598351152301645904403697613233287231227125684710820209725157101726931323469678542580656697935045997268352998638215525166389437335543602135433229604645318478604952148193555853611059596230656
  | 14 => 1
  | _ => 0
def b : Nat → Bool
  | 0 => true
  | 1 => true
  | 2 => true
  | 3 => false
  | 4 => false
  | 5 => false
  | 6 => false
  | 7 => false
  | 8 => false
  | 9 => false
  | 10 => false
  | 11 => false
  | 12 => false
  | 13 => false
  | 14 => false
  | _ => false
def c : Nat → Bool
  | 0 => false
  | 1 => false
  | 2 => true
  | 3 => true
  | 4 => true
  | 5 => false
  | _ => false
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Zzero : Z.testBit 0 = true := by decide +kernel
theorem Zfixed : image K false Z = Z := by decide +kernel
theorem p0 : preCheck K (tail.getD 0 false) (P 0) (P 1) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem p1 : preCheck K (tail.getD 1 false) (P 1) (P 2) = true := by decide +kernel
theorem p2 : preCheck K (tail.getD 2 false) (P 2) (P 3) = true := by decide +kernel
theorem p3 : preCheck K (tail.getD 3 false) (P 3) (P 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks2Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem p4 : preCheck K (tail.getD 4 false) (P 4) (P 5) = true := by decide +kernel
theorem p5 : preCheck K (tail.getD 5 false) (P 5) (P 6) = true := by decide +kernel
theorem s0 : image K (tail.getD 0 false) (S 0) = S 1 := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks3Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem s1 : image K (tail.getD 1 false) (S 1) = S 2 := by decide +kernel
theorem s2 : image K (tail.getD 2 false) (S 2) = S 3 := by decide +kernel
theorem s3 : image K (tail.getD 3 false) (S 3) = S 4 := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks4Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem s4 : image K (tail.getD 4 false) (S 4) = S 5 := by decide +kernel
theorem s5 : image K (tail.getD 5 false) (S 5) = S 6 := by decide +kernel
theorem q0 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 1) (Q 0) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks5Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q1 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 2) (Q 1) = true := by decide +kernel
theorem q2 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 3) (Q 2) = true := by decide +kernel
theorem q3 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 4) (Q 3) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks6Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q4 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 5) (Q 4) = true := by decide +kernel
theorem q5 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 6) (Q 5) = true := by decide +kernel
theorem q6 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 7) (Q 6) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks7Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q7 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 8) (Q 7) = true := by decide +kernel
theorem q8 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 9) (Q 8) = true := by decide +kernel
theorem q9 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 10) (Q 9) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks8Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q10 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 11) (Q 10) = true := by decide +kernel
theorem q11 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 12) (Q 11) = true := by decide +kernel
theorem q12 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 13) (Q 12) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks9Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q13 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 14) (Q 13) = true := by decide +kernel
theorem qf0 : colConst K (Z &&& Q 0) (b 0) = true := by decide +kernel
theorem qf1 : colConst K (Z &&& Q 1) (b 1) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks10Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem qf2 : colConst K (Z &&& Q 2) (b 2) = true := by decide +kernel
theorem qf3 : colConst K (Z &&& Q 3) (b 3) = true := by decide +kernel
theorem qf4 : colConst K (Z &&& Q 4) (b 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks11Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem qf5 : colConst K (Z &&& Q 5) (b 5) = true := by decide +kernel
theorem qf6 : colConst K (Z &&& Q 6) (b 6) = true := by decide +kernel
theorem qf7 : colConst K (Z &&& Q 7) (b 7) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks12Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem qf8 : colConst K (Z &&& Q 8) (b 8) = true := by decide +kernel
theorem qf9 : colConst K (Z &&& Q 9) (b 9) = true := by decide +kernel
theorem qf10 : colConst K (Z &&& Q 10) (b 10) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks13Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem qf11 : colConst K (Z &&& Q 11) (b 11) = true := by decide +kernel
theorem qf12 : colConst K (Z &&& Q 12) (b 12) = true := by decide +kernel
theorem qf13 : colConst K (Z &&& Q 13) (b 13) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks14Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem qf14 : colConst K (Z &&& Q 14) (b 14) = true := by decide +kernel
theorem pf2 : colConst K (S 2 &&& P 2) (c 2) = true := by decide +kernel
theorem pf3 : colConst K (S 3 &&& P 3) (c 3) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Checks15Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem pf4 : colConst K (S 4 &&& P 4) (c 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint110001Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30RestrictedBackwardTubeResearch
theorem Pstep (j : Nat) (h : j < 6)  : preCheck K (tail.getD j false) (P j) (P (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
theorem Sstep (j : Nat) (h : j < 6)  : image K (tail.getD j false) (S j) = S (j+1) := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact s0
  · exact s1
  · exact s2
  · exact s3
  · exact s4
  · exact s5
theorem Qstep (j : Nat) (h : j < 14)  : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q (j+1)) (Q j) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact q0
  · exact q1
  · exact q2
  · exact q3
  · exact q4
  · exact q5
  · exact q6
  · exact q7
  · exact q8
  · exact q9
  · exact q10
  · exact q11
  · exact q12
  · exact q13
theorem Qforce (j : Nat) (h : j ≤ 14)  : colConst K (Z &&& Q j) (b j) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact qf0
  · exact qf1
  · exact qf2
  · exact qf3
  · exact qf4
  · exact qf5
  · exact qf6
  · exact qf7
  · exact qf8
  · exact qf9
  · exact qf10
  · exact qf11
  · exact qf12
  · exact qf13
  · exact qf14
theorem Pforce (j : Nat) (h : j < 6) (hz : tail.getD j false = false) : colConst K (S j &&& P j) (c j) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [tail] at hz
  · simp [tail] at hz
  · exact pf2
  · exact pf3
  · exact pf4
  · simp [tail] at hz

theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 74 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  apply Rule30RestrictedBackwardTubeResearch.no_padding_of_endpoint_tube hlo hzero i tail
    K L Z Q P S b c (by decide) Zzero Zfixed (by rfl) (by rfl) (by rfl) (by rfl)
  · intro d hd; exact Qstep d (by simpa [L] using hd)
  · intro j hj; exact Pstep j (by simpa [tail] using hj)
  · intro j hj; exact Sstep j (by simpa [tail] using hj)
  · intro d hd; exact Qforce d (by simpa [L] using hd)
  · intro j hj hz; exact Pforce j (by simpa [tail] using hj) hz
  · simp [tail]; omega
  · simp [K, tail]; omega
  · simp [L]; omega
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C110001

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint111101DefsResearch -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30RestrictedBackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def K : Nat := 10
def L : Nat := 3
def tail : List Bool := [true,true,true,true,false,true]
def Z : Nat := 22735012826402829640330845028270138285322580040444007300909362385916439266896543149610238686320216056435780344404205848328219421260474298750385351543389654728234198340007085173652166890015379376283335268515280352133205158392792810606103065109052716427422735929218602287628814021845225225961682986285373333537
def P : Nat → Nat
  | 0 => 10993678309731102712930841003355618576360013368098774812372882398755285281784106807180581058048041469045575794276728882975022997835686126299229660958309876766640644528370162155267202703819797252333109207127311794353489281070242172904087645674785672717563048171012498746380956584635637094351763520899514880
  | 1 => 685765508599211085444167454110345735329250641945289022767281753598509534196353414878545479039379807389837750761349598985028858375208779004505941099864320379492740288001567355526202127451158949771433393936033706471566394140024155065909140433024362471834102148197255021327319622998459064896669836411666432
  | 2 => 4249103942534136789516705652419749018636744941816255385595553105603228478886817941913300018121834285351114635889972008122772634701221663761282709153744371630289981031815224393163866112
  | 3 => 9516908214257811601907599988159363584840065290620124537956939899622020205826587990689077212775400643774711832257235027522909345571487396529861315719055326314814455073792347245307224163568933595697422149216092441761606229067073230804364931451679374391341388606002756129612438214868467712
  | 4 => 126633165554229521438977290762059361297987250739820462036000284719563379254544315991201997343356439034674007770120263341747898897565145822484177753904735444846393260786157879296
  | 5 => 89884656743115795386465259539451236680898848947115328636715040578866337902750481566354238661203768010560056939935696678829394884407208311246423715319737068892787911683731292425163608903546110799409451772239191746199797202053246477510444956207562702033389100358222242362999049846181264125702651381636615110656
  | 6 => 1
  | _ => 0
def S : Nat → Nat
  | 0 => 22735012826402829640330845028270138285322580040444007300909362385916439266896543149610238686320216056435780344404205848328219421260474298750385351543389654728234198340007085173652166890015379376283335268515280352133205158392792810606103065109052716427422735929218602287628814021845225225961682986285373333537
  | 1 => 11631097530814485438354584499196436334496782036459160547436877468571669887692909931094425410704051928841016951598308594342559155307328807941720663327346899466014643981634112220770992118146856533176599740344127780840428744881958449455270371253872990782508508141782077847426616654856857015662222778226514858002
  | 2 => 90281715072738341317908149172933904747035357349485025174971929987747706870075169717711175495499833472578599205252320262544461107478293283694264051404363197076607978646880205660199966601669104274316636631320300232442419704501530431713534116495052117025313379736192129268228564245446539178651196839223573446788
  | 3 => 715995456300597686300489247994644201974451184809443033528034543495392943880871637674615356079408052962453992901021214068123979014454654372075136379790595388425444881779607419254996321064856552717326537390714987806647707782523769862435714892881720274126647698824085382695904779180252941467980943218557649217
  | 4 => 4220203796918006597885377979697452555332151157780197425716103857574784588535011671961832494393949002521501215053941225433690111992318267371412433395247133250285348030933806639083585881283348764741258548489951615680861468225935543863980651986906262883390892808935077976779606176710456743585139547350839075842
  | 5 => 95525770513807586845511671510210327886208930000639911759053266593350053918355000753938501014304769853819848228294003076111536839600132986689428932161752974520137663514527349476224421499242512921743578471379066953406312783470800213521429201873909538620473814664461476011337008436039282830493878416096683395080
  | 6 => 11952046992944266397105472189691791226286406421078365585761066070754974659020917986998716084716692178497169100190800608732812244256839884149865217433187583399732867997058649417760183432438399428802989366419439740942802168656289004043578791947216177955582571387500920051152385578127982949966576197865819930897
  | _ => 0
def Q : Nat → Nat
  | 0 => 10993678309731102712930841003355618576360013368098774812372882398755285281784106807180581058048041469045575794276728882975022997835686126299229660958309876766640644528370162155267202703819797252333109207127311794353489281070242172904087645674785672717563048171012498746380956584635637094351763520899514880
  | 1 => 1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856
  | 2 => 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096
  | 3 => 1
  | _ => 0
def b : Nat → Bool
  | 0 => false
  | 1 => false
  | 2 => false
  | 3 => false
  | _ => false
def c : Nat → Bool
  | 0 => false
  | 1 => false
  | 2 => false
  | 3 => false
  | 4 => false
  | 5 => false
  | _ => false
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint111101Checks0Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem Zzero : Z.testBit 0 = true := by decide +kernel
theorem Zfixed : image K false Z = Z := by decide +kernel
theorem p0 : preCheck K (tail.getD 0 false) (P 0) (P 1) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint111101Checks1Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem p1 : preCheck K (tail.getD 1 false) (P 1) (P 2) = true := by decide +kernel
theorem p2 : preCheck K (tail.getD 2 false) (P 2) (P 3) = true := by decide +kernel
theorem p3 : preCheck K (tail.getD 3 false) (P 3) (P 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint111101Checks2Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem p4 : preCheck K (tail.getD 4 false) (P 4) (P 5) = true := by decide +kernel
theorem p5 : preCheck K (tail.getD 5 false) (P 5) (P 6) = true := by decide +kernel
theorem s0 : image K (tail.getD 0 false) (S 0) = S 1 := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint111101Checks3Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem s1 : image K (tail.getD 1 false) (S 1) = S 2 := by decide +kernel
theorem s2 : image K (tail.getD 2 false) (S 2) = S 3 := by decide +kernel
theorem s3 : image K (tail.getD 3 false) (S 3) = S 4 := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint111101Checks4Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem s4 : image K (tail.getD 4 false) (S 4) = S 5 := by decide +kernel
theorem s5 : image K (tail.getD 5 false) (S 5) = S 6 := by decide +kernel
theorem q0 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 1) (Q 0) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint111101Checks5Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q1 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 2) (Q 1) = true := by decide +kernel
theorem q2 : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q 3) (Q 2) = true := by decide +kernel
theorem qf0 : colConst K (Z &&& Q 0) (b 0) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint111101Checks6Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem qf1 : colConst K (Z &&& Q 1) (b 1) = true := by decide +kernel
theorem qf2 : colConst K (Z &&& Q 2) (b 2) = true := by decide +kernel
theorem qf3 : colConst K (Z &&& Q 3) (b 3) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint111101Checks7Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
open Rule30StripCertificates Rule30BackwardTubeResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem pf4 : colConst K (S 4 &&& P 4) (c 4) = true := by decide +kernel
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101

/- Source: Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoint111101Research -/
namespace Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101
open Rule30StripCertificates Rule30BackwardTubeResearch Rule30RestrictedBackwardTubeResearch
theorem Pstep (j : Nat) (h : j < 6)  : preCheck K (tail.getD j false) (P j) (P (j+1)) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
theorem Sstep (j : Nat) (h : j < 6)  : image K (tail.getD j false) (S j) = S (j+1) := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact s0
  · exact s1
  · exact s2
  · exact s3
  · exact s4
  · exact s5
theorem Qstep (j : Nat) (h : j < 3)  : Rule30RestrictedBackwardTubeResearch.restrictedPreCheck K false Z (Q (j+1)) (Q j) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · exact q0
  · exact q1
  · exact q2
theorem Qforce (j : Nat) (h : j ≤ 3)  : colConst K (Z &&& Q j) (b j) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · exact qf0
  · exact qf1
  · exact qf2
  · exact qf3
theorem Pforce (j : Nat) (h : j < 6) (hz : tail.getD j false = false) : colConst K (S j &&& P j) (c j) = true := by
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [tail] at hz
  · simp [tail] at hz
  · simp [tail] at hz
  · simp [tail] at hz
  · exact pf4
  · simp [tail] at hz

theorem no_padding {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 72 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ tail) := by
  apply Rule30RestrictedBackwardTubeResearch.no_padding_of_endpoint_tube hlo hzero i tail
    K L Z Q P S b c (by decide) Zzero Zfixed (by rfl) (by rfl) (by rfl) (by rfl)
  · intro d hd; exact Qstep d (by simpa [L] using hd)
  · intro j hj; exact Pstep j (by simpa [tail] using hj)
  · intro j hj; exact Sstep j (by simpa [tail] using hj)
  · intro d hd; exact Qforce d (by simpa [L] using hd)
  · intro j hj hz; exact Pforce j (by simpa [tail] using hj) hz
  · simp [tail]; omega
  · simp [K, tail]; omega
  · simp [L]; omega
end Ruliology.CellularAutomata.Rule30SixTailEndpointResearch.C111101

namespace Ruliology.CellularAutomata.Rule30SixTailReductionResearch
def sixCores : List (List Bool) :=
  [[true,false,false,false,false,true],
   [true,false,false,false,true,true],
   [true,false,false,true,false,true],
   [true,false,false,true,true,true],
   [true,false,true,false,false,true],
   [true,false,true,false,true,true],
   [true,false,true,true,false,true],
   [true,false,true,true,true,true],
   [true,true,false,false,false,true],
   [true,true,false,false,true,true],
   [true,true,false,true,false,true],
   [true,true,false,true,true,true],
   [true,true,true,false,false,true],
   [true,true,true,false,true,true],
   [true,true,true,true,false,true],
   [true,true,true,true,true,true]]
end Ruliology.CellularAutomata.Rule30SixTailReductionResearch

namespace Ruliology.CellularAutomata.Rule30SixTailSharpenedResearch
open Rule30Jen Rule30Realization
open Rule30SixTailReductionResearch

theorem no_six_core {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (hv : v ∈ sixCores) (r : Nat) (hr : 74 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ v) := by
  simp only [sixCores, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Rule30SixTailCertificatesResearch.C100001.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C100011.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C100101.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C100111.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C101001.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C101011.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C101101.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C101111.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailEndpointResearch.C110001.no_padding hlo hzero i r hr
  · exact Rule30SixTailCertificatesResearch.C110011.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C110101.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C110111.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C111001.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C111011.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailEndpointResearch.C111101.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C111111.no_padding hlo hzero i r (by omega)
end Ruliology.CellularAutomata.Rule30SixTailSharpenedResearch

namespace Rule30Submission
open Ruliology.CellularAutomata
 theorem no_six_bit_core {x : Int -> Bool} {lo : Int}
    (hlo : x lo = true) (hzero : forall p, p < lo -> x p = false)
    (i : Int) (u : List Bool) (hu : u ∈ Rule30SixTailReductionResearch.sixCores)
    (r : Nat) (hr : 74 <= r) :
    Not (Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ u)) :=
  Rule30SixTailSharpenedResearch.no_six_core hlo hzero i u hu r hr
end Rule30Submission
