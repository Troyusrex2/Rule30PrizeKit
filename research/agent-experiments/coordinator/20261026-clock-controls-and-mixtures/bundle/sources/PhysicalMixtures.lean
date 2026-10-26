import PhysicalMaintenance
import CedarPhysicalAgeBridge
import Ruliology.CellularAutomata.Rule30StripCertificates

namespace PhysicalMixtures
open Ruliology.CellularAutomata Rule30Jen Rule30StripCertificates
open PhysicalMaintenance CedarPhysicalAgeBridge

def offset (u : Nat → List Bool) (q : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => offset u q i + (u i).length + q i

def RepeatsSegments (T r : Nat) (u : Nat → List Bool) (q : Nat → Nat) : Prop :=
  ∀ m i, i < r → Drives (T + m * offset u q r + offset u q i) (u i) (q i)

theorem offset_mono (u : Nat → List Bool) (q : Nat → Nat) :
    ∀ i j, i ≤ j → offset u q i ≤ offset u q j := by
  intro i j
  induction j generalizing i with
  | zero =>
    intro hij
    have hi : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    intro hij
    by_cases h : i ≤ j
    · have hm := ih i h
      simp only [offset]
      omega
    · have he : i = j + 1 := by omega
      subst i
      exact Nat.le_refl _

theorem offset_cover (u : Nat → List Bool) (q : Nat → Nat) :
    ∀ r s, s < offset u q r →
      ∃ i, i < r ∧ ∃ d, d < (u i).length + q i ∧ s = offset u q i + d := by
  intro r
  induction r with
  | zero => intro s hs; simp [offset] at hs
  | succ r ih =>
    intro s hs
    by_cases h : s < offset u q r
    · obtain ⟨i, hi, d, hd, he⟩ := ih s h
      exact ⟨i, by omega, d, hd, he⟩
    · refine ⟨r, by omega, s - offset u q r, ?_, ?_⟩
      · simp only [offset] at hs
        omega
      · omega

theorem walk_stripes (N T r : Nat) (u : Nat → List Bool) (q : Nat → Nat)
    (hN : 1 ≤ N) (hlen : ∀ i, i < r → (u i).length ≤ N)
    (hblack : ∀ i, i < r → ∃ j, j < (u i).length ∧ (u i).getD j false = true)
    (hq : ∀ i, i < r → padding N ≤ q i)
    (hstripe : StripeAt N T)
    (hdrive : ∀ i, i < r → Drives (T + offset u q i) (u i) (q i)) :
    ∀ i, i ≤ r → StripeAt N (T + offset u q i) := by
  intro i
  induction i with
  | zero => intro _; simpa [offset] using hstripe
  | succ i ih =>
    intro hi
    have hh := (maintain N (T + offset u q i) (u i) (q i) hN
      (hlen i (by omega)) (hblack i (by omega)) (hq i (by omega))
      (ih (by omega)) (hdrive i (by omega))).2
    simpa [offset, Nat.add_assoc] using hh

theorem cycle_stripes (N T r : Nat) (u : Nat → List Bool) (q : Nat → Nat)
    (hN : 1 ≤ N) (hlen : ∀ i, i < r → (u i).length ≤ N)
    (hblack : ∀ i, i < r → ∃ j, j < (u i).length ∧ (u i).getD j false = true)
    (hq : ∀ i, i < r → padding N ≤ q i)
    (hstripe : StripeAt N T) (hdrive : RepeatsSegments T r u q) :
    ∀ m i, i ≤ r → StripeAt N (T + m * offset u q r + offset u q i) := by
  have hstarts : ∀ m, StripeAt N (T + m * offset u q r) := by
    intro m
    induction m with
    | zero => simpa using hstripe
    | succ m ih =>
      have hh := walk_stripes N (T + m * offset u q r) r u q hN hlen hblack hq
        ih (hdrive m) r (Nat.le_refl _)
      simpa [Nat.succ_mul, Nat.add_assoc] using hh
  intro m
  exact walk_stripes N (T + m * offset u q r) r u q hN hlen hblack hq
    (hstarts m) (hdrive m)

theorem periodic_of_phases (f : Nat → Bool) (T P : Nat) (hP : 0 < P)
    (hphase : ∀ m s, s < P → f (T + (m + 1) * P + s) = f (T + m * P + s)) :
    ∀ t, T ≤ t → f (t + P) = f t := by
  intro t ht
  let k := (t - T) / P
  let s := (t - T) % P
  have hs : s < P := Nat.mod_lt _ hP
  have hd : s + P * k = t - T := Nat.mod_add_div _ _
  have htime : t = T + k * P + s := by
    rw [Nat.mul_comm P k] at hd
    omega
  have hnext : t + P = T + (k + 1) * P + s := by
    rw [Nat.add_mul]
    simp only [Nat.one_mul]
    omega
  rw [hnext, htime]
  exact hphase k s hs

/-- A repeated finite mixture with a certified initial stripe is impossible. -/
theorem not_repeats_from_stripe (N T r : Nat) (u : Nat → List Bool) (q : Nat → Nat)
    (hN : 1 ≤ N) (hr : 1 ≤ r)
    (hlen : ∀ i, i < r → (u i).length ≤ N)
    (hblack : ∀ i, i < r → ∃ j, j < (u i).length ∧ (u i).getD j false = true)
    (hq : ∀ i, i < r → padding N ≤ q i)
    (hstripe : StripeAt N T) (hdrive : RepeatsSegments T r u q) : False := by
  let P := offset u q r
  have hP : 0 < P := by
    obtain ⟨j, hj, _⟩ := hblack 0 (by omega)
    have hm := offset_mono u q 1 r hr
    simp only [offset] at hm
    dsimp [P]
    omega
  have hstripes := cycle_stripes N T r u q hN hlen hblack hq hstripe hdrive
  have hphase1 : ∀ m s, s < P →
      cell (T + (m + 1) * P + s) 1 = cell (T + m * P + s) 1 := by
    intro m s hs
    obtain ⟨i, hi, d, hd, he⟩ := offset_cover u q r s hs
    have hh := response_agree N (T + (m + 1) * P + offset u q i)
      (T + m * P + offset u q i) (u i) (q i) (q i) hN (hlen i hi)
      (hblack i hi) (hq i hi) (hq i hi)
      (hstripes (m + 1) i (by omega)) (hstripes m i (by omega))
      (hdrive (m + 1) i hi) (hdrive m i hi) d (by omega) (by omega)
    simpa [he, Nat.add_assoc] using hh
  have hphase0 : ∀ m s, s < P →
      cell (T + (m + 1) * P + s) 0 = cell (T + m * P + s) 0 := by
    intro m s hs
    obtain ⟨i, hi, d, hd, he⟩ := offset_cover u q r s hs
    have h0 := hdrive (m + 1) i hi d hd
    have h1 := hdrive m i hi d hd
    have hh := h0.trans h1.symm
    simpa [he, Nat.add_assoc] using hh
  have hp0 : EventuallyPeriodic (fun t => cell t 0) :=
    ⟨T, P, hP, periodic_of_phases (fun t => cell t 0) T P hP hphase0⟩
  have hp1 : EventuallyPeriodic (fun t => cell t (0 + 1)) :=
    ⟨T, P, hP, periodic_of_phases (fun t => cell t 1) T P hP hphase1⟩
  exact not_adjacent 0 hp0 hp1

theorem repeats_shift (T r k : Nat) (u : Nat → List Bool) (q : Nat → Nat)
    (hdrive : RepeatsSegments T r u q) :
    RepeatsSegments (T + k * offset u q r) r u q := by
  intro m i hi
  have hh := hdrive (k + m) i hi
  simpa [Nat.add_mul, Nat.add_assoc] using hh

/-- A pair of large gaps surrounding block zero provides entry; all other
gaps need only satisfy the linear maintenance bound. -/
theorem not_repeats_seed_pair (N T r : Nat) (u : Nat → List Bool) (q : Nat → Nat)
    (hN : 1 ≤ N) (hr : 1 ≤ r)
    (hlen : ∀ i, i < r → (u i).length ≤ N)
    (hblack : ∀ i, i < r → ∃ j, j < (u i).length ∧ (u i).getD j false = true)
    (hq : ∀ i, i < r → padding N ≤ q i)
    (hbefore : warmup N ≤ q (r - 1))
    (hafter : bound N + 9 * horizon N ≤ q 0)
    (hdrive : RepeatsSegments T r u q) : False := by
  let P := offset u q r
  let W := warmup N
  let A := T + P - W
  have hri : r - 1 < r := by omega
  have hPend : P = offset u q (r - 1) + (u (r - 1)).length + q (r - 1) := by
    dsimp [P]
    exact (congrArg (offset u q) (show r = (r - 1) + 1 by omega)).trans rfl
  have hWP : W ≤ P := by dsimp [W]; omega
  have hwhite : ∀ s, s < W → cell (A + s) 0 = false := by
    intro s hs
    let d := (u (r - 1)).length + q (r - 1) - W + s
    have hd : d < (u (r - 1)).length + q (r - 1) := by dsimp [d, W] at *; omega
    have hdn : (u (r - 1)).length ≤ d := by dsimp [d, W] at *; omega
    have htime : A + s = T + 0 * offset u q r + offset u q (r - 1) + d := by
      dsimp [A, d]
      omega
    rw [htime, hdrive 0 (r - 1) hri d hd,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none hdn]
    rfl
  obtain ⟨ell, hell, hbell, hlast⟩ := exists_last (u 0) (u 0).length
    (Nat.le_refl _) (hblack 0 (by omega))
  have hellN : ell < N := by have hh := hlen 0 (by omega); omega
  have hwitness := physical_white_witness A N ell hN hellN hwhite
  have htime : A + warmup N + ell = T + P + ell := by dsimp [A, W] at *; omega
  rw [htime] at hwitness
  have hd0 : Drives (T + P) (u 0) (q 0) := by
    simpa [P, offset] using hdrive 1 0 (by omega)
  have h0 : cell (T + P + ell) 0 = true := by
    rw [hd0 ell (by omega)]
    exact hbell
  let L := (u 0).length + q 0 - ell - 1
  have hL : bound N + 9 * horizon N ≤ L := by dsimp [L]; omega
  have htailwhite : ∀ s, s < L → cell (T + P + ell + 1 + s) 0 = false := by
    intro s hs
    have hsp : ell + 1 + s < (u 0).length + q 0 := by dsimp [L] at hs; omega
    rw [show T + P + ell + 1 + s = T + P + (ell + 1 + s) by omega,
      hd0 (ell + 1 + s) hsp]
    by_cases hu : ell + 1 + s < (u 0).length
    · exact hlast _ (by omega) hu
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  have hseed0 := (PhysicalCapture.tail_and_stripe (T + P + ell) (bound N)
    (horizon N) L h0 hwitness htailwhite hL).2
  have hseed : StripeAt N (T + P + offset u q 1) := by
    have he : T + P + ell + 1 + L = T + P + offset u q 1 := by
      dsimp [L, offset]
      omega
    simpa only [StripeAt, he] using hseed0
  have hsuffix : ∀ i, 1 ≤ i → i ≤ r → StripeAt N (T + P + offset u q i) := by
    intro i
    induction i with
    | zero => intro hi; omega
    | succ i ih =>
      intro hi hir
      by_cases hi0 : i = 0
      · subst i
        exact hseed
      · have hh := (maintain N (T + P + offset u q i) (u i) (q i) hN
          (hlen i (by omega)) (hblack i (by omega)) (hq i (by omega))
          (ih (by omega) (by omega)) (by simpa [P] using hdrive 1 i (by omega))).2
        simpa [offset, Nat.add_assoc] using hh
  have hstart : StripeAt N (T + 2 * offset u q r) := by
    have hh := hsuffix r hr (Nat.le_refl _)
    simpa [P, Nat.two_mul, Nat.add_assoc] using hh
  exact not_repeats_from_stripe N (T + 2 * offset u q r) r u q hN hr hlen hblack hq
    hstart (repeats_shift T r 2 u q hdrive)

end PhysicalMixtures
