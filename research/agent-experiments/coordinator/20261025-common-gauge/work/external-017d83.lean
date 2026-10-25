import Ruliology.CellularAutomata.Rule30Prize
import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripe
import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFamily
import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryStripeCycles3
import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFour

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30Submission

open Ruliology.CellularAutomata
open Ruliology.CellularAutomata.Rule30ZeroBoundary
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripe
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles0
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles1
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles2
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles3

theorem seg5_17_0 : seg 32 31 1 17 0 16384 0 17 0 = true := by decide +kernel
theorem cyc5_17 : Cycle 32 31 17 0 16384 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 17 0 16384 0 17 0 seg5_17_0)⟩

theorem seg5_19_0 : seg 32 31 1 3825205267 0 16384 0 19 0 = true := by decide +kernel
theorem seg5_19_1 : seg 32 31 1 2415919123 0 16384 16384 3825205267 0 = true := by decide +kernel
theorem seg5_19_2 : seg 32 31 1 1946157075 0 16384 32768 2415919123 0 = true := by decide +kernel
theorem seg5_19_3 : seg 32 31 1 19 0 16384 49152 1946157075 0 = true := by decide +kernel
theorem cyc5_19 : Cycle 32 31 19 0 65536 :=
  ⟨by decide, by decide, (path_append (path_append (path_append (seg_sound 32 31 1 3825205267 0 16384 0 19 0 seg5_19_0) (seg_sound 32 31 1 2415919123 0 16384 16384 3825205267 0 seg5_19_1)) (seg_sound 32 31 1 1946157075 0 16384 32768 2415919123 0 seg5_19_2)) (seg_sound 32 31 1 19 0 16384 49152 1946157075 0 seg5_19_3))⟩

theorem seg5_21_0 : seg 32 31 1 2147483669 0 16384 0 21 0 = true := by decide +kernel
theorem seg5_21_1 : seg 32 31 1 21 0 16384 16384 2147483669 0 = true := by decide +kernel
theorem cyc5_21 : Cycle 32 31 21 0 32768 :=
  ⟨by decide, by decide, (path_append (seg_sound 32 31 1 2147483669 0 16384 0 21 0 seg5_21_0) (seg_sound 32 31 1 21 0 16384 16384 2147483669 0 seg5_21_1))⟩

theorem seg5_23_0 : seg 32 31 1 23 0 16384 0 23 0 = true := by decide +kernel
theorem cyc5_23 : Cycle 32 31 23 0 16384 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 23 0 16384 0 23 0 seg5_23_0)⟩

theorem seg5_25_0 : seg 32 31 1 25 0 16384 0 25 0 = true := by decide +kernel
theorem cyc5_25 : Cycle 32 31 25 0 16384 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 25 0 16384 0 25 0 seg5_25_0)⟩

theorem seg5_27_0 : seg 32 31 1 27 0 4096 0 27 0 = true := by decide +kernel
theorem cyc5_27 : Cycle 32 31 27 0 4096 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 27 0 4096 0 27 0 seg5_27_0)⟩

theorem seg5_29_0 : seg 32 31 1 3758096413 0 16384 0 29 0 = true := by decide +kernel
theorem seg5_29_1 : seg 32 31 1 3221225501 0 16384 16384 3758096413 0 = true := by decide +kernel
theorem seg5_29_2 : seg 32 31 1 2684354589 0 16384 32768 3221225501 0 = true := by decide +kernel
theorem seg5_29_3 : seg 32 31 1 29 0 16384 49152 2684354589 0 = true := by decide +kernel
theorem cyc5_29 : Cycle 32 31 29 0 65536 :=
  ⟨by decide, by decide, (path_append (path_append (path_append (seg_sound 32 31 1 3758096413 0 16384 0 29 0 seg5_29_0) (seg_sound 32 31 1 3221225501 0 16384 16384 3758096413 0 seg5_29_1)) (seg_sound 32 31 1 2684354589 0 16384 32768 3221225501 0 seg5_29_2)) (seg_sound 32 31 1 29 0 16384 49152 2684354589 0 seg5_29_3))⟩

theorem seg5_31_0 : seg 32 31 1 1207959583 0 16384 0 31 0 = true := by decide +kernel
theorem seg5_31_1 : seg 32 31 1 1073741855 0 16384 16384 1207959583 0 = true := by decide +kernel
theorem seg5_31_2 : seg 32 31 1 134217759 0 16384 32768 1073741855 0 = true := by decide +kernel
theorem seg5_31_3 : seg 32 31 1 31 0 16384 49152 134217759 0 = true := by decide +kernel
theorem cyc5_31 : Cycle 32 31 31 0 65536 :=
  ⟨by decide, by decide, (path_append (path_append (path_append (seg_sound 32 31 1 1207959583 0 16384 0 31 0 seg5_31_0) (seg_sound 32 31 1 1073741855 0 16384 16384 1207959583 0 seg5_31_1)) (seg_sound 32 31 1 134217759 0 16384 32768 1073741855 0 seg5_31_2)) (seg_sound 32 31 1 31 0 16384 49152 134217759 0 seg5_31_3))⟩

/-! ## Two-level cycle certificate for `(13, 0)` at `K = 46, S = 45` -/

theorem fstep_mod_two_pow (K0 K W fp : Nat) (hK : K0 ≤ K) (hfp : fp < 2) :
    fstep K W fp % 2 ^ K0 = fstep K0 (W % 2 ^ K0) fp := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, testBit_fstep K W fp i hfp, testBit_fstep K0 (W % 2 ^ K0) fp i hfp]
  by_cases hi : i < K0
  · have hiK : i < K := by omega
    simp only [hi, hiK, decide_true, Bool.true_and, Nat.testBit_mod_two_pow]
    rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi2
    · simp
    · simp [show 0 < K0 by omega]
    · simp [show i - 1 < K0 by omega, show i - 2 < K0 by omega]
  · simp [hi]

theorem orb_mod_two_pow (K0 K : Nat) (hK : K0 ≤ K) :
    ∀ t W fp, fp < 2 →
      ((orb K t (W, fp)).1 % 2 ^ K0 = (orb K0 t (W % 2 ^ K0, fp)).1 ∧
       (orb K t (W, fp)).2 = (orb K0 t (W % 2 ^ K0, fp)).2 ∧
       (orb K t (W, fp)).2 < 2) := by
  intro t
  induction t with
  | zero =>
    intro W fp hfp
    exact ⟨rfl, rfl, hfp⟩
  | succ t ih =>
    intro W fp hfp
    obtain ⟨h1, h2, h3⟩ := ih W fp hfp
    show (fstep K (orb K t (W, fp)).1 (orb K t (W, fp)).2) % 2 ^ K0 =
           fstep K0 (orb K0 t (W % 2 ^ K0, fp)).1 (orb K0 t (W % 2 ^ K0, fp)).2 ∧
         1 - (orb K t (W, fp)).2 = 1 - (orb K0 t (W % 2 ^ K0, fp)).2 ∧
         1 - (orb K t (W, fp)).2 < 2
    refine ⟨?_, by rw [h2], by omega⟩
    rw [fstep_mod_two_pow K0 K _ _ hK h3, h1, h2]

theorem pstepN_mod_two_pow (x m : Nat) :
    pstepN (x % 2 ^ (m + 1)) % 2 ^ m = pstepN x % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < m
  · simp only [hi, decide_true, Bool.true_and]
    show (((x % 2 ^ (m + 1)) >>> 1) ^^^ ((x % 2 ^ (m + 1)) ||| ((x % 2 ^ (m + 1)) <<< 1))).testBit i =
      ((x >>> 1) ^^^ (x ||| (x <<< 1))).testBit i
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
      Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    cases i with
    | zero =>
      simp [show 0 < m + 1 by omega, show 1 < m + 1 by omega]
    | succ i =>
      simp [show 1 + (i + 1) < m + 1 by omega, show i + 1 < m + 1 by omega,
        show i < m + 1 by omega]
  · simp [hi]

theorem sig_mono : ∀ f1 f2 r x, f1 ≤ f2 → sig f1 r x = true → sig f2 r x = true := by
  intro f1
  induction f1 with
  | zero => intro f2 r x _ h; exact absurd h Bool.false_ne_true
  | succ f1 ih =>
    intro f2 r x hf h
    obtain ⟨f2', rfl⟩ : ∃ f2', f2 = f2' + 1 := ⟨f2 - 1, by omega⟩
    have h' : Bool.rec (motive := fun _ => Bool) (sig f1 (Nat.add r 1) (pstepN x)) true
        (band (Nat.beq (Nat.mod r 2) 0) (Nat.beq (Nat.mod x 2) 0)) = true := h
    show Bool.rec (motive := fun _ => Bool) (sig f2' (Nat.add r 1) (pstepN x)) true
        (band (Nat.beq (Nat.mod r 2) 0) (Nat.beq (Nat.mod x 2) 0)) = true
    cases hb : band (Nat.beq (Nat.mod r 2) 0) (Nat.beq (Nat.mod x 2) 0)
    · rw [hb] at h'; exact ih f2' (r + 1) (pstepN x) (by omega) h'
    · rfl

theorem sig_par_congr : ∀ fuel r1 r2 x, r1 % 2 = r2 % 2 → sig fuel r1 x = sig fuel r2 x := by
  intro fuel
  induction fuel with
  | zero => intro r1 r2 x _; rfl
  | succ fuel ih =>
    intro r1 r2 x hr
    have hr' : Nat.mod r1 2 = Nat.mod r2 2 := hr
    have hrec : sig fuel (Nat.add r1 1) (pstepN x) = sig fuel (Nat.add r2 1) (pstepN x) :=
      ih (r1 + 1) (r2 + 1) (pstepN x) (by omega)
    show Bool.rec (motive := fun _ => Bool) (sig fuel (Nat.add r1 1) (pstepN x)) true
        (band (Nat.beq (Nat.mod r1 2) 0) (Nat.beq (Nat.mod x 2) 0)) =
      Bool.rec (motive := fun _ => Bool) (sig fuel (Nat.add r2 1) (pstepN x)) true
        (band (Nat.beq (Nat.mod r2 2) 0) (Nat.beq (Nat.mod x 2) 0))
    rw [hr', hrec]

theorem sig_mod_two_pow :
    ∀ fuel K0 r x, fuel ≤ K0 → sig fuel r (x % 2 ^ K0) = sig fuel r x := by
  intro fuel
  induction fuel with
  | zero => intro K0 r x _; rfl
  | succ fuel ih =>
    intro K0 r x hf
    obtain ⟨m, rfl⟩ : ∃ m, K0 = m + 1 := ⟨K0 - 1, by omega⟩
    have hmod2 : Nat.mod (x % 2 ^ (m + 1)) 2 = Nat.mod x 2 := by
      show (x % 2 ^ (m + 1)) % 2 = x % 2
      have hdvd : 2 ∣ 2 ^ (m + 1) := ⟨2 ^ m, by rw [Nat.pow_succ, Nat.mul_comm]⟩
      exact Nat.mod_mod_of_dvd x hdvd
    have hrec : sig fuel (Nat.add r 1) (pstepN (x % 2 ^ (m + 1))) = sig fuel (Nat.add r 1) (pstepN x) := by
      rw [← ih m (r + 1) (pstepN (x % 2 ^ (m + 1))) (by omega),
          ← ih m (r + 1) (pstepN x) (by omega), pstepN_mod_two_pow]
    show Bool.rec (motive := fun _ => Bool) (sig fuel (Nat.add r 1) (pstepN (x % 2 ^ (m + 1)))) true
        (band (Nat.beq (Nat.mod r 2) 0) (Nat.beq (Nat.mod (x % 2 ^ (m + 1)) 2) 0)) =
      Bool.rec (motive := fun _ => Bool) (sig fuel (Nat.add r 1) (pstepN x)) true
        (band (Nat.beq (Nat.mod r 2) 0) (Nat.beq (Nat.mod x 2) 0))
    rw [hmod2, hrec]

def fstepPair (mask W : Nat) : Nat :=
  let W1 := Nat.land (Nat.xor W (Nat.lor (Nat.lor (Nat.shiftLeft W 1) 1)
      (Nat.lor (Nat.lor (Nat.shiftLeft W 2) 2) 0))) mask
  Nat.land (Nat.xor W1 (Nat.lor (Nat.lor (Nat.shiftLeft W1 1) 0)
      (Nat.lor (Nat.lor (Nat.shiftLeft W1 2) 0) 1))) mask

noncomputable def fstridePair (mask fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun W => W)
    (fun _ ih W => ih (fstepPair mask W)) fuel

noncomputable def fstridePairBig (mask blocks rem W : Nat) : Nat :=
  let W' := Nat.rec (motive := fun _ => Nat → Nat)
    (fun W => W)
    (fun _ ih W => ih (fstridePair mask 1024 W))
    blocks W
  fstridePair mask rem W'

theorem fstepPair_eq_orb (K W : Nat) :
    orb K 2 (W, 0) = (fstepPair (Nat.sub (Nat.pow 2 K) 1) W, 0) := rfl

theorem fstridePair_eq_orb (K : Nat) :
    ∀ fuel W, orb K (2 * fuel) (W, 0) = (fstridePair (Nat.sub (Nat.pow 2 K) 1) fuel W, 0) := by
  intro fuel
  induction fuel with
  | zero => intro W; rfl
  | succ fuel ih =>
    intro W
    rw [show 2 * (fuel + 1) = 2 + 2 * fuel by omega, orb_add, fstepPair_eq_orb]
    exact ih (fstepPair (Nat.sub (Nat.pow 2 K) 1) W)

theorem fstridePairBig_eq_orb (K blocks rem W : Nat) :
    orb K (2048 * blocks + 2 * rem) (W, 0) = (fstridePairBig (Nat.sub (Nat.pow 2 K) 1) blocks rem W, 0) := by
  unfold fstridePairBig
  suffices h : ∀ b W, orb K (2048 * b) (W, 0) =
      (Nat.rec (motive := fun _ => Nat → Nat) (fun W => W)
        (fun _ ih W => ih (fstridePair (Nat.sub (Nat.pow 2 K) 1) 1024 W)) b W, 0) by
    rw [orb_add, h blocks W, fstridePair_eq_orb]
  intro b
  induction b with
  | zero => intro W; rfl
  | succ b ih =>
    intro W
    rw [show 2048 * (b + 1) = 2 * 1024 + 2048 * b by omega, orb_add, fstridePair_eq_orb]
    exact ih (fstridePair (Nat.sub (Nat.pow 2 K) 1) 1024 W)

noncomputable def liftSegFast (W0 W1 : Nat) : Bool :=
  let mask := Nat.sub (Nat.pow 2 46) 1
  let W_even := fstridePairBig mask 29 806 W0
  let W_hit := fstep 46 W_even 0
  band (sig 46 1 W_hit)
    (let W_next := fstep 46 W_hit 1
     let W_end := fstridePairBig mask 2 217 W_next
     Nat.beq W_end W1)

theorem liftSegFast_sound (r W0 W1 : Nat)
    (h_pre : PathOK 34 33 1 0 (13, 0) (4159956310, 1) 61005)
    (h_post : PathOK 34 33 1 61006 (13020969643, 0) (13, 0) 4530)
    (hr : r % 2 = 0) (hmod : W0 % 2 ^ 34 = 13)
    (hlift : liftSegFast W0 W1 = true) :
    PathOK 46 45 1 r (W0, 0) (W1, 0) 65536 ∧ W1 % 2 ^ 34 = 13 := by
  let mask := Nat.sub (Nat.pow 2 46) 1
  let W_even := fstridePairBig mask 29 806 W0
  let W_hit := fstep 46 W_even 0
  let W_next := fstep 46 W_hit 1
  let W_end := fstridePairBig mask 2 217 W_next
  have h1 : band (sig 46 1 W_hit) (Nat.beq W_end W1) = true := hlift
  cases hs : sig 46 1 W_hit <;> cases he : Nat.beq W_end W1 <;> rw [hs, he] at h1 <;>
    try exact absurd h1 (by decide)
  rw [Nat.beq_eq] at he
  have ho_even : orb 46 61004 (W0, 0) = (W_even, 0) :=
    fstridePairBig_eq_orb 46 29 806 W0
  have ho_hit : orb 46 61005 (W0, 0) = (W_hit, 1) := by
    show fS 46 (orb 46 61004 (W0, 0)) = (W_hit, 1)
    rw [ho_even]; rfl
  have ho_next : orb 46 61006 (W0, 0) = (W_next, 0) := by
    show fS 46 (orb 46 61005 (W0, 0)) = (W_next, 0)
    rw [ho_hit]; rfl
  have ho_end : orb 46 65536 (W0, 0) = (W1, 0) := by
    rw [show (65536 : Nat) = 61006 + (2048 * 2 + 2 * 217) by decide, orb_add, ho_next]
    rw [fstridePairBig_eq_orb 46 2 217 W_next]
    show (W_end, 0) = (W1, 0)
    rw [he]
  have h_cstep : orb 34 61006 (13, 0) = (13020969643, 0) := by
    show fS 34 (orb 34 61005 (13, 0)) = (13020969643, 0)
    rw [h_pre.1]; decide
  have h_cper : orb 34 65536 (13, 0) = (13, 0) := by
    rw [show (65536 : Nat) = 61006 + 4530 by decide, orb_add, h_cstep, h_post.1]
  have hW1_mod : W1 % 2 ^ 34 = 13 := by
    have hm := (orb_mod_two_pow 34 46 (by decide) 65536 W0 0 (by decide)).1
    rw [ho_end, hmod, h_cper] at hm
    exact hm
  refine ⟨⟨ho_end, fun j hj hq => ?_⟩, hW1_mod⟩
  rcases (show j < 61005 ∨ j = 61005 ∨ 61006 ≤ j by omega) with hj1 | rfl | hj2
  · have hsig34 := h_pre.2 j hj1 (by omega)
    rw [Nat.zero_add] at hsig34
    have hm := (orb_mod_two_pow 34 46 (by decide) j W0 0 (by decide)).1
    rw [hmod] at hm
    rw [← hm, sig_mod_two_pow 34 34 j _ (by decide)] at hsig34
    rw [sig_par_congr 46 (r + j) j _ (by omega)]
    exact sig_mono 34 46 j _ (by decide) hsig34
  · rw [ho_hit, sig_par_congr 46 (r + 61005) 1 W_hit (by omega)]
    exact hs
  · obtain ⟨i, rfl⟩ : ∃ i, j = 61006 + i := ⟨j - 61006, by omega⟩
    have hsig34 := h_post.2 i (by omega) (by omega)
    have horb34 : orb 34 (61006 + i) (13, 0) = orb 34 i (13020969643, 0) := by
      rw [orb_add, h_cstep]
    rw [← horb34] at hsig34
    have hm := (orb_mod_two_pow 34 46 (by decide) (61006 + i) W0 0 (by decide)).1
    rw [hmod] at hm
    rw [← hm, sig_mod_two_pow 34 34 (61006 + i) _ (by decide)] at hsig34
    rw [sig_par_congr 46 (r + (61006 + i)) (61006 + i) _ (by omega)]
    exact sig_mono 34 46 (61006 + i) _ (by decide) hsig34

theorem c_seg13_0 : seg 34 33 1 536870925 0 16384 0 13 0 = true := by decide +kernel
theorem c_seg13_1 : seg 34 33 1 10737418253 0 16384 16384 536870925 0 = true := by decide +kernel
theorem c_seg13_2 : seg 34 33 1 15569256461 0 16384 32768 10737418253 0 = true := by decide +kernel
theorem c_seg13_3 : seg 34 33 1 4159956310 1 11853 49152 15569256461 0 = true := by decide +kernel
theorem c_seg13_4 : seg 34 33 1 13 0 4530 61006 13020969643 0 = true := by decide +kernel

theorem c_pre_13 : PathOK 34 33 1 0 (13, 0) (4159956310, 1) 61005 :=
  path_append (path_append (path_append
    (seg_sound 34 33 1 536870925 0 16384 0 13 0 c_seg13_0)
    (seg_sound 34 33 1 10737418253 0 16384 16384 536870925 0 c_seg13_1))
    (seg_sound 34 33 1 15569256461 0 16384 32768 10737418253 0 c_seg13_2))
    (seg_sound 34 33 1 4159956310 1 11853 49152 15569256461 0 c_seg13_3)

theorem c_post_13 : PathOK 34 33 1 61006 (13020969643, 0) (13, 0) 4530 :=
  seg_sound 34 33 1 13 0 4530 61006 13020969643 0 c_seg13_4

theorem lift_13_0 : liftSegFast 13 30288109371405 = true := by decide +kernel
theorem lift_13_1 : liftSegFast 30288109371405 34943853920269 = true := by decide +kernel
theorem lift_13_2 : liftSegFast 34943853920269 37125697306637 = true := by decide +kernel
theorem lift_13_3 : liftSegFast 37125697306637 29274497089549 = true := by decide +kernel
theorem lift_13_4 : liftSegFast 29274497089549 36472862277645 = true := by decide +kernel
theorem lift_13_5 : liftSegFast 36472862277645 33157147525133 = true := by decide +kernel
theorem lift_13_6 : liftSegFast 33157147525133 35064113004557 = true := by decide +kernel
theorem lift_13_7 : liftSegFast 35064113004557 46729244180493 = true := by decide +kernel
theorem lift_13_8 : liftSegFast 46729244180493 45131516346381 = true := by decide +kernel
theorem lift_13_9 : liftSegFast 45131516346381 54185307406349 = true := by decide +kernel
theorem lift_13_10 : liftSegFast 54185307406349 64063732187149 = true := by decide +kernel
theorem lift_13_11 : liftSegFast 64063732187149 36421322670093 = true := by decide +kernel
theorem lift_13_12 : liftSegFast 36421322670093 43619687858189 = true := by decide +kernel
theorem lift_13_13 : liftSegFast 43619687858189 57896159150093 = true := by decide +kernel
theorem lift_13_14 : liftSegFast 57896159150093 16922171146253 = true := by decide +kernel
theorem lift_13_15 : liftSegFast 16922171146253 13194139533325 = true := by decide +kernel
theorem lift_13_16 : liftSegFast 13194139533325 69870527971341 = true := by decide +kernel
theorem lift_13_17 : liftSegFast 69870527971341 39341900431373 = true := by decide +kernel
theorem lift_13_18 : liftSegFast 39341900431373 59115929862157 = true := by decide +kernel
theorem lift_13_19 : liftSegFast 59115929862157 24876450578445 = true := by decide +kernel
theorem lift_13_20 : liftSegFast 24876450578445 5686536699917 = true := by decide +kernel
theorem lift_13_21 : liftSegFast 5686536699917 46351287058445 = true := by decide +kernel
theorem lift_13_22 : liftSegFast 46351287058445 4277787426829 = true := by decide +kernel
theorem lift_13_23 : liftSegFast 4277787426829 51127290691597 = true := by decide +kernel
theorem lift_13_24 : liftSegFast 51127290691597 58325655879693 = true := by decide +kernel
theorem lift_13_25 : liftSegFast 58325655879693 49787260895245 = true := by decide +kernel
theorem lift_13_26 : liftSegFast 49787260895245 15685220565005 = true := by decide +kernel
theorem lift_13_27 : liftSegFast 15685220565005 67207648247821 = true := by decide +kernel
theorem lift_13_28 : liftSegFast 67207648247821 56813827391501 = true := by decide +kernel
theorem lift_13_29 : liftSegFast 56813827391501 53498112638989 = true := by decide +kernel
theorem lift_13_30 : liftSegFast 53498112638989 12524124635149 = true := by decide +kernel
theorem lift_13_31 : liftSegFast 12524124635149 13 = true := by decide +kernel

theorem cyc_13_0 : Cycle 46 45 13 0 2097152 := by
  refine ⟨by decide, by decide, ?_⟩
  have hl0 := (liftSegFast_sound 0 13 30288109371405 c_pre_13 c_post_13 (by decide) (by decide) lift_13_0).1
  have hp0 : PathOK 46 45 1 0 (13, 0) (30288109371405, 0) 65536 := hl0
  have hl1 := (liftSegFast_sound 65536 30288109371405 34943853920269 c_pre_13 c_post_13 (by decide) (by decide) lift_13_1).1
  have hp1 : PathOK 46 45 1 0 (13, 0) (34943853920269, 0) 131072 := path_append hp0 hl1
  have hl2 := (liftSegFast_sound 131072 34943853920269 37125697306637 c_pre_13 c_post_13 (by decide) (by decide) lift_13_2).1
  have hp2 : PathOK 46 45 1 0 (13, 0) (37125697306637, 0) 196608 := path_append hp1 hl2
  have hl3 := (liftSegFast_sound 196608 37125697306637 29274497089549 c_pre_13 c_post_13 (by decide) (by decide) lift_13_3).1
  have hp3 : PathOK 46 45 1 0 (13, 0) (29274497089549, 0) 262144 := path_append hp2 hl3
  have hl4 := (liftSegFast_sound 262144 29274497089549 36472862277645 c_pre_13 c_post_13 (by decide) (by decide) lift_13_4).1
  have hp4 : PathOK 46 45 1 0 (13, 0) (36472862277645, 0) 327680 := path_append hp3 hl4
  have hl5 := (liftSegFast_sound 327680 36472862277645 33157147525133 c_pre_13 c_post_13 (by decide) (by decide) lift_13_5).1
  have hp5 : PathOK 46 45 1 0 (13, 0) (33157147525133, 0) 393216 := path_append hp4 hl5
  have hl6 := (liftSegFast_sound 393216 33157147525133 35064113004557 c_pre_13 c_post_13 (by decide) (by decide) lift_13_6).1
  have hp6 : PathOK 46 45 1 0 (13, 0) (35064113004557, 0) 458752 := path_append hp5 hl6
  have hl7 := (liftSegFast_sound 458752 35064113004557 46729244180493 c_pre_13 c_post_13 (by decide) (by decide) lift_13_7).1
  have hp7 : PathOK 46 45 1 0 (13, 0) (46729244180493, 0) 524288 := path_append hp6 hl7
  have hl8 := (liftSegFast_sound 524288 46729244180493 45131516346381 c_pre_13 c_post_13 (by decide) (by decide) lift_13_8).1
  have hp8 : PathOK 46 45 1 0 (13, 0) (45131516346381, 0) 589824 := path_append hp7 hl8
  have hl9 := (liftSegFast_sound 589824 45131516346381 54185307406349 c_pre_13 c_post_13 (by decide) (by decide) lift_13_9).1
  have hp9 : PathOK 46 45 1 0 (13, 0) (54185307406349, 0) 655360 := path_append hp8 hl9
  have hl10 := (liftSegFast_sound 655360 54185307406349 64063732187149 c_pre_13 c_post_13 (by decide) (by decide) lift_13_10).1
  have hp10 : PathOK 46 45 1 0 (13, 0) (64063732187149, 0) 720896 := path_append hp9 hl10
  have hl11 := (liftSegFast_sound 720896 64063732187149 36421322670093 c_pre_13 c_post_13 (by decide) (by decide) lift_13_11).1
  have hp11 : PathOK 46 45 1 0 (13, 0) (36421322670093, 0) 786432 := path_append hp10 hl11
  have hl12 := (liftSegFast_sound 786432 36421322670093 43619687858189 c_pre_13 c_post_13 (by decide) (by decide) lift_13_12).1
  have hp12 : PathOK 46 45 1 0 (13, 0) (43619687858189, 0) 851968 := path_append hp11 hl12
  have hl13 := (liftSegFast_sound 851968 43619687858189 57896159150093 c_pre_13 c_post_13 (by decide) (by decide) lift_13_13).1
  have hp13 : PathOK 46 45 1 0 (13, 0) (57896159150093, 0) 917504 := path_append hp12 hl13
  have hl14 := (liftSegFast_sound 917504 57896159150093 16922171146253 c_pre_13 c_post_13 (by decide) (by decide) lift_13_14).1
  have hp14 : PathOK 46 45 1 0 (13, 0) (16922171146253, 0) 983040 := path_append hp13 hl14
  have hl15 := (liftSegFast_sound 983040 16922171146253 13194139533325 c_pre_13 c_post_13 (by decide) (by decide) lift_13_15).1
  have hp15 : PathOK 46 45 1 0 (13, 0) (13194139533325, 0) 1048576 := path_append hp14 hl15
  have hl16 := (liftSegFast_sound 1048576 13194139533325 69870527971341 c_pre_13 c_post_13 (by decide) (by decide) lift_13_16).1
  have hp16 : PathOK 46 45 1 0 (13, 0) (69870527971341, 0) 1114112 := path_append hp15 hl16
  have hl17 := (liftSegFast_sound 1114112 69870527971341 39341900431373 c_pre_13 c_post_13 (by decide) (by decide) lift_13_17).1
  have hp17 : PathOK 46 45 1 0 (13, 0) (39341900431373, 0) 1179648 := path_append hp16 hl17
  have hl18 := (liftSegFast_sound 1179648 39341900431373 59115929862157 c_pre_13 c_post_13 (by decide) (by decide) lift_13_18).1
  have hp18 : PathOK 46 45 1 0 (13, 0) (59115929862157, 0) 1245184 := path_append hp17 hl18
  have hl19 := (liftSegFast_sound 1245184 59115929862157 24876450578445 c_pre_13 c_post_13 (by decide) (by decide) lift_13_19).1
  have hp19 : PathOK 46 45 1 0 (13, 0) (24876450578445, 0) 1310720 := path_append hp18 hl19
  have hl20 := (liftSegFast_sound 1310720 24876450578445 5686536699917 c_pre_13 c_post_13 (by decide) (by decide) lift_13_20).1
  have hp20 : PathOK 46 45 1 0 (13, 0) (5686536699917, 0) 1376256 := path_append hp19 hl20
  have hl21 := (liftSegFast_sound 1376256 5686536699917 46351287058445 c_pre_13 c_post_13 (by decide) (by decide) lift_13_21).1
  have hp21 : PathOK 46 45 1 0 (13, 0) (46351287058445, 0) 1441792 := path_append hp20 hl21
  have hl22 := (liftSegFast_sound 1441792 46351287058445 4277787426829 c_pre_13 c_post_13 (by decide) (by decide) lift_13_22).1
  have hp22 : PathOK 46 45 1 0 (13, 0) (4277787426829, 0) 1507328 := path_append hp21 hl22
  have hl23 := (liftSegFast_sound 1507328 4277787426829 51127290691597 c_pre_13 c_post_13 (by decide) (by decide) lift_13_23).1
  have hp23 : PathOK 46 45 1 0 (13, 0) (51127290691597, 0) 1572864 := path_append hp22 hl23
  have hl24 := (liftSegFast_sound 1572864 51127290691597 58325655879693 c_pre_13 c_post_13 (by decide) (by decide) lift_13_24).1
  have hp24 : PathOK 46 45 1 0 (13, 0) (58325655879693, 0) 1638400 := path_append hp23 hl24
  have hl25 := (liftSegFast_sound 1638400 58325655879693 49787260895245 c_pre_13 c_post_13 (by decide) (by decide) lift_13_25).1
  have hp25 : PathOK 46 45 1 0 (13, 0) (49787260895245, 0) 1703936 := path_append hp24 hl25
  have hl26 := (liftSegFast_sound 1703936 49787260895245 15685220565005 c_pre_13 c_post_13 (by decide) (by decide) lift_13_26).1
  have hp26 : PathOK 46 45 1 0 (13, 0) (15685220565005, 0) 1769472 := path_append hp25 hl26
  have hl27 := (liftSegFast_sound 1769472 15685220565005 67207648247821 c_pre_13 c_post_13 (by decide) (by decide) lift_13_27).1
  have hp27 : PathOK 46 45 1 0 (13, 0) (67207648247821, 0) 1835008 := path_append hp26 hl27
  have hl28 := (liftSegFast_sound 1835008 67207648247821 56813827391501 c_pre_13 c_post_13 (by decide) (by decide) lift_13_28).1
  have hp28 : PathOK 46 45 1 0 (13, 0) (56813827391501, 0) 1900544 := path_append hp27 hl28
  have hl29 := (liftSegFast_sound 1900544 56813827391501 53498112638989 c_pre_13 c_post_13 (by decide) (by decide) lift_13_29).1
  have hp29 : PathOK 46 45 1 0 (13, 0) (53498112638989, 0) 1966080 := path_append hp28 hl29
  have hl30 := (liftSegFast_sound 1966080 53498112638989 12524124635149 c_pre_13 c_post_13 (by decide) (by decide) lift_13_30).1
  have hp30 : PathOK 46 45 1 0 (13, 0) (12524124635149, 0) 2031616 := path_append hp29 hl30
  have hl31 := (liftSegFast_sound 2031616 12524124635149 13 c_pre_13 c_post_13 (by decide) (by decide) lift_13_31).1
  have hp31 : PathOK 46 45 1 0 (13, 0) (13, 0) 2097152 := path_append hp30 hl31
  exact hp31

theorem family4_of_class_46 (m q δ lam v : Nat) (hq : m % 2 = q) (hδ : 1 ≤ δ)
    (hdev : dev4 q δ v = true)
    (hcyc : Cycle 46 45 (pk (fun i => tail4 v (δ - 1 + i)) 46) ((q + δ) % 2) lam) :
    (∀ k, 1 ≤ k → k < m + δ → row4 m v k = stripe k) ∧
      row4 m v (m + δ) ≠ stripe (m + δ) ∧
      ∃ t, t ≤ m + δ - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row4 m v) t 1 = false := by
  simp only [dev4, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at hdev
  obtain ⟨hall, hne⟩ := hdev
  have hag : ∀ k, 1 ≤ k → k < m + δ → row4 m v k = stripe k := by
    intro k hk1 hk2
    unfold row4
    by_cases hkm : k ≤ m
    · rw [ite_eq_left hkm]
    · rw [ite_eq_right hkm]
      obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
      rw [stripe_add_mod m q j hq, show m + j - m - 1 = j - 1 by omega]
      rcases hall j (by omega) with h | h
      · omega
      · exact h
  refine ⟨hag, ?_, ?_⟩
  · unfold row4
    rw [ite_eq_right (by omega), show m + δ - m - 1 = δ - 1 by omega,
      stripe_add_mod m q δ hq]
    exact hne
  · have hw : pk (fun i => row4 m v (m + δ + i)) 46 =
        pk (fun i => tail4 v (δ - 1 + i)) 46 :=
      pk_congr _ _ _ fun i _ => by
        unfold row4
        rw [ite_eq_right (by omega), show m + δ + i - m - 1 = δ - 1 + i by omega]
    have hp : (m + δ) % 2 = (q + δ) % 2 := by omega
    rw [← hw, ← hp] at hcyc
    obtain ⟨s, hs, he, hz⟩ := front_sound (row4 m v) (m + δ) 46 45 lam
      (by omega) hag (by omega) hcyc
    exact ⟨m + δ - 1 + s, by omega, he, hz⟩

/-- Five tail bits, read from the boundary outwards. -/
def tail5 (v i : Nat) : Bool := if i < 5 then v.testBit i else false

/-- A stripe prefix, five extra cells, and an infinite white tail. -/
def row5 (m v k : Nat) : Bool :=
  if k ≤ m then stripe k else tail5 v (k - m - 1)

def dev5 (q δ v : Nat) : Bool :=
  (List.range δ).all (fun j => j == 0 || tail5 v (j - 1) == stripe (q + j)) &&
    tail5 v (δ - 1) != stripe (q + δ)

theorem family5_of_class (m q δ K S H lam v : Nat) (hq : m % 2 = q) (hδ : 1 ≤ δ) (hSK : S < K) (hSH : S ≤ H)
    (hdev : dev5 q δ v = true)
    (h : (q + δ) % 2 = 1 ∨ Cycle K S (pk (fun i => tail5 v (δ - 1 + i)) K) ((q + δ) % 2) lam) :
    (∀ k, 1 ≤ k → k < m + δ → row5 m v k = stripe k) ∧
      row5 m v (m + δ) ≠ stripe (m + δ) ∧
      ∃ t, t ≤ m + δ - 1 + H ∧ t % 2 = 0 ∧ zrow (row5 m v) t 1 = false := by
  simp only [dev5, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at hdev
  obtain ⟨hall, hne⟩ := hdev
  have hag : ∀ k, 1 ≤ k → k < m + δ → row5 m v k = stripe k := by
    intro k hk1 hk2
    unfold row5
    by_cases hkm : k ≤ m
    · rw [ite_eq_left hkm]
    · rw [ite_eq_right hkm]
      obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
      rw [stripe_add_mod m q j hq, show m + j - m - 1 = j - 1 by omega]
      rcases hall j (by omega) with h | h
      · omega
      · exact h
  have hne' : row5 m v (m + δ) ≠ stripe (m + δ) := by
    unfold row5
    rw [ite_eq_right (by omega), show m + δ - m - 1 = δ - 1 by omega,
      stripe_add_mod m q δ hq]
    exact hne
  refine ⟨hag, hne', ?_⟩
  rcases h with hodd | hcyc
  · exact ⟨m + δ - 1, by omega, by omega,
      first_defect_hits (row5 m v) (m + δ) (by omega) hag hne'⟩
  · have hw : pk (fun i => row5 m v (m + δ + i)) K =
        pk (fun i => tail5 v (δ - 1 + i)) K :=
      pk_congr _ _ _ fun i _ => by
        unfold row5
        rw [ite_eq_right (by omega), show m + δ + i - m - 1 = δ - 1 + i by omega]
    have hp : (m + δ) % 2 = (q + δ) % 2 := by omega
    rw [← hw, ← hp] at hcyc
    obtain ⟨s, hs, he, hz⟩ := front_sound (row5 m v) (m + δ) K S lam
      (by omega) hag (by omega) hcyc
    exact ⟨m + δ - 1 + s, by omega, he, hz⟩

private theorem lt_sixteen_cases : ∀ v, v < 16 →
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨
      v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15 := by
  decide

/-- **Stripe prefixes with four tail cells die within 31 steps of arrival.** For every `m` and
every four-bit tail `v` but `13` with `m` odd, the first deviation `d` of `S[1..m] · v · 0^∞` from
the stripe satisfies `d ≤ m + 6`, and depth `1` is white at some even time `t ≤ d - 1 + 31`. -/
theorem stripe_four_tail (m : Nat) (v : Fin 16) (hv : v.val ≠ 13 ∨ m % 2 = 0) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 6 ∧
      (∀ k, 1 ≤ k → k < d → row4 m v.val k = stripe k) ∧
      row4 m v.val d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row4 m v.val) t 1 = false := by
  obtain ⟨v, hv16⟩ := v
  rcases Nat.mod_two_eq_zero_or_one m with hq | hq <;>
    rcases lt_sixteen_cases v hv16 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 4096 0 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_0_1)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 3 4096 1 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_0_1)
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 16384 2 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_2_1)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 2 4096 3 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_1_0)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 65536 4 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_4_1)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 5 4096 5 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_0_1)
    exact ⟨m + 5, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 4096 6 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_6_1)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 2 16384 7 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_3_0)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 32768 8 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc4_8)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 3 16384 9 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_2_1)
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 8192 10 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc4_10)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 2 65536 11 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_5_0)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 16384 12 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc4_12)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 4 4096 13 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_1_0)
    exact ⟨m + 4, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 1 65536 14 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc4_14)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 0 2 16384 15 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_7_0)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 2 4096 0 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_0_1)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 1 4096 1 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_1_0)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 4 4096 2 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_0_1)
    exact ⟨m + 4, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 1 16384 3 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_3_0)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 2 16384 4 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_2_1)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 1 65536 5 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_5_0)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 3 4096 6 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_1_0)
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 1 16384 7 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_7_0)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 2 65536 8 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_4_1)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 1 4096 9 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc4_9)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 6 4096 10 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_0_1)
    exact ⟨m + 6, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 1 65536 11 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc4_11)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 2 4096 12 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_6_1)
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · simp at hv
    omega
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 3 16384 14 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_3_0)
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family4_of_class m 1 1 16384 15 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc4_15)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩

/-- **Stripe prefixes with four tail cells die within 45 steps of arrival.**
Unconditional mortality for every `m` and every four-bit tail `v : Fin 16`. -/
theorem stripe_four_tail_all (m : Nat) (v : Fin 16) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 6 ∧
      (∀ k, 1 ≤ k → k < d → row4 m v.val k = stripe k) ∧
      row4 m v.val d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row4 m v.val) t 1 = false := by
  by_cases hv : v.val ≠ 13 ∨ m % 2 = 0
  · obtain ⟨d, hd1, hd2, hag, hne, t, ht, he, hz⟩ := stripe_four_tail m v hv
    exact ⟨d, hd1, hd2, hag, hne, t, by omega, he, hz⟩
  · have hv13 : v.val = 13 := by omega
    have hq : m % 2 = 1 := by omega
    rw [hv13]
    obtain ⟨h1, h2, h3⟩ := family4_of_class_46 m 1 1 2097152 13 hq (by omega)
      (by decide +kernel) (cycle_congr (by decide +kernel) (by decide) cyc_13_0)
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩

private theorem lt_thirty_two_cases : ∀ v, v < 32 →
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨
    v = 8 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨ v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15 ∨
    v = 16 ∨ v = 17 ∨ v = 18 ∨ v = 19 ∨ v = 20 ∨ v = 21 ∨ v = 22 ∨ v = 23 ∨
    v = 24 ∨ v = 25 ∨ v = 26 ∨ v = 27 ∨ v = 28 ∨ v = 29 ∨ v = 30 ∨ v = 31 := by
  decide

/-- **Stripe prefixes with five tail cells die within 45 steps of arrival.**
For every `m` and every five-bit tail `v : Fin 32`, the first deviation `d` of `S[1..m] · v · 0^∞`
from the stripe is at depth `≤ m + 7`, and depth `1` is white at some even time `≤ d - 1 + 45`. -/
theorem stripe_five_tail (m : Nat) (v : Fin 32) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 7 ∧
      (∀ k, 1 ≤ k → k < d → row5 m v.val k = stripe k) ∧
      row5 m v.val d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row5 m v.val) t 1 = false := by
  obtain ⟨v, hv32⟩ := v
  rcases Nat.mod_two_eq_zero_or_one m with hq | hq <;>
    rcases lt_thirty_two_cases v hv32 with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 0 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 3 32 31 45 0 1 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 2 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 2 32 31 45 4096 3 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 4 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 5 32 31 45 0 5 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 5, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 6 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 2 32 31 45 16384 7 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 8 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 3 32 31 45 0 9 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 10 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 2 32 31 45 65536 11 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_5_0))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 12 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 4 32 31 45 4096 13 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
    exact ⟨m + 4, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 14 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 2 32 31 45 16384 15 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_7_0))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 16 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 3 32 31 45 0 17 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 18 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 2 32 31 45 4096 19 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_9))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 20 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 7 32 31 45 0 21 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 7, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 22 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 2 32 31 45 65536 23 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_11))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 24 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 3 32 31 45 0 25 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 26 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 2 46 45 45 2097152 27 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_13_0))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 28 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 4 32 31 45 16384 29 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
    exact ⟨m + 4, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 1 32 31 45 0 30 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 0 2 32 31 45 16384 31 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_15))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 2 32 31 45 0 0 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 4096 1 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 4 32 31 45 0 2 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 4, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 16384 3 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 2 32 31 45 0 4 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 65536 5 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_5_0))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 3 32 31 45 4096 6 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 16384 7 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_7_0))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 2 32 31 45 0 8 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 4096 9 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_9))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 6 32 31 45 0 10 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 6, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 65536 11 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_11))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 2 32 31 45 0 12 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 46 45 45 2097152 13 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_13_0))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 3 32 31 45 16384 14 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 16384 15 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_15))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 2 32 31 45 0 16 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 16384 17 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_17))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 4 32 31 45 0 18 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 4, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 65536 19 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_19))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 2 32 31 45 0 20 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 32768 21 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_21))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 3 32 31 45 65536 22 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_5_0))
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 16384 23 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_23))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 2 32 31 45 0 24 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 16384 25 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_25))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 5 32 31 45 4096 26 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
    exact ⟨m + 5, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 4096 27 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_27))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 2 32 31 45 0 28 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inl (by decide))
    exact ⟨m + 2, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 65536 29 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_29))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 3 32 31 45 16384 30 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_7_0))
    exact ⟨m + 3, by omega, by omega, h1, h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := family5_of_class m 1 1 32 31 45 65536 31 hq (by omega) (by omega) (by omega) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_31))
    exact ⟨m + 1, by omega, by omega, h1, h2, h3⟩

theorem stripe_five_tail_all (m : Nat) (v : Fin 32) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 7 ∧
      (∀ k, 1 ≤ k → k < d → row5 m v.val k = stripe k) ∧
      row5 m v.val d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row5 m v.val) t 1 = false :=
  stripe_five_tail m v


end Rule30Submission
