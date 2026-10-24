module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontPeriod

/-! Bit-parallel high-window updates above a shared lower front window.
The generic projection lemmas below do not certify any numerical table. -/

@[expose] public section

/-! Contributed by Troy Lowry and OpenAI Codex. Builds on the catalog's
stripe-front and bit-sliced lane methods. Does not prove Q01 or Problem 1. -/

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontParallel
open Ruliology.CellularAutomata
open Rule30ZeroBoundaryStripeFront Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift

def scan (l r : Nat) : List Nat → List Nat
  | [] => []
  | a :: xs => (a ^^^ (l ||| r)) :: scan a l xs

def bscan (l r : Bool) : List Bool → List Bool
  | [] => []
  | a :: xs => xor a (l || r) :: bscan a l xs

theorem scan_length (l r : Nat) (xs : List Nat) : (scan l r xs).length = xs.length := by
  induction xs generalizing l r with
  | nil => rfl
  | cons a xs ih => simp only [scan, List.length_cons, ih]

theorem bscan_length (l r : Bool) (xs : List Bool) : (bscan l r xs).length = xs.length := by
  induction xs generalizing l r with
  | nil => rfl
  | cons a xs ih => simp only [bscan, List.length_cons, ih]

theorem map_bit_scan (l r : Nat) (xs : List Nat) (p : Nat) :
    (scan l r xs).map (fun x => x.testBit p) =
      bscan (l.testBit p) (r.testBit p) (xs.map (fun x => x.testBit p)) := by
  induction xs generalizing l r with
  | nil => rfl
  | cons a xs ih =>
    simp only [scan, bscan, List.map_cons, Nat.testBit_xor, Nat.testBit_or, ih]

def bitMask (ALL : Nat) (b : Bool) : Nat := if b then ALL else 0

theorem bitMask_bit {ALL p : Nat} (h : ALL.testBit p = true) (b : Bool) :
    (bitMask ALL b).testBit p = b := by
  cases b <;> simp [bitMask, h]

structure LaneState where
  lo : Nat
  phase : Nat
  planes : List Nat
deriving DecidableEq

structure BoolState where
  lo : Nat
  phase : Nat
  bits : List Bool
deriving DecidableEq

def project (p : Nat) (s : LaneState) : BoolState :=
  ⟨s.lo, s.phase, s.planes.map (fun x => x.testBit p)⟩

def next (K ALL : Nat) (s : LaneState) : LaneState :=
  ⟨fstep K s.lo s.phase, 1-s.phase,
    scan (bitMask ALL (s.lo.testBit (K-1))) (bitMask ALL (s.lo.testBit (K-2))) s.planes⟩

def bnext (K : Nat) (s : BoolState) : BoolState :=
  ⟨fstep K s.lo s.phase, 1-s.phase,
    bscan (s.lo.testBit (K-1)) (s.lo.testBit (K-2)) s.bits⟩

theorem project_next {ALL p : Nat} (h : ALL.testBit p = true) (K : Nat) (s : LaneState) :
    project p (next K ALL s) = bnext K (project p s) := by
  cases s with
  | mk lo phase planes =>
    simp only [project, next, bnext, map_bit_scan, bitMask_bit h]

noncomputable def run (K ALL : Nat) : Nat → LaneState → LaneState :=
  Nat.rec (motive := fun _ => LaneState → LaneState) (fun s => s)
    (fun _ ih s => ih (next K ALL s))

def brun (K : Nat) : Nat → BoolState → BoolState
  | 0, s => s
  | n+1, s => brun K n (bnext K s)

theorem project_run {ALL p : Nat} (h : ALL.testBit p = true) (K t : Nat) (s : LaneState) :
    project p (run K ALL t s) = brun K t (project p s) := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    change project p (run K ALL t (next K ALL s)) = brun K t (bnext K (project p s))
    rw [← project_next h K s]
    exact ih _

theorem bscan_getD (l r : Bool) (xs : List Bool) (i : Nat) (hi : i < xs.length) :
    (bscan l r xs).getD i false = xor (xs.getD i false)
      ((if i = 0 then l else xs.getD (i-1) false) ||
       (if i = 0 then r else if i = 1 then l else xs.getD (i-2) false)) := by
  induction xs generalizing l r i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => cases xs with
        | nil => simp at hi
        | cons b xs => rfl
      | succ i =>
        have h := ih a l (i+1) (by simpa using hi)
        cases i <;> simpa [bscan, Nat.add_sub_cancel] using h

def config (K : Nat) (s : BoolState) (i : Nat) : Bool :=
  if i < K then s.lo.testBit i else s.bits.getD (i-K) false

def Represents (K row : Nat) (s : BoolState) : Prop :=
  ∀ i, i < K+s.bits.length → row.testBit i = config K s i

/-- Every high bit uses precisely the two preceding old bits. The shared low
window supplies the two missing boundary bits, for every lane simultaneously. -/
theorem represents_next {K row : Nat} {s : BoolState} (hK : 2 ≤ K)
    (hp : s.phase < 2) (h : Represents K row s) :
    Represents K (fstep (K+s.bits.length) row s.phase) (bnext K s) := by
  intro i hi
  have hti : i < K+s.bits.length := by simpa only [bnext, bscan_length] using hi
  rw [testBit_fstep _ _ _ _ hp]
  by_cases hlo : i < K
  · have hc : ∀ j, j ≤ i → row.testBit j = s.lo.testBit j := by
      intro j hj
      have hjK : j < K := by omega
      simpa only [config, ite_eq_left hjK] using h j (by omega)
    simp only [config, bnext, ite_eq_left hlo]
    rw [testBit_fstep _ _ _ _ hp]
    simp only [decide_eq_true hti, decide_eq_true hlo, Bool.true_and,
      hc i (Nat.le_refl _), hc (i-1) (by omega), hc (i-2) (by omega)]
  · simp only [config, bnext, ite_eq_right hlo]
    rw [bscan_getD _ _ _ _ (by omega)]
    simp only [decide_eq_true hti, Bool.true_and,
      ite_eq_right (show i ≠ 0 by omega), ite_eq_right (show i ≠ 1 by omega)]
    rw [h i hti, h (i-1) (by omega), h (i-2) (by omega)]
    by_cases hb : i = K
    · subst i
      simp [config, show K-1 < K by omega, show K-2 < K by omega]
    · by_cases hb1 : i = K+1
      · subst i
        simp [config, show ¬ (K+1 < K) by omega, show K+1-1 = K by omega, show K+1-2 = K-1 by omega,
          show K+1-K = 1 by omega, show K-1 < K by omega]
      · have hbig : K+2 ≤ i := by omega
        simp only [config, ite_eq_right hlo,
          ite_eq_right (show ¬ (i-1 < K) by omega),
          ite_eq_right (show ¬ (i-2 < K) by omega),
          ite_eq_right (show i-K ≠ 0 by omega),
          ite_eq_right (show i-K ≠ 1 by omega),
          show i-1-K = i-K-1 by omega,
          show i-2-K = i-K-2 by omega]

theorem brun_length (K t : Nat) (s : BoolState) :
    (brun K t s).bits.length = s.bits.length := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    change (brun K t (bnext K s)).bits.length = s.bits.length
    rw [ih]
    exact bscan_length _ _ _

/-- The Boolean lane follows the actual official finite front orbit, for all
times. The representation specifies every bit in the finite window. -/
theorem brun_represents {K row : Nat} {s : BoolState} (hK : 2 ≤ K)
    (hp : s.phase < 2) (h : Represents K row s) (t : Nat) :
    (brun K t s).phase = (orb (K+s.bits.length) t (row,s.phase)).2 ∧
      Represents K (orb (K+s.bits.length) t (row,s.phase)).1 (brun K t s) := by
  induction t generalizing row s with
  | zero => exact ⟨rfl, h⟩
  | succ t ih =>
    have hp' : (bnext K s).phase < 2 := by change 1-s.phase < 2; omega
    have hn := represents_next hK hp h
    have hr := ih (row := fstep (K+s.bits.length) row s.phase) (s := bnext K s) hp' hn
    simpa only [brun, bnext, bscan_length, orb_succ', fS] using hr

theorem run_represents {ALL p K row : Nat} {s : LaneState}
    (hALL : ALL.testBit p = true) (hK : 2 ≤ K) (hp : s.phase < 2)
    (h : Represents K row (project p s)) (t : Nat) :
    Represents K (orb (K+s.planes.length) t (row,s.phase)).1 (project p (run K ALL t s)) := by
  rw [project_run hALL]
  have hr := (brun_represents hK hp h t).2
  simpa only [project, List.length_map] using hr

def word (K : Nat) (s : BoolState) : Nat :=
  s.lo ||| ((pk (fun j => s.bits.getD j false) s.bits.length) <<< K)

theorem word_bound (K : Nat) (s : BoolState) (hlo : s.lo < 2^K) :
    word K s < 2^(K+s.bits.length) := by
  apply Nat.lt_pow_two_of_testBit _
  intro i hi
  unfold word
  rw [Nat.testBit_or, Nat.testBit_shiftLeft,
    Rule30ZeroBoundarySmall.testBit_ge_of_lt hlo (by omega), testBit_pk]
  simp [show K ≤ i by omega, show ¬ (i-K < s.bits.length) by omega]

theorem word_represents (K : Nat) (s : BoolState) (hlo : s.lo < 2^K) :
    Represents K (word K s) s := by
  intro i hi
  unfold word
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h : i < K
  · simp only [config, ite_eq_left h, decide_eq_false (show ¬ (K ≤ i) by omega),
      Bool.false_and, Bool.or_false]
  · rw [Rule30ZeroBoundarySmall.testBit_ge_of_lt hlo (by omega), testBit_pk]
    simp only [Bool.false_or, decide_eq_true (show K ≤ i by omega), Bool.true_and,
      decide_eq_true (show i-K < s.bits.length by omega), config, ite_eq_right h]

theorem represents_unique {K row : Nat} {s : BoolState}
    (hr : row < 2^(K+s.bits.length)) (hlo : s.lo < 2^K) (h : Represents K row s) :
    row = word K s := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < K+s.bits.length
  · exact (h i hi).trans ((word_represents K s hlo) i hi).symm
  · rw [Rule30ZeroBoundarySmall.testBit_ge_of_lt hr (by omega),
      Rule30ZeroBoundarySmall.testBit_ge_of_lt (word_bound K s hlo) (by omega)]

theorem brun_lo_bound {K : Nat} {s : BoolState} (hlo : s.lo < 2^K) (t : Nat) :
    (brun K t s).lo < 2^K := by
  induction t generalizing s with
  | zero => exact hlo
  | succ t ih =>
    change (brun K t (bnext K s)).lo < 2^K
    exact ih (Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontPeriod.fstep_bound _ _ _)

/-- Integer endpoint semantics of the parallel program, including phase.
Every closed program equality can therefore certify all of its input lanes. -/
theorem run_correct {ALL p K : Nat} {s : LaneState}
    (hALL : ALL.testBit p = true) (hK : 2 ≤ K) (hp : s.phase < 2)
    (hlo : s.lo < 2^K) (t : Nat) :
    orb (K+s.planes.length) t (word K (project p s), s.phase) =
      (word K (project p (run K ALL t s)), (run K ALL t s).phase) := by
  have hi := word_represents K (project p s) hlo
  have hr := run_represents hALL hK hp hi t
  have he := project_run hALL K t s
  have hl : (project p (run K ALL t s)).lo < 2^K := by
    rw [he]
    exact brun_lo_bound hlo t
  have hn : (project p (run K ALL t s)).bits.length = s.planes.length := by
    rw [he, brun_length]
    exact List.length_map _
  have hb : (orb (K+s.planes.length) t (word K (project p s),s.phase)).1 <
      2^(K+(project p (run K ALL t s)).bits.length) := by
    rw [hn]
    apply Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontPeriod.orbit_bound
    simpa only [project, List.length_map] using word_bound K (project p s) hlo
  apply Prod.ext
  · exact represents_unique hb hl hr
  · have hphase := (brun_represents hK hp hi t).1
    have hh : (project p (run K ALL t s)).phase =
        (orb (K+s.planes.length) t (word K (project p s),s.phase)).2 := by
      rw [he]
      simpa only [project, List.length_map] using hphase
    exact hh.symm

def initial (m a p : Nat) : LaneState :=
  ⟨a, p, (List.range m).map (Rule30ZeroBoundaryLanes.pat m)⟩

def allMask (m : Nat) : Nat := 2^(2^m)-1

theorem allMask_bit {m u : Nat} (hu : u < 2^m) : (allMask m).testBit u = true := by
  simp only [allMask, Nat.testBit_two_pow_sub_one, decide_eq_true hu]

theorem pk_pats (m u : Nat) (hu : u < 2^m) :
    pk (fun j => (((List.range m).map (Rule30ZeroBoundaryLanes.pat m)).getD j 0).testBit u) m = u := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_pk]
  by_cases hi : i < m
  · rw [decide_eq_true hi, Bool.true_and, Rule30ZeroBoundaryLanes.pats_getD m i hi,
      Rule30ZeroBoundaryLanes.pat_spec m i u hi hu]
  · rw [decide_eq_false hi, Bool.false_and,
      Rule30ZeroBoundarySmall.testBit_ge_of_lt hu (by omega)]

theorem initial_word (K m a phase u : Nat) (hu : u < 2^m) :
    word K (project u (initial m a phase)) = a ||| (u <<< K) := by
  simp only [word, project, initial, List.length_map, List.length_range,
    ← Rule30ZeroBoundaryLanes.getD_testBit]
  rw [pk_pats m u hu]

theorem initial_run_correct (K m a phase u t : Nat) (hK : 2 ≤ K)
    (ha : a < 2^K) (hp : phase < 2) (hu : u < 2^m) :
    orb (K+m) t (a ||| (u <<< K), phase) =
      (word K (project u (run K (allMask m) t (initial m a phase))),
        (run K (allMask m) t (initial m a phase)).phase) := by
  have hc := run_correct (s := initial m a phase) (allMask_bit hu) hK hp ha t
  rw [initial_word K m a phase u hu] at hc
  simpa only [initial, List.length_map, List.length_range] using hc

theorem run_zero (K ALL : Nat) (s : LaneState) : run K ALL 0 s = s := rfl

theorem run_succ (K ALL n : Nat) (s : LaneState) :
    run K ALL (n+1) s = run K ALL n (next K ALL s) := rfl

theorem run_add (K ALL a b : Nat) (s : LaneState) :
    run K ALL (a+b) s = run K ALL b (run K ALL a s) := by
  induction a generalizing s with
  | zero => rw [Nat.zero_add, run_zero]
  | succ a ih =>
    rw [Nat.succ_add, run_succ, ih, run_succ]

theorem run_chain {K ALL a b : Nat} {s t u : LaneState}
    (ha : run K ALL a s = t) (hb : run K ALL b t = u) :
    run K ALL (a+b) s = u := by rw [run_add, ha, hb]

end Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontParallel
