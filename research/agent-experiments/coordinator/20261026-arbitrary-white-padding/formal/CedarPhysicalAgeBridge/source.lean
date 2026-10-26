import FrontBlackInterval
import PhysicalEarlyCases
import Ruliology.CellularAutomata.Rule30Realization

/-! Global free-front recurrence and the physical age bridge. -/
namespace CedarPhysicalAgeBridge
open Ruliology.CellularAutomata Rule30Jen Rule30Realization

def freeRow (t : Nat) (D p : Int) : Bool :=
  if p < D then false else cell t p

def freeEvol (t : Nat) (D : Int) (k : Nat) (p : Int) : Bool :=
  evol (freeRow t D) k p

theorem free_succ (t : Nat) (D : Int) (k : Nat) (p l c r : Int)
    (hl : l = p-1) (hc : c = p) (hr : r = p+1) :
    freeEvol t D (k+1) p =
      rule (freeEvol t D k l) (freeEvol t D k c) (freeEvol t D k r) := by
  subst l c r
  rfl

theorem free_support (t : Nat) (D : Int) :
    ∀ (k : Nat) (p : Int), p < D-(k:Int) → freeEvol t D k p = false
  | 0, p, hp => by simp [freeEvol, evol, freeRow, show p < D by omega]
  | k+1, p, hp => by
    change rule (freeEvol t D k (p-1)) (freeEvol t D k p)
      (freeEvol t D k (p+1)) = false
    rw [free_support t D k (p-1) (by omega),
      free_support t D k p (by omega), free_support t D k (p+1) (by omega)]
    rfl

def front (t : Nat) (D : Int) (i k : Nat) : Bool :=
  freeEvol t D k (D-(k:Int)+(i:Int))

theorem front_recurrence (t : Nat) (D : Int) :
    FrontBlackInterval.Recurrence (front t D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    change freeEvol t D (k+1) (D-((k+1:Nat):Int)+0) =
      freeEvol t D k (D-(k:Int)+0)
    rw [free_succ t D k _ (D-(k:Int)-2) (D-(k:Int)-1) (D-(k:Int))
      (by omega) (by omega) (by omega), free_support t D k (D-(k:Int)-2) (by omega),
      free_support t D k (D-(k:Int)-1) (by omega)]
    simp [rule]
  · intro k
    change freeEvol t D (k+1) (D-((k+1:Nat):Int)+1) = _
    rw [free_succ t D k _ (D-(k:Int)-1) (D-(k:Int)) (D-(k:Int)+1)
      (by omega) (by omega) (by omega), free_support t D k (D-(k:Int)-1) (by omega)]
    simp [front, rule]
  · intro i k
    change freeEvol t D (k+1) (D-((k+1:Nat):Int)+((i+2:Nat):Int)) = _
    rw [free_succ t D k _ (D-(k:Int)+(i:Int))
      (D-(k:Int)+((i+1:Nat):Int)) (D-(k:Int)+((i+2:Nat):Int))
      (by omega) (by omega) (by omega)]
    rfl

theorem free_initial_agrees (t : Nat) (D : Int)
    (hrow : ∀ p : Int, 0 < p → p < D → cell t p = false)
    (p : Int) (hp : 0 < p) : freeEvol t D 0 p = cell t p := by
  unfold freeEvol evol freeRow
  split
  · exact (hrow p hp ‹p < D›).symm
  · rfl

/-- Equality on the whole positive half-line, retaining the ORIGINAL age. -/
theorem before_arrival (t N : Nat) (D : Int) (hD : (N:Int) < D)
    (hrow : ∀ p : Int, 0 < p → p < D → cell t p = false)
    (hw : ∀ k, k < N → cell (t+k) 0 = false) :
    ∀ k, k ≤ N → ∀ p : Int, 0 < p → freeEvol t D k p = cell (t+k) p := by
  intro k
  induction k with
  | zero => intro hk p hp; simpa using free_initial_agrees t D hrow p hp
  | succ k ih =>
    intro hk p hp
    have hl : freeEvol t D k (p-1) = cell (t+k) (p-1) := by
      by_cases he : p=1
      · subst p
        rw [show (1:Int)-1=0 by omega, free_support t D k 0 (by omega), hw k (by omega)]
      · exact ih (by omega) (p-1) (by omega)
    rw [show t+(k+1)=t+k+1 by omega]
    change rule (freeEvol t D k (p-1)) (freeEvol t D k p)
      (freeEvol t D k (p+1)) =
      rule (cell (t+k) (p-1)) (cell (t+k) p) (cell (t+k) (p+1))
    rw [hl, ih (by omega) p hp, ih (by omega) (p+1) (by omega)]

/-- After coupling at age N, arbitrary center changes propagate at speed one. -/
theorem after_cone (t N : Nat) (D : Int)
    (hN : ∀ p : Int, 0 < p → freeEvol t D N p = cell (t+N) p) :
    ∀ (s : Nat) (p : Int), (s:Int) < p → freeEvol t D (N+s) p = cell (t+N+s) p := by
  intro s
  induction s with
  | zero => intro p hp; simpa using hN p hp
  | succ s ih =>
    intro p hp
    rw [show N+(s+1)=N+s+1 by omega, show t+N+(s+1)=t+N+s+1 by omega]
    change rule (freeEvol t D (N+s) (p-1)) (freeEvol t D (N+s) p)
      (freeEvol t D (N+s) (p+1)) =
      rule (cell (t+N+s) (p-1)) (cell (t+N+s) p) (cell (t+N+s) (p+1))
    rw [ih (p-1) (by omega), ih p (by omega), ih (p+1) (by omega)]

def lower (n : Nat) : Nat := 20*n
def upper (n : Nat) : Nat := lower n + 2^(lower n+1)
def age (n : Nat) : Nat := 2^(upper n)-1
def warmup (n : Nat) : Nat := age n + 9*n
def bound (n : Nat) : Nat := upper n + 11*n

/-- A genuinely aged free front supplies a bounded physical white witness. -/
theorem late_witness (t n j : Nat) (hn : 1 ≤ n) (hj : j < n) (D : Int)
    (hDlo : (age n:Int)+2 ≤ D) (hDhi : D ≤ (age n:Int)+11*n-1)
    (hrow : ∀ p : Int, 0 < p → p < D → cell t p = false)
    (hw : ∀ k, k < age n → cell (t+k) 0 = false) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ bound n ∧ cell (t+warmup n+j) p = false := by
  let N := age n
  let s := 9*n+j
  have hN : ∀ p : Int, 0 < p → freeEvol t D N p = cell (t+N) p :=
    before_arrival t N D (by dsimp [N]; omega) hrow hw N (by omega)
  have hlo : 1 ≤ lower n := by dsimp [lower]; omega
  have he : lower n-1+1=lower n := by omega
  have hage : 2^(lower n-1+1+2^(lower n-1+2))-1 ≤ N+s := by
    have he2 : lower n-1+2=lower n+1 := by omega
    rw [he, he2]
    exact Nat.le_add_right (age n) s
  obtain ⟨i, hi1, hi2, hiw⟩ := FrontBlackInterval.aged_white_witness
    (front_recurrence t D) (lower n-1) (N+s) hage
  rw [he] at hi1 hi2
  have hi2' : i ≤ upper n := by
    have he2 : lower n-1+2=lower n+1 := by omega
    simpa [upper, he2] using hi2
  let p : Int := D-(N:Int)-(s:Int)+(i:Int)
  have hps : (s:Int) < p := by dsimp [p, s, N, lower] at *; omega
  have hpb : p ≤ (bound n:Int) := by
    dsimp [p, s, N, bound] at *
    omega
  have hp0 : 0 ≤ p := by omega
  refine ⟨p.toNat, by omega, by omega, ?_⟩
  have hcouple := after_cone t N D hN s p hps
  have hpos : D-((N+s:Nat):Int)+(i:Int)=p := by dsimp [p]; omega
  change freeEvol t D (N+s) (D-((N+s:Nat):Int)+(i:Int)) = false at hiw
  rw [hpos, hcouple] at hiw
  have ht : t+N+s=t+warmup n+j := by dsimp [N,s,warmup]; omega
  rw [ht] at hiw
  simpa [Int.toNat_of_nonneg hp0] using hiw

theorem white_back_pair (t : Nat) (p : Int)
    (hl : cell t (p-1) = false) (hz : cell (t+1) p = false) :
    cell t p = false ∧ cell t (p+1) = false := by
  change rule (cell t (p-1)) (cell t p) (cell t (p+1)) = false at hz
  rw [hl] at hz
  cases hc : cell t p <;> cases hr : cell t (p+1) <;> simp_all [rule]

/-- A white row prefix expands by one when traced backwards past a white driver. -/
theorem white_back_step (t m : Nat) (hm : 1 ≤ m) (hc : cell t 0 = false)
    (hz : ∀ p : Nat, 1 ≤ p → p ≤ m → cell (t+1) p = false) :
    ∀ p : Nat, 1 ≤ p → p ≤ m+1 → cell t p = false := by
  have pair : ∀ k : Nat, k < m →
      cell t ((k+1:Nat):Int) = false ∧ cell t ((k+2:Nat):Int) = false := by
    intro k
    induction k with
    | zero =>
      intro hk
      simpa using white_back_pair t 1 (by simpa using hc) (hz 1 (by omega) (by omega))
    | succ k ih =>
      intro hk
      have hl := (ih (by omega)).1
      have h := white_back_pair t ((k+2:Nat):Int)
        (by simpa only [show ((k+2:Nat):Int)-1=((k+1:Nat):Int) by omega] using hl)
        (hz (k+2) (by omega) (by omega))
      simpa only [show ((k+2:Nat):Int)+1=((k+1+2:Nat):Int) by omega] using h
  intro p hp hpm
  by_cases he : p=1
  · subst p
    exact (pair 0 (by omega)).1
  · have h := (pair (p-2) (by omega)).2
    simpa only [show p-2+2=p by omega] using h

theorem white_backwards (t N : Nat)
    (hw : ∀ k, k < N → cell (t+k) 0 = false) :
    ∀ m : Nat, 1 ≤ m →
      (∀ p : Nat, 1 ≤ p → p ≤ m → cell (t+N) p = false) →
      ∀ p : Nat, 1 ≤ p → p ≤ m+N → cell t p = false := by
  induction N with
  | zero => intro m hm hz p hp hpm; simpa using hz p hp (by omega)
  | succ N ih =>
    intro m hm hz p hp hpm
    have hz' : ∀ p : Nat, 1 ≤ p → p ≤ m → cell (t+N+1) p = false := by
      simpa only [show t+(N+1)=t+N+1 by omega] using hz
    have prev := white_back_step (t+N) m hm (hw N (by omega)) hz'
    exact ih (fun k hk => hw k (by omega)) (m+1) (by omega) prev p hp (by omega)

theorem original_white_prefix (t N : Nat)
    (hw : ∀ k, k < N → cell (t+k) 0 = false) (h1 : cell (t+N) 1 = false) :
    ∀ p : Int, 0 < p → p < (N:Int)+2 → cell t p = false := by
  have hh := white_backwards t N hw 1 (by omega)
    (fun p hp hp1 => by simpa [show p=1 by omega] using h1)
  intro p hp hpN
  have hn := hh p.toNat (by omega) (by omega)
  simpa [Int.toNat_of_nonneg (show 0 ≤ p by omega)] using hn

/-- Every one of the next n ticks has a bounded white cell after the warmup. -/
theorem physical_white_witness (t n j : Nat) (hn : 1 ≤ n) (hj : j < n)
    (hw : ∀ k, k < warmup n → cell (t+k) 0 = false) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ bound n ∧ cell (t+warmup n+j) p = false := by
  cases h1 : cell (t+age n) 1 with
  | true =>
    obtain ⟨p,hp1,hpB,hpw⟩ := PhysicalEarlyCases.early_white_witness
      n (age n) t j hn hj hw h1
    refine ⟨p,hp1,?_,hpw⟩
    unfold bound
    omega
  | false =>
    have hwN : ∀ k, k < age n → cell (t+k) 0 = false :=
      fun k hk => hw k (by dsimp [warmup]; omega)
    exact late_witness t n j hn hj ((age n:Int)+2) (by omega) (by omega)
      (original_white_prefix t (age n) hwN h1) hwN

def BlockBound (u : List Bool) : Prop :=
  ∀ t, (∀ k, k < warmup u.length → cell (t+k) 0 = false) →
    (∀ j, j < u.length → cell (t+warmup u.length+j) 0 = u.getD j false) →
    ∀ j, j < u.length → u.getD j false = true →
      ∃ p : Nat, 1 ≤ p ∧ p ≤ bound u.length ∧ cell (t+warmup u.length+j) p = false

theorem block_bound (u : List Bool) (hu : 1 ≤ u.length) : BlockBound u := by
  intro t hw _ j hj _
  exact physical_white_witness t u.length j hu hj hw

end CedarPhysicalAgeBridge
