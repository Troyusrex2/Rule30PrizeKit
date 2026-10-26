import Ruliology.CellularAutomata.Rule30Diagonals
import Ruliology.CellularAutomata.Rule30Prize

/-!
An arbitrary-width symbolic obstruction to black intervals in an aged front.
The only dynamics assumed are the literal triangular left-diagonal recurrence.
No finite certificate table, bound on the initial width, or common minimal clock
is assumed.  The explicit onset is deliberately enormous.
-/

namespace FrontBlackInterval
open Ruliology.CellularAutomata

def Recurrence (b : Nat → Nat → Bool) : Prop :=
  (∀ t, b 0 (t+1) = b 0 t) ∧
  (∀ t, b 1 (t+1) = (b 0 t || b 1 t)) ∧
  (∀ i t, b (i+2) (t+1) = xor (b i t) (b (i+1) t || b (i+2) t))

def PeriodFrom (x : Nat → Bool) (T P : Nat) : Prop :=
  ∀ t, T ≤ t → x (t+P) = x t

theorem period_mono {x : Nat → Bool} {T U P : Nat}
    (h : PeriodFrom x T P) (hTU : T ≤ U) : PeriodFrom x U P :=
  fun _ ht => h _ (Nat.le_trans hTU ht)

theorem period_mul {x : Nat → Bool} {T P : Nat} (h : PeriodFrom x T P)
    (k t : Nat) (ht : T ≤ t) : x (t+k*P) = x t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, h _ (by omega), ih]

theorem period_double {x : Nat → Bool} {T P : Nat} (h : PeriodFrom x T P) :
    PeriodFrom x T (2*P) := by
  intro t ht
  rw [show t+2*P=t+P+P by omega, h _ (by omega), h t ht]

/-- Uniform onset, valid for every initial row, not only an odd front. -/
theorem uniform_period {b : Nat → Nat → Bool} (h : Recurrence b) :
    ∀ i, PeriodFrom (b i) (2^i-1) (2^i) := by
  have pair : ∀ i, PeriodFrom (b i) (2^i-1) (2^i) ∧
      PeriodFrom (b (i+1)) (2^(i+1)-1) (2^(i+1)) := by
    intro i
    induction i with
    | zero =>
      constructor
      · intro t _
        simpa using h.1 t
      · have ht := Rule30Diagonals.transducer_periodic
          (x := b 1) (F := fun t x => b 0 t || x) (T := 0) (L := 1)
          (fun t _ => h.2.1 t)
          (fun t _ => by funext x; rw [h.1 t])
        simpa [PeriodFrom] using ht
    | succ i ih =>
      refine ⟨ih.2, ?_⟩
      have hp : 0 < 2^(i+1) := Nat.two_pow_pos _
      have hpow : 2^(i+2) = 2*2^(i+1) := by
        rw [show i+2=(i+1)+1 by omega, Nat.pow_succ]; omega
      have hpow0 : 2^(i+1) = 2*2^i := by rw [Nat.pow_succ]; omega
      have old : PeriodFrom (b i) (2^(i+1)-1) (2^(i+1)) := by
        rw [hpow0]
        exact period_mono (period_double ih.1) (by omega)
      have ht := Rule30Diagonals.transducer_periodic
        (x := b (i+2)) (F := fun t x => xor (b i t) (b (i+1) t || x))
        (T := 2^(i+1)-1) (L := 2^(i+1))
        (fun t _ => h.2.2 i t)
        (fun t ht => by funext x; rw [old t ht, ih.2 t ht])
      intro t ht0
      rw [show i+1+1=i+2 by omega, hpow] at ht0 ⊢
      exact ht t (by omega)
  exact fun i => (pair i).1

/-- A reset gives eventual P-periodicity. Known Q-periodicity pulls it back
to the stated onset T; no backward transfer is assumed without that clock. -/
theorem reset_inherits {x l g : Nat → Bool} {T P Q A : Nat}
    (hx : ∀ t, x (t+1) = xor (l t) (g t || x t))
    (hl : PeriodFrom l T P) (hg : PeriodFrom g T P)
    (hq : PeriodFrom x T Q) (hQ : 0 < Q)
    (hA : T ≤ A) (hblack : g A = true) : PeriodFrom x T P := by
  have start : x (A+1+P) = x (A+1) := by
    rw [show A+1+P=A+P+1 by omega, hx, hx, hl A hA, hg A hA, hblack]
    simp
  have future : ∀ s, x (A+1+s+P) = x (A+1+s) := by
    intro s
    induction s with
    | zero => simpa using start
    | succ s ih =>
      rw [show A+1+(s+1)+P=(A+1+s+P)+1 by omega,
        show A+1+(s+1)=(A+1+s)+1 by omega, hx, hx,
        hl _ (by omega), hg _ (by omega), ih]
  intro t ht
  have hlarge : A+1 ≤ (A+1)*Q := by
    have hh := Nat.mul_le_mul_left (A+1) (show 1 ≤ Q by omega)
    simpa using hh
  have hf := future (t+(A+1)*Q-(A+1))
  rw [show A+1+(t+(A+1)*Q-(A+1))=t+(A+1)*Q by omega] at hf
  rw [show t+(A+1)*Q+P=t+P+(A+1)*Q by omega,
    period_mul hq (A+1) (t+P) (by omega), period_mul hq (A+1) t ht] at hf
  exact hf

theorem rec_at {b : Nat → Nat → Bool} (h : Recurrence b) (i t : Nat) (hi : 2 ≤ i) :
    b i (t+1) = xor (b (i-2) t) (b (i-1) t || b i t) := by
  have hh := h.2.2 (i-2) t
  simpa [show i-2+2=i by omega, show i-2+1=i-1 by omega] using hh

/-- A black interval becomes a white interior after one tick; its white
interior then shrinks by two cells on the left per tick. -/
theorem black_erodes {b : Nat → Nat → Bool} (h : Recurrence b) {lo hi A : Nat}
    (hb : ∀ i, lo ≤ i → i ≤ hi → b i A = true) :
    ∀ n i, lo+2*(n+1) ≤ i → i ≤ hi → b i (A+(n+1)) = false := by
  intro n
  induction n with
  | zero =>
    intro i hlo hhi
    rw [show A+(0+1)=A+1 by omega, rec_at h i A (by omega),
      hb (i-2) (by omega) (by omega), hb (i-1) (by omega) (by omega), hb i (by omega) hhi]
    rfl
  | succ n ih =>
    intro i hlo hhi
    rw [show A+(n+1+1)=(A+(n+1))+1 by omega, rec_at h i (A+(n+1)) (by omega),
      ih (i-2) (by omega) (by omega), ih (i-1) (by omega) (by omega), ih i (by omega) hhi]
    rfl

/-- Across a black interval, the leftmost two clocks propagate unchanged.
The observed black phases give resets; uniform longer clocks justify moving
the inherited period back to the common onset. -/
theorem black_interval_period {b : Nat → Nat → Bool} (h : Recurrence b)
    (a B A : Nat) (haB : a+1 ≤ B) (hA : 2^B-1 ≤ A)
    (hb : ∀ i, a+1 ≤ i → i ≤ B → b i A = true) :
    PeriodFrom (b B) (2^B-1) (2^(a+1)) := by
  have up : ∀ i, i ≤ B → PeriodFrom (b i) (2^B-1) (2^i) := by
    intro i hi
    exact period_mono (uniform_period h i)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) hi) 1)
  have base0 : PeriodFrom (b a) (2^B-1) (2^(a+1)) := by
    rw [show 2^(a+1)=2*2^a by rw [Nat.pow_succ]; omega]
    exact period_double (up a (by omega))
  have base1 := up (a+1) haB
  have pairs : ∀ k, a+k+1 ≤ B →
      PeriodFrom (b (a+k)) (2^B-1) (2^(a+1)) ∧
      PeriodFrom (b (a+k+1)) (2^B-1) (2^(a+1)) := by
    intro k
    induction k with
    | zero => intro _; simpa using And.intro base0 base1
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      have hn := reset_inherits (x := b (a+k+2)) (l := b (a+k)) (g := b (a+k+1))
        (fun t => h.2.2 (a+k) t) hp.1 hp.2 (up (a+k+2) (by omega))
        (Nat.two_pow_pos _) hA (hb (a+k+1) (by omega) (by omega))
      simpa [Nat.add_assoc] using And.intro hp.2 hn
  have hh := (pairs (B-a-1) (by omega)).2
  simpa [show a+(B-a-1)+1=B by omega] using hh

/-- Uniform arbitrary-interval obstruction. Starting at index a+1 avoids
special negative-boundary notation. Equivalently, for lo>=1 the right endpoint
is lo+2^(lo+1), and the onset is 2^endpoint-1. -/
theorem no_aged_black_interval {b : Nat → Nat → Bool} (h : Recurrence b)
    (a A : Nat) (hA : 2^(a+1+2^(a+2))-1 ≤ A) :
    ¬ (∀ i, a+1 ≤ i → i ≤ a+1+2^(a+2) → b i A = true) := by
  intro hb
  let B := a+1+2^(a+2)
  let P := 2^(a+1)
  have hP : 0 < P := Nat.two_pow_pos _
  have hB : B = a+1+2*P := by
    dsimp [B, P]
    rw [show a+2=(a+1)+1 by omega, Nat.pow_succ]
    omega
  have hp := black_interval_period h a B A (by omega) hA hb
  have he := black_erodes h hb (P-1) B (by omega) (Nat.le_refl _)
  rw [show P-1+1=P by omega] at he
  have hper := hp A hA
  change b B (A+P) = b B A at hper
  rw [he, hb B (by omega) (Nat.le_refl _)] at hper
  cases hper

theorem aged_white_witness {b : Nat → Nat → Bool} (h : Recurrence b)
    (a A : Nat) (hA : 2^(a+1+2^(a+2))-1 ≤ A) :
    ∃ i, a+1 ≤ i ∧ i ≤ a+1+2^(a+2) ∧ b i A = false := by
  classical
  apply Classical.byContradiction
  intro hn
  apply no_aged_black_interval h a A hA
  intro i hi hj
  cases hc : b i A
  · exact (hn ⟨i,hi,hj,hc⟩).elim
  · rfl

end FrontBlackInterval
