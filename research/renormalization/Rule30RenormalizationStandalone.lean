import Ruliology.CellularAutomata.Rule30ZeroBoundary
import Ruliology.CellularAutomata.Rule30Prize

open Ruliology.CellularAutomata

/-!
# An eight-column reconstruction identity and the condition needed to iterate it

The boundary history is `!G 0, 1, !G 1, 1, ...`. If the black gate
positions have spacing at least three, shifting reconstruction eight columns
left replaces `G r` by `G (r+2) xor G (r+4)`. This condition is not asserted
to hold after that replacement, or for every driven right half.
-/



namespace Rule30Submission.Spacing

open Rule30ZeroBoundary

def boundary (G : Nat → Bool) (t : Nat) : Bool :=
  if t % 2 = 0 then !G (t / 2) else true

def transform (G : Nat → Bool) (r : Nat) : Bool := xor (G (r+2)) (G (r+4))

def Spaced (G : Nat → Bool) : Prop :=
  ∀ r, (G r && G (r+1)) = false ∧ (G r && G (r+2)) = false

/-- The even/odd pair of a reconstructed column. -/
def pair (G : Nat → Bool) : Nat → Nat → Bool × Bool
  | 0, _ => (false, false)
  | 1, r => (!G r, true)
  | k+2, r =>
      (xor (pair G (k+1) r).2 ((pair G (k+1) r).1 || (pair G k r).1),
       xor (pair G (k+1) (r+1)).1 ((pair G (k+1) r).2 || (pair G k r).2))

theorem boundary_even (G : Nat → Bool) (r : Nat) : boundary G (2*r) = !G r := by
  simp [boundary, show 2*r % 2 = 0 by omega,
    show 2*r / 2 = r by omega]

theorem boundary_odd (G : Nat → Bool) (r : Nat) : boundary G (2*r+1) = true := by
  simp [boundary]

/-- The pair recurrence is exactly the kit's scalar reconstruction. -/
theorem pair_recon (G : Nat → Bool) : ∀ k r,
    pair G k r = (recon (boundary G) k (2*r), recon (boundary G) k (2*r+1))
  | 0, r => rfl
  | 1, r => by simp [pair, recon, boundary_even, boundary_odd]
  | k+2, r => by
      rw [pair, pair_recon G (k+1) r, pair_recon G (k+1) (r+1), pair_recon G k r]
      simp only [recon_two, show 2*r+1+1 = 2*(r+1) by omega]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ninth_pair (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 9 r = pair (transform G) 1 r := by
  have h0 := h r
  have h1 := h (r+1)
  have h2 := h (r+2)
  have h3 := h (r+3)
  simp only [Nat.add_assoc] at h1 h2 h3
  simp only [pair, transform, Nat.add_assoc]
  cases ha : G r <;> cases hb : G (r+1) <;> cases hc : G (r+2) <;>
    cases hd : G (r+3) <;> cases he : G (r+4) <;> simp_all

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tenth_pair (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 10 r = pair (transform G) 2 r := by
  have h0 := h r
  have h1 := h (r+1)
  have h2 := h (r+2)
  have h3 := h (r+3)
  have h4 := h (r+4)
  simp only [Nat.add_assoc] at h1 h2 h3 h4
  simp only [pair, transform, Nat.add_assoc]
  cases ha : G r <;> cases hb : G (r+1) <;> cases hc : G (r+2) <;>
    cases hd : G (r+3) <;> cases he : G (r+4) <;> cases hf : G (r+5) <;> simp_all

/-- An exact eight-column translation, with an explicit spacing premise. -/
theorem pair_translate (G : Nat → Bool) (h : Spaced G) : ∀ m r,
    pair G (m+9) r = pair (transform G) (m+1) r := by
  have key : ∀ m, (∀ r, pair G (m+9) r = pair (transform G) (m+1) r) ∧
      (∀ r, pair G (m+10) r = pair (transform G) (m+2) r) := by
    intro m
    induction m with
    | zero => exact ⟨ninth_pair G h, tenth_pair G h⟩
    | succ m ih =>
        refine ⟨ih.2, fun r => ?_⟩
        change
          (xor (pair G (m+10) r).2 ((pair G (m+10) r).1 || (pair G (m+9) r).1),
           xor (pair G (m+10) (r+1)).1 ((pair G (m+10) r).2 || (pair G (m+9) r).2)) =
          (xor (pair (transform G) (m+2) r).2
             ((pair (transform G) (m+2) r).1 || (pair (transform G) (m+1) r).1),
           xor (pair (transform G) (m+2) (r+1)).1
             ((pair (transform G) (m+2) r).2 || (pair (transform G) (m+1) r).2))
        rw [ih.2 r, ih.2 (r+1), ih.1 r]
  exact fun m => (key m).1

/-- The scalar statement holds at every time, not only at time zero. -/
theorem reconstruction_translate (G : Nat → Bool) (h : Spaced G) (m t : Nat) :
    recon (boundary G) (m+9) t = recon (boundary (transform G)) (m+1) t := by
  have hp := pair_translate G h m (t/2)
  rw [pair_recon, pair_recon] at hp
  rcases Nat.mod_two_eq_zero_or_one t with ht | ht
  · have he : t = 2*(t/2) := by omega
    rw [he]
    exact congrArg Prod.fst hp
  · have he : t = 2*(t/2)+1 := by omega
    rw [he]
    exact congrArg Prod.snd hp

/-- An explicit support bound drops by eight under the translation. -/
theorem support_transfer (G : Nat → Bool) (h : Spaced G) (W : Nat)
    (hW : ∀ k, W < k → lam (boundary G) k = false) :
    ∀ k, W-8 < k → lam (boundary (transform G)) k = false := by
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m+1 := ⟨k-1, by omega⟩
  unfold lam
  rw [← reconstruction_translate G h]
  exact hW _ (by omega)

/-- A finite reconstructed initial row remains finite after the translation. -/
theorem finite_transfer (G : Nat → Bool) (h : Spaced G)
    (hf : FinSupp (lam (boundary G))) : FinSupp (lam (boundary (transform G))) := by
  obtain ⟨W, hW⟩ := hf
  exact ⟨W-8, support_transfer G h W hW⟩

/-- The spacing premise survives one transform exactly for gates white beyond
index three. Thus an infinite gate cannot support a second application. -/
theorem transform_spaced_iff (G : Nat → Bool) (h : Spaced G) :
    Spaced (transform G) ↔ ∀ r, G (r+4) = false := by
  constructor
  · intro ht r
    have ha := (h (r+2)).2
    have hb := (h (r+4)).2
    have hc := (ht r).2
    simp only [transform, Nat.add_assoc] at hc ha hb
    cases h2 : G (r+2) <;> cases h4 : G (r+4) <;> cases h6 : G (r+6) <;> simp_all
  · intro hz
    have he : transform G = fun r => G (r+2) := by
      funext r
      simp [transform, hz r]
    rw [he]
    intro r
    simpa only [Nat.add_assoc] using h (r+2)

/-- Spacing is not preserved: a period-five gate supplies a counterexample. -/
def periodFive (r : Nat) : Bool := r % 5 == 0

theorem periodFive_spaced : Spaced periodFive := by
  intro r
  have hr := Nat.mod_lt r (by decide : 0 < 5)
  have h1 : (r+1)%5 = (r%5+1)%5 := by omega
  have h2 : (r+2)%5 = (r%5+2)%5 := by omega
  simp only [periodFive]
  rw [h1, h2]
  have hs : r%5=0 ∨ r%5=1 ∨ r%5=2 ∨ r%5=3 ∨ r%5=4 := by omega
  rcases hs with hh | hh | hh | hh | hh <;> rw [hh] <;> decide

theorem transform_not_spaced : ¬ Spaced (transform periodFive) := by
  intro h
  have hh := (h 1).2
  change true = false at hh
  exact Bool.noConfusion hh

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Dropping the spacing premise for the second step gives a false identity,
already at depth seventeen and time zero for the period-five gate. -/
theorem second_translation_fails :
    recon (boundary periodFive) 17 0 ≠
      recon (boundary (transform (transform periodFive))) 1 0 := by
  decide

end Rule30Submission.Spacing

/-!
# Finite packed checks of the scalar sideways reconstruction

Each natural number holds a column's successive times in its bits. A right
shift reads the next time, so the packed update is the scalar inverse rule.
The soundness bound explicitly excludes the unrepresented future boundary.
-/



namespace Rule30Submission.Packed

open Rule30ZeroBoundary Rule30Submission.Spacing

noncomputable def advance : Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat × Nat)
    (fun a b => (a,b))
    (fun _ ih a b => ih b (Nat.xor (Nat.shiftRight b 1) (Nat.lor b a)))

theorem advance_zero (a b : Nat) : advance 0 a b = (a,b) := rfl

theorem advance_succ (k a b : Nat) :
    advance (k+1) a b = advance k b ((b >>> 1) ^^^ (b ||| a)) := rfl

theorem advance_last : ∀ k a b,
    advance (k+1) a b =
      ((advance k a b).2,
       ((advance k a b).2 >>> 1) ^^^ ((advance k a b).2 ||| (advance k a b).1))
  | 0,a,b => rfl
  | k+1,a,b => by
      rw [advance_succ, advance_succ k a b, advance_last]

noncomputable def packedRun (B k : Nat) : Nat × Nat := advance k 0 B

theorem packedRun_zero (B : Nat) : packedRun B 0 = (0,B) := rfl

theorem packedRun_succ (B k : Nat) :
    packedRun B (k+1) =
      ((packedRun B k).2,
       ((packedRun B k).2 >>> 1) ^^^ ((packedRun B k).2 ||| (packedRun B k).1)) :=
  advance_last k 0 B

/-- Every checked bit agrees with scalar reconstruction inside its finite cone. -/
theorem packed_sound (B H : Nat) (b : Nat → Bool)
    (hb : ∀ t, t < H → B.testBit t = b t) : ∀ k t, t+k < H →
    (packedRun B k).1.testBit t = recon b k t ∧
    (packedRun B k).2.testBit t = recon b (k+1) t := by
  intro k
  induction k with
  | zero =>
      intro t ht
      exact ⟨by simp [packedRun_zero, recon], hb t ht⟩
  | succ k ih =>
      intro t ht
      have h0 := ih t (by omega)
      have h1 := ih (t+1) (by omega)
      rw [packedRun_succ]
      refine ⟨h0.2, ?_⟩
      simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight]
      rw [show 1+t=t+1 by omega, h1.2, h0.2, h0.1]
      exact (recon_two b k t).symm

end Rule30Submission.Packed

/-!
# A spacing-three/five gate with seventeen white initial cells

The gate is globally periodic of period 31, with gaps 3,3,3,3,3,3,3,5,5.
Its reconstructed initial row is white at depths 528 through 544. A finite
packed cone is proved equal to the kit's scalar reconstruction. There is no
claim that this gate is realized by a finite driven right half.
-/



namespace Rule30Submission.Gap

open Rule30ZeroBoundary Rule30Submission.Spacing
open Rule30Submission.Packed

def gate31 (r : Nat) : Bool := decide (r%31 ∈ [0,3,6,9,12,15,18,21,26])

def Next35 (G : Nat → Bool) (r : Nat) : Prop :=
  G (r+1) = false ∧ G (r+2) = false ∧
    (G (r+3) = true ∨ (G (r+3) = false ∧ G (r+4) = false ∧ G (r+5) = true))

theorem gate31_periodic (r : Nat) : gate31 (r+31) = gate31 r := by
  simp [gate31]

theorem gate31_residues : ∀ r : Fin 31, gate31 r = true → Next35 gate31 r := by
  unfold Next35
  decide

/-- Every black gate cell is followed by a gap of exactly three or five. -/
theorem gate31_gaps (r : Nat) (hr : gate31 r = true) : Next35 gate31 r := by
  have h := gate31_residues ⟨r%31, Nat.mod_lt r (by decide)⟩
  simp only [Next35, gate31, Nat.add_mod, Nat.mod_mod] at h hr ⊢
  exact h hr

theorem gate31_spaced : Spaced gate31 := by
  intro r
  cases hr : gate31 r with
  | false => simp
  | true =>
      have h := gate31_gaps r hr
      simp only [Next35] at h
      simp [h.1, h.2.1]

-- The finite boundary prefix is generated and cross-checked by the companion
-- Python experiment. Its bits are rechecked below by the ordinary kernel.
def boundaryPrefix : Nat := 114258128115382768325149165979858622949054058922182384017825772718783752107996860734084690853574210578405379476224683606690194761257884644651583470255712858309128126

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem boundary_bits : ∀ t : Fin 545,
    boundaryPrefix.testBit t = boundary gate31 t := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem window_check : ∀ j : Fin 17,
    (packedRun boundaryPrefix (528+j.val)).1.testBit 0 = false := by
  decide

/-- The seventeen white cells belong to the actual scalar reconstruction. -/
theorem seventeen_white (j : Nat) (hj : j < 17) :
    recon (boundary gate31) (528+j) 0 = false := by
  have h := (packed_sound boundaryPrefix 545 (boundary gate31)
    (fun t ht => boundary_bits ⟨t,ht⟩) (528+j) 0 (by omega)).1
  exact h.symm.trans (window_check ⟨j,hj⟩)

/-- Spacing-three/five gates do not force a black initial cell in every
seventeen-cell interval, even when the gate itself is periodic. -/
theorem no_uniform_gap_bound_sixteen :
    ¬ (∀ G : Nat → Bool, (∀ r, G r = true → Next35 G r) →
      ∀ n, 1 ≤ n → ∃ j, j ≤ 16 ∧ recon (boundary G) (n+j) 0 = true) := by
  intro h
  obtain ⟨j, hj, hb⟩ := h gate31 gate31_gaps 528 (by decide)
  rw [seventeen_white j (by omega)] at hb
  exact Bool.noConfusion hb

end Rule30Submission.Gap
