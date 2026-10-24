import Ruliology.CellularAutomata.Rule30ZeroBoundary
import Ruliology.CellularAutomata.Rule30Prize

import Ruliology.CellularAutomata.Rule30PeriodTwoSideways

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

/-!
# Packed prefixes of the alternating-driven right half

The packed update represents spatial cells at positions 1,2,..., in low to
high bits. The prefix agreement lemmas retain the exact dependence on the
unrepresented tail. No finite-prefix observation is assumed to be invariant.
-/



namespace Rule30Submission.Driven

open Rule30Jen Rule30Ether Rule30PeriodTwoCoupled Rule30PeriodTwoSideways

def step (b : Bool) (a : Nat) : Nat :=
  ((a <<< 1) ||| b.toNat) ^^^ (a ||| (a >>> 1))

theorem step_bit (b : Bool) (a j : Nat) :
    (step b a).testBit j = xor (if j=0 then b else a.testBit (j-1))
      (a.testBit j || a.testBit (j+1)) := by
  simp only [step,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight,Nat.testBit_bool_toNat]
  cases j <;> simp [Nat.add_comm]

theorem step_agree (b : Bool) {a c k : Nat}
    (h : ∀ j, j<k+1 → a.testBit j=c.testBit j) :
    ∀ j, j<k → (step b a).testBit j=(step b c).testBit j := by
  intro j hj
  rw [step_bit,step_bit,h j (by omega),h (j+1) (by omega)]
  by_cases h0 : j=0
  · simp [h0]
  · simp [h0,h (j-1) (by omega)]

def packed (c : Nat → Bool) (a : Nat) : Nat → Nat
  | 0 => a
  | t+1 => step (c t) (packed c a t)

theorem packed_sound (c R : Nat → Bool) (a : Nat)
    (ha : ∀ j, a.testBit j=R (j+1)) : ∀ t j,
    (packed c a t).testBit j=drv c R t (j+1) := by
  intro t
  induction t with
  | zero => intro j; simpa [packed,drv] using ha j
  | succ t ih =>
      intro j
      rw [packed,step_bit]
      cases j with
      | zero => simp [drv,rule,ih,drv_col0]
      | succ j => simp [drv,rule,ih,Nat.add_assoc]

def double (a : Nat) : Nat := step true (step false a)

def white : Nat → Nat
  | 0 => 1
  | n+1 => double (white n)

theorem packed_white : ∀ n, packed altCol 0 (2*n+1)=white n
  | 0 => by decide
  | n+1 => by
      rw [show 2*(n+1)+1=(2*n+1+1)+1 by omega,packed,packed]
      rw [show 2*n+1+1=2*(n+1) by omega,altCol_even,altCol_odd,packed_white]
      rfl

theorem white_sound (n j : Nat) :
    (white n).testBit j=drv altCol empty (2*n+1) (j+1) := by
  rw [← packed_white]
  exact packed_sound altCol empty 0 (by intro j; simp [empty]) (2*n+1) j

theorem white_gate (n : Nat) : (white n).testBit 0=u empty n := white_sound n 0

theorem double_agree {a c k : Nat}
    (h : ∀ j, j<k+2 → a.testBit j=c.testBit j) :
    ∀ j, j<k → (double a).testBit j=(double c).testBit j := by
  exact step_agree true (step_agree false (by intro j hj; exact h j (by omega)))

def iterate (a : Nat) : Nat → Nat
  | 0 => a
  | n+1 => double (iterate a n)

theorem iterate_agree : ∀ n {a c k : Nat},
    (∀ j, j<k+2*n → a.testBit j=c.testBit j) →
    ∀ j, j<k → (iterate a n).testBit j=(iterate c n).testBit j
  | 0,a,c,k,h => by simpa [iterate] using h
  | n+1,a,c,k,h => by
      apply double_agree
      apply iterate_agree n
      intro j hj
      exact h j (by omega)

theorem iterate_white (r n : Nat) : iterate (white r) n=white (r+n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate,ih,show r+(n+1)=(r+n)+1 by omega,white]

theorem double_prefix (a k : Nat) : double a % 2^k=double (a % 2^(k+2)) % 2^k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow]
  by_cases hj : j<k
  · simp only [hj,decide_true,Bool.true_and]
    apply double_agree (k:=k)
    · intro i hi
      rw [Nat.testBit_mod_two_pow]
      simp [hi]
    · exact hj
  · simp [hj]

theorem iterate_mod_bit (a k n j : Nat) (hj : j+2*n<k) :
    (iterate (a % 2^k) n).testBit j=(iterate a n).testBit j := by
  apply iterate_agree n (k:=j+1)
  · intro i hi
    rw [Nat.testBit_mod_two_pow]
    simp [show i<k by omega]
  · omega

/-- The local gate window needed for exact spacings three or five. -/
def Window (f : Nat → Bool) (r : Nat) : Prop :=
  (f r && f (r+1))=false ∧ (f r && f (r+2))=false ∧
  (f r=true →
    (f (r+3)=true ∧ f (r+4)=false ∧ f (r+5)=false) ∨
    (f (r+3)=false ∧ f (r+4)=false ∧ f (r+5)=true)) ∧
  (f r || f (r+1) || f (r+2) || f (r+3) || f (r+4) || f (r+5))=true

instance (f : Nat → Bool) (r : Nat) : Decidable (Window f r) := inferInstanceAs
  (Decidable ((f r && f (r+1))=false ∧ (f r && f (r+2))=false ∧
  (f r=true →
    (f (r+3)=true ∧ f (r+4)=false ∧ f (r+5)=false) ∨
    (f (r+3)=false ∧ f (r+4)=false ∧ f (r+5)=true)) ∧
  (f r || f (r+1) || f (r+2) || f (r+3) || f (r+4) || f (r+5))=true))

def Observe (a : Nat) : Prop := Window (fun n => (iterate a n).testBit 0) 0

instance (a : Nat) : Decidable (Observe a) := inferInstanceAs
  (Decidable (Window (fun n => (iterate a n).testBit 0) 0))

theorem observe_trim (a : Nat) : Observe (a % 2^18) ↔ Observe a := by
  simp only [Observe,Window,Nat.zero_add]
  rw [iterate_mod_bit a 18 0 0 (by decide),iterate_mod_bit a 18 1 0 (by decide),
    iterate_mod_bit a 18 2 0 (by decide),iterate_mod_bit a 18 3 0 (by decide),
    iterate_mod_bit a 18 4 0 (by decide),iterate_mod_bit a 18 5 0 (by decide)]

end Rule30Submission.Driven

/-! Untrusted generated wall data; every membership, observation and
transition case is checked below by ordinary kernel reduction. -/



namespace Rule30Submission.DrivenWall

open Rule30Submission.Driven

def wallMask : Nat := 0x94c0051014c00840008005900580c0400100048014c08044544010400540810004c00080154088400480159010c040441900059051c00c4414c005000400050010c005004140c84081c0159010c0c0448100048014c0814451c005c0058004808080149004c0c044810005901580c004008015905440c4001400058000c0404001c0158011808844014005800580c0400100149014c0c1005440144015c0800005c001c0154088448480159010c040448100059011c0804014c004001440850005400110110048448480059014404044810011005080844050c015d005c000808100049054c08144190005900500c8048180158054c0c40041c005900540c4049400058014c0884405801590158040440580051014c0840054c014401540804005c0011015c0884480800590148040448100059051c0084014c005000400050010c005004140c84081c0159010c0c8448100048014c0814451c005c00580048081001100508084400100059005c0c0448d801590544044401180058001c045401080050004c0484080c015801080c8440100048014c0814451c005c005c00400154001505100484484801590004048440980159051c0844014c0050014c0050005c001c0154088448480159010c040448080149014c0c14411c01510058001040100149014c0c10001c01590148040440140058054c084441180059015c0c5001540051054c0c844848015900480c8000100048014c08044554014401500c4c004c0140010c0884005800590148040441900059051c00c4414c005000400050010c0051001c0484001c005801080c0408100048014c0814451c01580058001008080149004408140890005900580c844048015905440c4001540058001c0c04005c0158051808844054005800580c4400180149014c0c9045440144015c0800005c001d0154088448480159010c040448100059011c0804054c0040014408500154001505100484484801590004048448100141054c0814451c01540154084000100048014c08044810005900500c80480c0158055c0880004c0059005c08004154015800440c8448d4005900580c4400180141054c0c4005040144005c0c48015c01480148088408080059010c040448100059014c0804404c005401440050010c0050005c048408500058010c0cc408100048014c0804451c005c005c000008180110014c081448100159015c040040480159054c0c4405180058001c0454410c0051045c0c84481c0159010c0c8448100049054c0814455c005c005c0048005400110118048448d801590144048441900059054c0cc405480145011c0050015c0015015c0884481c00590148040440100049014c0844451c0158005c001801580051014c0c4000480159014c0c04405c015905540844014c0059005c0054015c0150054c0484085c005900580c0408100049054c081445440004015c08440154000801480884401c0059010c0c0448100059051c00c4414c005000400050010c005101140c84489c0158010c0c0400100048014c0844451c01580058001048080149054c0c044810005901580c004848015905440c4001540158001c0c04001c00580508088440c4005900580c4400500140014c08000544014401540814004c00180154088400480159010c040448900059015c08844044005001440850015400110118008408cc0159014c040448180151051c0844414c005c005c001048100048014c08144190005900500c80481c0159054c0c000414005900540c4049400058014c0884405c01590158040441580051014c0c40054c014401540854015c0015015c0884481c00590148040448900059051c0084414c005500440050010c0051045c0c84481c0159010c0c8448100049054c0814455c005c005c0048081001100548084401900059015c0c4448d801590544044401180158001c0454010c0050005c048408500058010c0cc408100048014c0804451c005c005c0000005400110518048440480159014c0c044810015905140c44414c005001140850015c01480148088408080059010c040448100149004c0844414c00510058001040180141054c0c40009c00590148040048d40059054c081440440059015c045448480050014c088448cc0159004c0c0400500051054c0c000544010401540854014c0011054c0804001801590148040440000059051c0084414c005400400050010c0051041c0c8448180158010c0c8448100049054c0814451c005c005c0048081001100508084400900059015c0c40484800590544044401100058001c0454015401580044088440c4005900580c4408580151054c0c0005440144005c0844005400080140088440080159010c040448100059010c0804004c004001440850005400110110048440080059010c040448100110014c0804451c015d0050001008100048014c08144190005900500c8048100058014c0800001c015900540800481c0158011808844014005800580c0400100149014c0c1005440144015c0c10005c001c0154088448480159010c040448100059011c0804014c00400144085001080050004c0484080c015801080c8440100048014c0814451c005c005c004008100140014c08044098015901580c80484801590544044005100059001c0454010c0051004c0484001c0058010c0c0400100049014c0804451c015800580010004c01000154088400480159014c0c0448100059055c08844044015001440850014c0148010c0884005800590148040448100048014c0814451c005c0058004800100048014c080448d80159014404044008005905080844055c0059015c0054495c0050014c0c84401c015900580c4400100048054c0844454c0144015c0804005c001c0154088448480159010c040448100059051c00c4414c005000480050010c0051041c0c8448180158010c0c8448100049054c0814451c005c005c004808100149004c08444810005900580c044808005905440c4001480158014c0c04005c0158051c0c844844005800580c0400580148054c0c000544014400540c10004c01000154088400480159014c0c0448100059055c08844554015501440850005400110118048448d80159014404844810011005480844054c015d005c000808100049054c08144190005900500c84481c0159055c0c40045c005900540c4049400058054c0884484801590058040440500051054c0c000544010401540854004c0011051c0884004801590148040448100059051c0084014c005000400050010c0050045c0c84081c0159010c0c0448100048014c0814455c005c0058004808180151051c084440100059005c0c0448cc015905540c4401180059001c045401080051015c0484080c015800080c8401180048014c0804451c005d005c0040415c0015051804844858015901040c84411c0159055c0844054c0054014c0050005c001d0154088448480159010c040448080149054c0c04411c01510058001000180149014c0c90401801590148040440540058014c084445180059015c0c5401540151055c0c844848015900480c8000100048015c0804455c014401540c4c014c0148010c088400d801590148040449d00059051c00c4414c015000480050011c0051005c0484081c0058010c0c0408100049054c0814451c01580058001008080149004c08140890005901580c8440480159054c0c4441540158011c0c04485c015905180c844054005800580c4400180149014c0c9045440144015c0c10005c001d0554088448c80159010c0c0448100059015c0844054c0040014408500154001505100484484c0159000c048448100149054c0814451c01540154084800100048014c08144810005900500c80485c0158055c0880004c0059005c081041540158005c0c8448d40059015c0cc408580151055c0c4005440144005c0c440154000801480884401c0159014c0c0448100059014c0884445c014c0144085001080051001c048408900158010c0c8408100048014c0814451c005c0058004c08100111014c080448900159015c0c444848015905440c4005140058001c0454410c0051041c0c8448180158010c0c8448100049054c0814451c005c005c00480154001501100484484c00590144040440980159050c0cc4051c0044015c0850015c0011055c0c04481c015901480c0441100049054c0854451c01590058000c00500051054c0cc008480159010c040448cc0159014c0c14414c0059005c085409580155055c0c84401c00590148080401180048014c080445440144015c084c014c0148010c0c84485c00590148040441900059055c00c4454c015000480050010c0051004c0484409c0158010c0c4400100049014c0844451c0158005c001808180140055408440810005900580c8440480159054c0c4401540158010c0c04481c0158011808844014005800580c0400100149014c0c1005440144015c0c10005c001c0154088448480159010c040448100059011c0804014c0040014408500154001505100484484801590004048448100140014c0804451c01540154084800100048014c08144810005900500c80480c0158055c0800004c00590054080048580050014c088448cc0159004c0c4401580151055c0c000544010401540854014c0011054c0884001801590148040440000059051c0084414c005400400050010c0051045c0c8448180158010c0c8448100049054c0814451c005c005c0048081001100548084401900059015c0c4448c801590544044401100058001c0454010c0050001c04840850005801080c8408100049054c0814451c005c005c0048015400150110048440080059010c040448100059051c08c4014c0050011c0850005c001c0154088448480159010c040448080149014c0c04411c01510058001008580151054c0c00005800590148040440c40059014c081440440059015c045449400058014c088440dc01590158040441580051014c0c40054c014401540854015c0015015c0884481c00590148040448900059051c0084414c005500440050010c0051045c0c84481c0159010c0c8448100049054c0c14455c005c015c0048481801100548085401d40059015c0c4448d80159054c044401180158001c045401540158004c0c8448d4005900580c4401180141055c0c4005040144005c0c48015c01480148088408480159010c040448900059014c0884405c005401440050005400110518048440480159014c0c0448180119054c0814455c0155015c041008100048014c08044810005900500c8048500058054c0cc0005c015900540c00401c00580548088448d4005900580c4400500140014c0c000544014401540814004c00180154088400480159010c040448900059015c08844044005001440850010c005004140c84089c0159010c0c0448100048014c0814451c005c0058004c08180151051c084448100059005c0c0448cc015905540c4405180058001c0454010c005101140c84489c0158010c0c0400100048014c0844451c015800580010405c001d0154088448480159010c040448100059011c0804054c0040014408500154000801480884401c0059010c0c0440100048014c0804451c005d005c004008100049054c08144848015900040484485c0059054c0814454c0159015c0c54495c0050014c0084001c005900580c0400100048014c08444544010401540804004c00080154088440480159010c040448100059051c00c4414c005000400050010c0051041c0c8448180158010c0c8448100049054c0814451c005c005c004808100149004c08444810005900580c044008005905440c4001480158000c0404001c0158011c08844804005800580c0400100148014c0c000544014400540c10004c00000154088400480159010c040448100059011c08040144004001440850005400110110048448480059014404044810011005080844050c015d005c000808100049054c08144190005900500c8048180158055c0c40041c005900540c4049400058054c0884484801590058040440500051014c08000544010401540804004c0011011c0884004801590148040448100059051c0084014c005000400050010c005004140c84081c0159010c0c0448100048014c0814451c005c0058004808180151051c084440100059005c0c0448cc015905540c4401180058001c045401080051004c0484080c015800080c8400100048014c0804451c005d005c00400154001505100484484801590004048441180159051c0844054c0050014c0050005c001d0154088448480159010c040448080149054c0c04411c01510058001000180149014c0c90401801590148040440540058014c084445180059015c0c5401540051054c0c844848015900480c8000100048014c08044554014401500c4c004c0140010c0884005800590148040441900059051c00c4414c005000400050010c0051001c0484001c005801080c0408100048014c0814451c01580058001008080149004408140890005900580c844048015905440c4001540058001c0c04005c0158051808844054005800580c4400180149014c0c9045440144015c0800005c001d0154088448480159010c040448100059011c0804054c0040014408500154001505100484484801590004048448100141054c0814451c01540154084000100048014c08044810005900500c80480c0158055c0880004c0059005c08004154015800440c8448d4005900580c4400180141054c0c4005040144005c0c40015400080148088400080059010c040448100059014c0804404c00440144005001080050001c048408100058010c0c8408100048014c0804451c005c0058000008100110014c080448100159015c04004048015905440c4005100058001c0454410c0051041c0c8448180158010c0c8448100049054c0814451c005c005c00480054001101100484484800590144040440900059050c0cc405080044011c0050015c0011015c0804481c00590148040440100049014c0844451c01580058000800500051014c0c4000480159010c0404404c015901440804014c0059005c0054015c0150054c0484085c005900580c0408100049054c081445440004015c08440154000801480884401c0059010c0c0448100059051c00c4414c005000400050010c005101140c84489c0158010c0c0400100048014c0844451c01580058001048080149054c0c044810005901580c004848015905440c4001540158001c0c04001c00580548088448d4005900580c4400500140014c0c000544014401540814004c00180154088400480159010c040448900059015c08844044005001440850015400110518008408cc0159014c040448180151051c0844414c005c005c001048100048014c081449d0005900500c80489c0159054c0c000414015900540c4049400058014c088440dc01590158040441580051014c0c40054c014401540854015c0015015c0884481c00590148040448900059051c0084414c005500440050010c0051045c0c84481c0159010c0c8448100049054c0c14455c005c015c0048481801100548085401d40059015c0c4448d80159054c044401180158001c0454010c0050005c048408500058010c0cc408100048014c0804451c005c005c0000005400110518048440480159014c0c0448140159055c0c44454c015001140850015c01480148088408480159010c040448100149005c0844414c00590058001841180141055c0c40009c00590148040048d40059054c0814404c0059015c045448580050014c088448cc0159004c0c4401580151055c0c000544010401540854014c0011054c0884001801590148040440000059051c0084414c005400400050010c0051045c0c8448180158010c0c8448100049054c0814451c005c005c0048081001100548084401900059015c0c4448c801590544044401100058001c0454015401580044088440c4005900580c4408580151054c0c0005440144005c0844005c001c0154088448480159010c040448100059011c0804014c004001440850015400150110048440080059010c040448180110014c0804451c015d0054001008100049054c08144190005900500c8048500058014c0800001c015900540c00481c0158011808844014005800580c0400100149014c0c1005440144015c0c10005c001c0154088448480159010c040448100059011c0804014c00400144085001080050004c0484080c015801080c8440100048014c0814451c005c005c004008100140014c08044098015901580c80484801590544044005100059001c0454010c0051004c0484409c0158010c0c4400100049014c0844451c0158005c0018004c01000154088400480159014c0c0448100059055c08844554015501440850014c0148010c0c84485c00590148040448100049054c0814455c005c005c004801180048014c080448d8015901440484401c005905480844055c0059015c0854415c0150054c0484085c005900580c0408100049054c081445440004015c08440154000801480884401c0059010c0c0448100059051c00c4414c005000400050010c005101140c84489c0158010c0c0400100048014c0844451c01580058001048080149054c0c044810005901580c004848015905440c4001540158001c0c04001c00580508088440c4005900580c4400500140014c08000544014401540814004c00180154088400480159010c040448900059015c08844044005001440850015400110118008408cc0159014c040448180151051c0844414c005c005c001048100048014c08144190005900500c80481c0159054c0c000414005900540c4049400058014c0884405c01590158040441580051014c0c40054c014401540854015c0015015c0884481c00590148040448900059051c0084414c005500440050010c0051045c0c84481c0159010c0c8448100049054c0814455c005c005c0048081001100548084401900059015c0c4448d801590544044401180158001c0454010c0050005c048408500058010c0cc408100048014c0804451c005c005c0000005400110518048440480159014c0c044810015905140c44414c005001140850015c01480148088408080059010c040448100149004c0844414c00510058001040180141054c0c40009c00590148040048d40059054c081440440059015c045441500151055c0c84400800590048080000100048014c0804454401440154084c014c0148010c0884005800590148040441900059051c00c4414c015000480050010c0051004c0484001c0058010c0c0400100049014c0804451c01580058001008080140004408040810005900580c8440480159054c0c4401540158010c0c04481c0158011808844014005800580c0400100149014c0c1005440144015c0c10005c001c0154088448480159010c040448100059011c0804014c0040014408500154001505100484484801590004048448100140014c0804451c01540154084800100048014c08144810005900500c80480c0158055c0800004c005900540800415401580044088440c4005900580c4408580151054c0c0005440144005c0844005400080140088440080159010c040448100059010c0804004c00400144085001080050001c04840810005801080c8408100048014c0814451c005c0058004808100110014c08044810005901580c004008005905440c4001100058001c0454010c0051041c0c8448180158010c0c8448100049054c0814451c005c005c00480054001101100484484800590144040440900059050c0cc405080044011c0050014c0011054c0804001801590148040440100048014c0844451c01580058000000500051054c0c0008480159010c040448cc0159014c0c04414c0059005c085401540051054c0c844848015900480c8000100048014c08044554014401500c4c004c0140010c0884005800590148040441900059051c00c4414c005000400050010c0051001c0484001c005801080c0408100048014c0814451c01580058001008080149004408140890005900580c844048015905440c4001540058001c0c04005c0158051808844054005800580c4400180149014c0c9045440144015c0800005c001d0154088448480159010c040448100059011c0804054c0040014408500154001505100484484801590004048448100141054c0814451c01540154084000100048014c08044810005900500c80480c0158055c0880004c0059005c080048400050014c0884404c01590048040400500051014c0c400544010401540854015c0011015c0804481c00590148040440800059051c0084414c005400400050010c0051041c0c8448180158010c0c8448100049054c0814451c005c005c0048081001100508084400900059015c0c40484800590544044401100158001c045401080050001c048408100058010c0c8408100048014c0804451c005c00580000005400110510048440480159010c04044810015905140c44014c005001140050015400080148088400080059010c040448100149004c0844414c00510058001000180141054c0c40001c00590148040048d40059054c081440440059015c045449400058014c0884404801590058040440500051014c08000544010401540804004c0011011c0884000800590148040448100059051c0084014c005000400050010c005004140c84081c0159010c0c0448100048014c0814451c005c00580048081001100508084400100059005c0c0448c801590544044401180058001c0454001c0158011808844014005800580c0400100149014c0c1005440144015c0800005c001c0154088448480159010c040448100059011c0804014c0040014408500154001505100484484801590004048448100140014c0804451c01540154084000100048014c08044810005900500c80480c0158055c0800004c005900540800401c0158011808844004005800580c0400100148014c0c000544014400540800004c00000154088400480159010c040448100059011c08040144004001440850010c0051041c0c8448180158010c0c8448100049054c0814451c005c005c0048081001100508084400900059015c0c40484800590544044401100058001c0454010c005004140c8408180158010c0c0448100048014c0814451c005c00580048005400080140088400080059010c040448100059010c0804004c004001440050004c00080154088400480159010c040448100048014c0804451c005c0058000000100048014c080440080059010c040440080059014c0804414c005900540c544

def wall (q : Nat) : Bool := wallMask.testBit (q % 65536)

def Good (q : Nat) : Prop := wall q=true → Observe q ∧ wall (double q)=true

instance (q : Nat) : Decidable (Good q) := inferInstanceAs
  (Decidable (wall q=true → Observe q ∧ wall (double q)=true))

def checkBlock (base : Nat) : Bool :=
  (List.range 1024).all (fun j => decide (Good (base+j)))

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem block0 : checkBlock 0=true := by decide
theorem block1 : checkBlock 1024=true := by decide
theorem block2 : checkBlock 2048=true := by decide
theorem block3 : checkBlock 3072=true := by decide
theorem block4 : checkBlock 4096=true := by decide
theorem block5 : checkBlock 5120=true := by decide
theorem block6 : checkBlock 6144=true := by decide
theorem block7 : checkBlock 7168=true := by decide
theorem block8 : checkBlock 8192=true := by decide
theorem block9 : checkBlock 9216=true := by decide
theorem block10 : checkBlock 10240=true := by decide
theorem block11 : checkBlock 11264=true := by decide
theorem block12 : checkBlock 12288=true := by decide
theorem block13 : checkBlock 13312=true := by decide
theorem block14 : checkBlock 14336=true := by decide
theorem block15 : checkBlock 15360=true := by decide
theorem block16 : checkBlock 16384=true := by decide
theorem block17 : checkBlock 17408=true := by decide
theorem block18 : checkBlock 18432=true := by decide
theorem block19 : checkBlock 19456=true := by decide
theorem block20 : checkBlock 20480=true := by decide
theorem block21 : checkBlock 21504=true := by decide
theorem block22 : checkBlock 22528=true := by decide
theorem block23 : checkBlock 23552=true := by decide
theorem block24 : checkBlock 24576=true := by decide
theorem block25 : checkBlock 25600=true := by decide
theorem block26 : checkBlock 26624=true := by decide
theorem block27 : checkBlock 27648=true := by decide
theorem block28 : checkBlock 28672=true := by decide
theorem block29 : checkBlock 29696=true := by decide
theorem block30 : checkBlock 30720=true := by decide
theorem block31 : checkBlock 31744=true := by decide
theorem block32 : checkBlock 32768=true := by decide
theorem block33 : checkBlock 33792=true := by decide
theorem block34 : checkBlock 34816=true := by decide
theorem block35 : checkBlock 35840=true := by decide
theorem block36 : checkBlock 36864=true := by decide
theorem block37 : checkBlock 37888=true := by decide
theorem block38 : checkBlock 38912=true := by decide
theorem block39 : checkBlock 39936=true := by decide
theorem block40 : checkBlock 40960=true := by decide
theorem block41 : checkBlock 41984=true := by decide
theorem block42 : checkBlock 43008=true := by decide
theorem block43 : checkBlock 44032=true := by decide
theorem block44 : checkBlock 45056=true := by decide
theorem block45 : checkBlock 46080=true := by decide
theorem block46 : checkBlock 47104=true := by decide
theorem block47 : checkBlock 48128=true := by decide
theorem block48 : checkBlock 49152=true := by decide
theorem block49 : checkBlock 50176=true := by decide
theorem block50 : checkBlock 51200=true := by decide
theorem block51 : checkBlock 52224=true := by decide
theorem block52 : checkBlock 53248=true := by decide
theorem block53 : checkBlock 54272=true := by decide
theorem block54 : checkBlock 55296=true := by decide
theorem block55 : checkBlock 56320=true := by decide
theorem block56 : checkBlock 57344=true := by decide
theorem block57 : checkBlock 58368=true := by decide
theorem block58 : checkBlock 59392=true := by decide
theorem block59 : checkBlock 60416=true := by decide
theorem block60 : checkBlock 61440=true := by decide
theorem block61 : checkBlock 62464=true := by decide
theorem block62 : checkBlock 63488=true := by decide
theorem block63 : checkBlock 64512=true := by decide
theorem block64 : checkBlock 65536=true := by decide
theorem block65 : checkBlock 66560=true := by decide
theorem block66 : checkBlock 67584=true := by decide
theorem block67 : checkBlock 68608=true := by decide
theorem block68 : checkBlock 69632=true := by decide
theorem block69 : checkBlock 70656=true := by decide
theorem block70 : checkBlock 71680=true := by decide
theorem block71 : checkBlock 72704=true := by decide
theorem block72 : checkBlock 73728=true := by decide
theorem block73 : checkBlock 74752=true := by decide
theorem block74 : checkBlock 75776=true := by decide
theorem block75 : checkBlock 76800=true := by decide
theorem block76 : checkBlock 77824=true := by decide
theorem block77 : checkBlock 78848=true := by decide
theorem block78 : checkBlock 79872=true := by decide
theorem block79 : checkBlock 80896=true := by decide
theorem block80 : checkBlock 81920=true := by decide
theorem block81 : checkBlock 82944=true := by decide
theorem block82 : checkBlock 83968=true := by decide
theorem block83 : checkBlock 84992=true := by decide
theorem block84 : checkBlock 86016=true := by decide
theorem block85 : checkBlock 87040=true := by decide
theorem block86 : checkBlock 88064=true := by decide
theorem block87 : checkBlock 89088=true := by decide
theorem block88 : checkBlock 90112=true := by decide
theorem block89 : checkBlock 91136=true := by decide
theorem block90 : checkBlock 92160=true := by decide
theorem block91 : checkBlock 93184=true := by decide
theorem block92 : checkBlock 94208=true := by decide
theorem block93 : checkBlock 95232=true := by decide
theorem block94 : checkBlock 96256=true := by decide
theorem block95 : checkBlock 97280=true := by decide
theorem block96 : checkBlock 98304=true := by decide
theorem block97 : checkBlock 99328=true := by decide
theorem block98 : checkBlock 100352=true := by decide
theorem block99 : checkBlock 101376=true := by decide
theorem block100 : checkBlock 102400=true := by decide
theorem block101 : checkBlock 103424=true := by decide
theorem block102 : checkBlock 104448=true := by decide
theorem block103 : checkBlock 105472=true := by decide
theorem block104 : checkBlock 106496=true := by decide
theorem block105 : checkBlock 107520=true := by decide
theorem block106 : checkBlock 108544=true := by decide
theorem block107 : checkBlock 109568=true := by decide
theorem block108 : checkBlock 110592=true := by decide
theorem block109 : checkBlock 111616=true := by decide
theorem block110 : checkBlock 112640=true := by decide
theorem block111 : checkBlock 113664=true := by decide
theorem block112 : checkBlock 114688=true := by decide
theorem block113 : checkBlock 115712=true := by decide
theorem block114 : checkBlock 116736=true := by decide
theorem block115 : checkBlock 117760=true := by decide
theorem block116 : checkBlock 118784=true := by decide
theorem block117 : checkBlock 119808=true := by decide
theorem block118 : checkBlock 120832=true := by decide
theorem block119 : checkBlock 121856=true := by decide
theorem block120 : checkBlock 122880=true := by decide
theorem block121 : checkBlock 123904=true := by decide
theorem block122 : checkBlock 124928=true := by decide
theorem block123 : checkBlock 125952=true := by decide
theorem block124 : checkBlock 126976=true := by decide
theorem block125 : checkBlock 128000=true := by decide
theorem block126 : checkBlock 129024=true := by decide
theorem block127 : checkBlock 130048=true := by decide
theorem block128 : checkBlock 131072=true := by decide
theorem block129 : checkBlock 132096=true := by decide
theorem block130 : checkBlock 133120=true := by decide
theorem block131 : checkBlock 134144=true := by decide
theorem block132 : checkBlock 135168=true := by decide
theorem block133 : checkBlock 136192=true := by decide
theorem block134 : checkBlock 137216=true := by decide
theorem block135 : checkBlock 138240=true := by decide
theorem block136 : checkBlock 139264=true := by decide
theorem block137 : checkBlock 140288=true := by decide
theorem block138 : checkBlock 141312=true := by decide
theorem block139 : checkBlock 142336=true := by decide
theorem block140 : checkBlock 143360=true := by decide
theorem block141 : checkBlock 144384=true := by decide
theorem block142 : checkBlock 145408=true := by decide
theorem block143 : checkBlock 146432=true := by decide
theorem block144 : checkBlock 147456=true := by decide
theorem block145 : checkBlock 148480=true := by decide
theorem block146 : checkBlock 149504=true := by decide
theorem block147 : checkBlock 150528=true := by decide
theorem block148 : checkBlock 151552=true := by decide
theorem block149 : checkBlock 152576=true := by decide
theorem block150 : checkBlock 153600=true := by decide
theorem block151 : checkBlock 154624=true := by decide
theorem block152 : checkBlock 155648=true := by decide
theorem block153 : checkBlock 156672=true := by decide
theorem block154 : checkBlock 157696=true := by decide
theorem block155 : checkBlock 158720=true := by decide
theorem block156 : checkBlock 159744=true := by decide
theorem block157 : checkBlock 160768=true := by decide
theorem block158 : checkBlock 161792=true := by decide
theorem block159 : checkBlock 162816=true := by decide
theorem block160 : checkBlock 163840=true := by decide
theorem block161 : checkBlock 164864=true := by decide
theorem block162 : checkBlock 165888=true := by decide
theorem block163 : checkBlock 166912=true := by decide
theorem block164 : checkBlock 167936=true := by decide
theorem block165 : checkBlock 168960=true := by decide
theorem block166 : checkBlock 169984=true := by decide
theorem block167 : checkBlock 171008=true := by decide
theorem block168 : checkBlock 172032=true := by decide
theorem block169 : checkBlock 173056=true := by decide
theorem block170 : checkBlock 174080=true := by decide
theorem block171 : checkBlock 175104=true := by decide
theorem block172 : checkBlock 176128=true := by decide
theorem block173 : checkBlock 177152=true := by decide
theorem block174 : checkBlock 178176=true := by decide
theorem block175 : checkBlock 179200=true := by decide
theorem block176 : checkBlock 180224=true := by decide
theorem block177 : checkBlock 181248=true := by decide
theorem block178 : checkBlock 182272=true := by decide
theorem block179 : checkBlock 183296=true := by decide
theorem block180 : checkBlock 184320=true := by decide
theorem block181 : checkBlock 185344=true := by decide
theorem block182 : checkBlock 186368=true := by decide
theorem block183 : checkBlock 187392=true := by decide
theorem block184 : checkBlock 188416=true := by decide
theorem block185 : checkBlock 189440=true := by decide
theorem block186 : checkBlock 190464=true := by decide
theorem block187 : checkBlock 191488=true := by decide
theorem block188 : checkBlock 192512=true := by decide
theorem block189 : checkBlock 193536=true := by decide
theorem block190 : checkBlock 194560=true := by decide
theorem block191 : checkBlock 195584=true := by decide
theorem block192 : checkBlock 196608=true := by decide
theorem block193 : checkBlock 197632=true := by decide
theorem block194 : checkBlock 198656=true := by decide
theorem block195 : checkBlock 199680=true := by decide
theorem block196 : checkBlock 200704=true := by decide
theorem block197 : checkBlock 201728=true := by decide
theorem block198 : checkBlock 202752=true := by decide
theorem block199 : checkBlock 203776=true := by decide
theorem block200 : checkBlock 204800=true := by decide
theorem block201 : checkBlock 205824=true := by decide
theorem block202 : checkBlock 206848=true := by decide
theorem block203 : checkBlock 207872=true := by decide
theorem block204 : checkBlock 208896=true := by decide
theorem block205 : checkBlock 209920=true := by decide
theorem block206 : checkBlock 210944=true := by decide
theorem block207 : checkBlock 211968=true := by decide
theorem block208 : checkBlock 212992=true := by decide
theorem block209 : checkBlock 214016=true := by decide
theorem block210 : checkBlock 215040=true := by decide
theorem block211 : checkBlock 216064=true := by decide
theorem block212 : checkBlock 217088=true := by decide
theorem block213 : checkBlock 218112=true := by decide
theorem block214 : checkBlock 219136=true := by decide
theorem block215 : checkBlock 220160=true := by decide
theorem block216 : checkBlock 221184=true := by decide
theorem block217 : checkBlock 222208=true := by decide
theorem block218 : checkBlock 223232=true := by decide
theorem block219 : checkBlock 224256=true := by decide
theorem block220 : checkBlock 225280=true := by decide
theorem block221 : checkBlock 226304=true := by decide
theorem block222 : checkBlock 227328=true := by decide
theorem block223 : checkBlock 228352=true := by decide
theorem block224 : checkBlock 229376=true := by decide
theorem block225 : checkBlock 230400=true := by decide
theorem block226 : checkBlock 231424=true := by decide
theorem block227 : checkBlock 232448=true := by decide
theorem block228 : checkBlock 233472=true := by decide
theorem block229 : checkBlock 234496=true := by decide
theorem block230 : checkBlock 235520=true := by decide
theorem block231 : checkBlock 236544=true := by decide
theorem block232 : checkBlock 237568=true := by decide
theorem block233 : checkBlock 238592=true := by decide
theorem block234 : checkBlock 239616=true := by decide
theorem block235 : checkBlock 240640=true := by decide
theorem block236 : checkBlock 241664=true := by decide
theorem block237 : checkBlock 242688=true := by decide
theorem block238 : checkBlock 243712=true := by decide
theorem block239 : checkBlock 244736=true := by decide
theorem block240 : checkBlock 245760=true := by decide
theorem block241 : checkBlock 246784=true := by decide
theorem block242 : checkBlock 247808=true := by decide
theorem block243 : checkBlock 248832=true := by decide
theorem block244 : checkBlock 249856=true := by decide
theorem block245 : checkBlock 250880=true := by decide
theorem block246 : checkBlock 251904=true := by decide
theorem block247 : checkBlock 252928=true := by decide
theorem block248 : checkBlock 253952=true := by decide
theorem block249 : checkBlock 254976=true := by decide
theorem block250 : checkBlock 256000=true := by decide
theorem block251 : checkBlock 257024=true := by decide
theorem block252 : checkBlock 258048=true := by decide
theorem block253 : checkBlock 259072=true := by decide
theorem block254 : checkBlock 260096=true := by decide
theorem block255 : checkBlock 261120=true := by decide

theorem all_blocks : ∀ n, n<256 → checkBlock (1024*n)=true
  | 0,_ => block0
  | 1,_ => block1
  | 2,_ => block2
  | 3,_ => block3
  | 4,_ => block4
  | 5,_ => block5
  | 6,_ => block6
  | 7,_ => block7
  | 8,_ => block8
  | 9,_ => block9
  | 10,_ => block10
  | 11,_ => block11
  | 12,_ => block12
  | 13,_ => block13
  | 14,_ => block14
  | 15,_ => block15
  | 16,_ => block16
  | 17,_ => block17
  | 18,_ => block18
  | 19,_ => block19
  | 20,_ => block20
  | 21,_ => block21
  | 22,_ => block22
  | 23,_ => block23
  | 24,_ => block24
  | 25,_ => block25
  | 26,_ => block26
  | 27,_ => block27
  | 28,_ => block28
  | 29,_ => block29
  | 30,_ => block30
  | 31,_ => block31
  | 32,_ => block32
  | 33,_ => block33
  | 34,_ => block34
  | 35,_ => block35
  | 36,_ => block36
  | 37,_ => block37
  | 38,_ => block38
  | 39,_ => block39
  | 40,_ => block40
  | 41,_ => block41
  | 42,_ => block42
  | 43,_ => block43
  | 44,_ => block44
  | 45,_ => block45
  | 46,_ => block46
  | 47,_ => block47
  | 48,_ => block48
  | 49,_ => block49
  | 50,_ => block50
  | 51,_ => block51
  | 52,_ => block52
  | 53,_ => block53
  | 54,_ => block54
  | 55,_ => block55
  | 56,_ => block56
  | 57,_ => block57
  | 58,_ => block58
  | 59,_ => block59
  | 60,_ => block60
  | 61,_ => block61
  | 62,_ => block62
  | 63,_ => block63
  | 64,_ => block64
  | 65,_ => block65
  | 66,_ => block66
  | 67,_ => block67
  | 68,_ => block68
  | 69,_ => block69
  | 70,_ => block70
  | 71,_ => block71
  | 72,_ => block72
  | 73,_ => block73
  | 74,_ => block74
  | 75,_ => block75
  | 76,_ => block76
  | 77,_ => block77
  | 78,_ => block78
  | 79,_ => block79
  | 80,_ => block80
  | 81,_ => block81
  | 82,_ => block82
  | 83,_ => block83
  | 84,_ => block84
  | 85,_ => block85
  | 86,_ => block86
  | 87,_ => block87
  | 88,_ => block88
  | 89,_ => block89
  | 90,_ => block90
  | 91,_ => block91
  | 92,_ => block92
  | 93,_ => block93
  | 94,_ => block94
  | 95,_ => block95
  | 96,_ => block96
  | 97,_ => block97
  | 98,_ => block98
  | 99,_ => block99
  | 100,_ => block100
  | 101,_ => block101
  | 102,_ => block102
  | 103,_ => block103
  | 104,_ => block104
  | 105,_ => block105
  | 106,_ => block106
  | 107,_ => block107
  | 108,_ => block108
  | 109,_ => block109
  | 110,_ => block110
  | 111,_ => block111
  | 112,_ => block112
  | 113,_ => block113
  | 114,_ => block114
  | 115,_ => block115
  | 116,_ => block116
  | 117,_ => block117
  | 118,_ => block118
  | 119,_ => block119
  | 120,_ => block120
  | 121,_ => block121
  | 122,_ => block122
  | 123,_ => block123
  | 124,_ => block124
  | 125,_ => block125
  | 126,_ => block126
  | 127,_ => block127
  | 128,_ => block128
  | 129,_ => block129
  | 130,_ => block130
  | 131,_ => block131
  | 132,_ => block132
  | 133,_ => block133
  | 134,_ => block134
  | 135,_ => block135
  | 136,_ => block136
  | 137,_ => block137
  | 138,_ => block138
  | 139,_ => block139
  | 140,_ => block140
  | 141,_ => block141
  | 142,_ => block142
  | 143,_ => block143
  | 144,_ => block144
  | 145,_ => block145
  | 146,_ => block146
  | 147,_ => block147
  | 148,_ => block148
  | 149,_ => block149
  | 150,_ => block150
  | 151,_ => block151
  | 152,_ => block152
  | 153,_ => block153
  | 154,_ => block154
  | 155,_ => block155
  | 156,_ => block156
  | 157,_ => block157
  | 158,_ => block158
  | 159,_ => block159
  | 160,_ => block160
  | 161,_ => block161
  | 162,_ => block162
  | 163,_ => block163
  | 164,_ => block164
  | 165,_ => block165
  | 166,_ => block166
  | 167,_ => block167
  | 168,_ => block168
  | 169,_ => block169
  | 170,_ => block170
  | 171,_ => block171
  | 172,_ => block172
  | 173,_ => block173
  | 174,_ => block174
  | 175,_ => block175
  | 176,_ => block176
  | 177,_ => block177
  | 178,_ => block178
  | 179,_ => block179
  | 180,_ => block180
  | 181,_ => block181
  | 182,_ => block182
  | 183,_ => block183
  | 184,_ => block184
  | 185,_ => block185
  | 186,_ => block186
  | 187,_ => block187
  | 188,_ => block188
  | 189,_ => block189
  | 190,_ => block190
  | 191,_ => block191
  | 192,_ => block192
  | 193,_ => block193
  | 194,_ => block194
  | 195,_ => block195
  | 196,_ => block196
  | 197,_ => block197
  | 198,_ => block198
  | 199,_ => block199
  | 200,_ => block200
  | 201,_ => block201
  | 202,_ => block202
  | 203,_ => block203
  | 204,_ => block204
  | 205,_ => block205
  | 206,_ => block206
  | 207,_ => block207
  | 208,_ => block208
  | 209,_ => block209
  | 210,_ => block210
  | 211,_ => block211
  | 212,_ => block212
  | 213,_ => block213
  | 214,_ => block214
  | 215,_ => block215
  | 216,_ => block216
  | 217,_ => block217
  | 218,_ => block218
  | 219,_ => block219
  | 220,_ => block220
  | 221,_ => block221
  | 222,_ => block222
  | 223,_ => block223
  | 224,_ => block224
  | 225,_ => block225
  | 226,_ => block226
  | 227,_ => block227
  | 228,_ => block228
  | 229,_ => block229
  | 230,_ => block230
  | 231,_ => block231
  | 232,_ => block232
  | 233,_ => block233
  | 234,_ => block234
  | 235,_ => block235
  | 236,_ => block236
  | 237,_ => block237
  | 238,_ => block238
  | 239,_ => block239
  | 240,_ => block240
  | 241,_ => block241
  | 242,_ => block242
  | 243,_ => block243
  | 244,_ => block244
  | 245,_ => block245
  | 246,_ => block246
  | 247,_ => block247
  | 248,_ => block248
  | 249,_ => block249
  | 250,_ => block250
  | 251,_ => block251
  | 252,_ => block252
  | 253,_ => block253
  | 254,_ => block254
  | 255,_ => block255
  | n+256,h => by omega

theorem good_all (q : Nat) (hq : q<262144) : Good q := by
  have hb := all_blocks (q/1024) (by omega)
  have he := (List.all_eq_true.mp hb) (q%1024) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have hh : 1024*(q/1024)+q%1024=q := by omega
  rw [hh] at he
  exact of_decide_eq_true he

theorem entry : wall (white 146)=true := by decide

end Rule30Submission.DrivenWall

/-!
# Eventual spacings three or five in the empty-right driven gate

This is a certified forward invariant of the driven right half, not a proof
that its reconstructed left row is infinite. In particular it does not prove
`CQ01Empty`, `CQ01`, `Q01`, or any prize problem.
-/



namespace Rule30Submission.EmptyGate

open Rule30Submission.Driven Rule30Submission.DrivenWall
open Rule30PeriodTwoSideways Rule30Submission.Spacing

theorem wall_trim (a : Nat) : wall (a % 2^18)=wall a := by
  unfold wall
  rw [Nat.mod_mod_of_dvd a (by decide : 65536 ∣ 2^18)]

/-- The two unseen right cells range over every possibility in `good_all`. -/
theorem wall_step (a : Nat) (ha : wall a=true) : Observe a ∧ wall (double a)=true := by
  have ht : wall (a % 262144)=true := by
    change wall (a % 2^18)=true
    rw [wall_trim]
    exact ha
  have hg := good_all (a%262144) (Nat.mod_lt _ (by decide)) ht
  refine ⟨(observe_trim a).mp hg.1,?_⟩
  have he : wall (double (a % 2^18))=wall (double a) := by
    unfold wall
    rw [← double_prefix a 16]
  rw [he] at hg
  exact hg.2

theorem white_wall : ∀ n, wall (white (146+n))=true
  | 0 => entry
  | n+1 => by
      rw [show 146+(n+1)=(146+n)+1 by omega,white]
      exact (wall_step _ (white_wall n)).2

def gate (r : Nat) : Bool := u empty (146+r)

/-- Every six-cycle window obeys the exact gate restrictions, at all later times. -/
theorem empty_windows (r : Nat) : Window gate r := by
  have ho := (wall_step _ (white_wall r)).1
  simpa only [Observe,Window,gate,Nat.zero_add,Nat.add_zero,iterate_white,white_gate,Nat.add_assoc] using ho

/-- Black gate positions are never separated by one or two cycles. -/
theorem empty_spaced : Spaced gate := by
  intro r
  exact ⟨(empty_windows r).1,(empty_windows r).2.1⟩

/-- After a black observation, the next black observation is exactly three or five cycles later. -/
theorem empty_next_gap (r : Nat) (hr : gate r=true) :
    (gate (r+3)=true ∧ gate (r+4)=false ∧ gate (r+5)=false) ∨
    (gate (r+3)=false ∧ gate (r+4)=false ∧ gate (r+5)=true) :=
  (empty_windows r).2.2.1 hr

theorem empty_no_six_white (r : Nat) :
    (gate r || gate (r+1) || gate (r+2) || gate (r+3) || gate (r+4) || gate (r+5))=true :=
  (empty_windows r).2.2.2

theorem empty_black_after (r : Nat) : ∃ s, r≤s ∧ gate s=true := by
  have h := empty_no_six_white r
  simp only [Bool.or_eq_true] at h
  rcases h with ((((ha | hb) | hc) | hd) | he) | hf
  · exact ⟨r,Nat.le_refl _,ha⟩
  · exact ⟨r+1,by omega,hb⟩
  · exact ⟨r+2,by omega,hc⟩
  · exact ⟨r+3,by omega,hd⟩
  · exact ⟨r+4,by omega,he⟩
  · exact ⟨r+5,by omega,hf⟩

/-- The previously formalized translation applies once to this actual driven gate. -/
theorem empty_reconstruction_translate (m t : Nat) :
    Rule30ZeroBoundary.recon (boundary gate) (m+9) t =
      Rule30ZeroBoundary.recon (boundary (transform gate)) (m+1) t :=
  reconstruction_translate gate empty_spaced m t

/-- The one-step reconstruction transform still cannot be iterated on this actual driven gate. -/
theorem transformed_empty_not_spaced : ¬ Spaced (transform gate) := by
  intro h
  have hz := (transform_spaced_iff gate empty_spaced).mp h
  have hw := empty_no_six_white 4
  rw [hz 0,hz 1,hz 2,hz 3,hz 4,hz 5] at hw
  contradiction

end Rule30Submission.EmptyGate
