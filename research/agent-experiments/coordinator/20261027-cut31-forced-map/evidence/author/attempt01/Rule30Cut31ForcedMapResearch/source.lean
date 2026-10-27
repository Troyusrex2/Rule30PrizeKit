module

public import Ruliology.CellularAutomata.Rule30EmptyGateLanguageResearch

/-!+# The complete cut-31 boundary of the actual empty-driven gate

The certified eight-bit windows cover the actual gate from its first index.
Overlapping these windows gives a small 17-bit certificate, which computes
both the new boundary and its nonzero forcing. No second-reset closure or
finite-support contradiction is asserted.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Cut31ForcedMapResearch

open Rule30ZeroBoundary Rule30PeriodTwoSideways
open Rule30SpacingRenormalizationResearch Rule30EmptyGateLanguageResearch

def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => pack f n ||| (f n).toNat <<< n

theorem pack_bit (f : Nat → Bool) : ∀ n i,
    (pack f n).testBit i = if i<n then f i else false := by
  intro n
  induction n with
  | zero => intro i; simp [pack]
  | succ n ih =>
      intro i
      rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_bool_toNat, ih]
      by_cases h : i<n
      · simp [h, show i<n+1 by omega, show ¬n≤i by omega]
      · by_cases he : i=n
        · subst i; simp
        · simp [h, show ¬i<n+1 by omega, show n≤i by omega, show i-n≠0 by omega]

def word (G : Nat → Bool) (r n : Nat) : Nat := pack (fun i => G (r+i)) n

def allowed8 : List Nat := [8,9,16,18,33,36,66,72,132,144]

theorem actual_eight (r : Nat) : word refinedGate r 8 ∈ allowed8 := by
  simpa [word, pack, allowed8, windowWord, Nat.add_zero] using windowWord_allowed r

def extend (n : Nat) (w : Nat) : List Nat :=
  [w, w ||| (1 <<< n)] |>.filter (fun v => decide ((v >>> (n-7)) % 256 ∈ allowed8))

def prefixes : Nat → List Nat
  | 0 => allowed8
  | n+1 => (prefixes n).flatMap (extend (8+n))

theorem rolling_word (G : Nat → Bool) (r n : Nat) (hn : 7≤n) :
    (word G r (n+1) >>> (n-7)) % 256 = word G (r+(n-7)) 8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (((word G r (n+1) >>> (n-7)) % 2^8).testBit i) = _
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, word, pack_bit]
  by_cases hi : i<8
  · simp [hi, show i+(n-7)<n+1 by omega, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simp [hi]

theorem actual_prefixes : ∀ n r, word refinedGate r (8+n) ∈ prefixes n := by
  intro n
  induction n with
  | zero => intro r; exact actual_eight r
  | succ n ih =>
      intro r
      rw [prefixes, List.mem_flatMap]
      refine ⟨word refinedGate r (8+n), ih r, ?_⟩
      rw [extend, List.mem_filter]
      constructor
      · change pack (fun i => refinedGate (r+i)) (8+(n+1)) ∈ _
        rw [show 8+(n+1)=(8+n)+1 by omega, pack]
        cases refinedGate (r+(8+n)) <;> simp [word, Bool.toNat]
      · simp only [decide_eq_true_eq]
        rw [show 8+(n+1)=(8+n)+1 by omega, rolling_word _ _ _ (by omega)]
        exact actual_eight _

def allowed17 : List Nat :=
  [4228,4240,4624,4626,8456,8457,8481,9249,9252,16912,16914,16962,18498,
   18504,33825,33828,33924,36996,37008,67650,67656,67848,67849,73992,73993,74017]

set_option maxRecDepth 100000 in
theorem cover_certificate : (prefixes 9).all (fun w => decide (w ∈ allowed17)) = true := by
  decide

theorem actual_seventeen (r : Nat) : word refinedGate r 17 ∈ allowed17 := by
  have h := List.all_eq_true.mp cover_certificate (word refinedGate r 17) (actual_prefixes 9 r)
  exact of_decide_eq_true h

def columns (a : Nat) : Nat → Nat × Nat
  | 0 => (0,a)
  | n+1 => let p := columns a n
           (p.2, (p.2 >>> 1) ^^^ (p.2 ||| p.1))

theorem columns_sound (a : Nat) : ∀ n t,
    ((columns a n).1.testBit t = recon a.testBit n t) ∧
    ((columns a n).2.testBit t = recon a.testBit (n+1) t) := by
  intro n
  induction n with
  | zero => intro t; simp [columns, recon]
  | succ n ih =>
      intro t
      refine ⟨(ih t).2, ?_⟩
      simp only [columns, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight]
      rw [(ih (t+1)).2, (ih t).2, (ih t).1]
      rfl

def packedBoundary (w : Nat) : Nat := pack (boundary w.testBit) 33

def pulse (G : Nat → Bool) (r : Nat) : Bool := G r && G (r+3)

def bEven (G : Nat → Bool) (r : Nat) : Bool :=
  xor (xor (xor (xor (xor (!G (r+1)) (pulse G (r+1)))
    (pulse G (r+5))) (pulse G (r+7))) (pulse G (r+8))) (pulse G (r+12))

def bOdd (G : Nat → Bool) (r : Nat) : Bool :=
  xor (xor (xor (xor (xor (xor (xor true (pulse G (r+3))) (pulse G (r+4)))
    (pulse G (r+7))) (pulse G (r+8))) (pulse G (r+11))) (pulse G (r+13)))
    (pulse G (r+4) && pulse G (r+12))

def lEven (G : Nat → Bool) (r : Nat) : Bool :=
  xor (xor (pulse G (r+6)) (pulse G (r+7))) (pulse G (r+12))

def lOdd (G : Nat → Bool) (r : Nat) : Bool :=
  xor (xor (xor (pulse G (r+7)) (pulse G (r+8))) (pulse G (r+13)))
    (pulse G (r+5) && pulse G (r+13))

def LocalClaim (w : Nat) : Prop :=
  let p := columns (packedBoundary w) 31
  p.2.testBit 0 = bEven w.testBit 0 ∧
  p.2.testBit 1 = bOdd w.testBit 0 ∧
  (p.1.testBit 0 && !p.2.testBit 0) = lEven w.testBit 0 ∧
  (p.1.testBit 1 && !p.2.testBit 1) = lOdd w.testBit 0

instance (w : Nat) : Decidable (LocalClaim w) := inferInstanceAs (Decidable (let p := columns (packedBoundary w) 31
  p.2.testBit 0 = bEven w.testBit 0 ∧ p.2.testBit 1 = bOdd w.testBit 0 ∧
  (p.1.testBit 0 && !p.2.testBit 0) = lEven w.testBit 0 ∧
  (p.1.testBit 1 && !p.2.testBit 1) = lOdd w.testBit 0))

set_option maxRecDepth 100000 in
theorem local_certificate : allowed17.all (fun w => decide (LocalClaim w)) = true := by
  decide

theorem encoded_boundary (G : Nat → Bool) (r t : Nat) (ht : t<33) :
    (packedBoundary (word G r 17)).testBit t = boundary G (2*r+t) := by
  simp only [packedBoundary, pack_bit, if_pos ht, boundary, word]
  rw [pack_bit]
  have hh : t/2<17 := by omega
  simp only [if_pos hh]
  have hm : (2*r+t)%2=t%2 := by omega
  have hd : (2*r+t)/2=r+t/2 := by omega
  rw [hm,hd]

theorem encoded_recon (G : Nat → Bool) (r k t : Nat) (hkt : k+t≤33) :
    recon (packedBoundary (word G r 17)).testBit k t = recon (boundary G) k (2*r+t) := by
  have hh : ∀ j, j<k → (packedBoundary (word G r 17)).testBit (t+j) = boundary G (t+j+2*r) := by
    intro j hj
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using encoded_boundary G r (t+j) (by omega)
  have he := recon_local k t hh
  rw [← recon_shift] at he
  simpa [Nat.add_comm] using he

def X (G : Nat → Bool) (k t : Nat) : Bool := recon (boundary G) k t
def B (G : Nat → Bool) (t : Nat) : Bool := X G 32 t
def L (G : Nat → Bool) (t : Nat) : Bool := X G 31 t && !X G 32 t

theorem cut31_actual (r : Nat) :
    B refinedGate (2*r) = bEven refinedGate r ∧
    B refinedGate (2*r+1) = bOdd refinedGate r ∧
    L refinedGate (2*r) = lEven refinedGate r ∧
    L refinedGate (2*r+1) = lOdd refinedGate r := by
  have h := of_decide_eq_true (List.all_eq_true.mp local_certificate (word refinedGate r 17) (actual_seventeen r))
  change LocalClaim (word refinedGate r 17) at h
  simp only [LocalClaim] at h
  rw [(columns_sound _ 31 0).2, (columns_sound _ 31 1).2,
    (columns_sound _ 31 0).1, (columns_sound _ 31 1).1] at h
  rw [encoded_recon _ _ 32 0 (by omega), encoded_recon _ _ 32 1 (by omega),
    encoded_recon _ _ 31 0 (by omega), encoded_recon _ _ 31 1 (by omega)] at h
  simpa [B,L,X,bEven,bOdd,lEven,lOdd,pulse,word,pack_bit,Nat.add_assoc] using h

theorem actual_history311 (t : Nat) :
    zrow (Psi empty) (t+311) 1 = boundary refinedGate t := by
  rcases Nat.mod_two_eq_zero_or_one t with ht | ht
  · obtain ⟨r,rfl⟩ : ∃ r, t=2*r := ⟨t/2,by omega⟩
    rw [show 2*r+311=2*(155+r)+1 by omega,Psi_free,boundary_even]
    rfl
  · obtain ⟨r,rfl⟩ : ∃ r, t=2*r+1 := ⟨t/2,by omega⟩
    rw [show 2*r+1+311=2*(156+r) by omega,Psi_inX empty,boundary_odd]

theorem actual_reconstruction (k t : Nat) : X refinedGate k t = zrow (Psi empty) (t+311) k := by
  have hh : (fun s => zrow (Psi empty) (s+311) 1)=boundary refinedGate := funext actual_history311
  have hr := recon_shift (fun s => zrow (Psi empty) s 1) 311 k t
  rw [hh] at hr
  exact hr.symm.trans (history_eq_recon (Psi empty) k (t+311)).symm

def forcedTail (b l : Nat → Bool) : Nat → Nat → Bool
  | 0,t => b t
  | 1,t => xor (xor (b (t+1)) (b t)) (l t)
  | n+2,t => xor (forcedTail b l (n+1) (t+1))
      (forcedTail b l (n+1) t || forcedTail b l n t)

theorem forced_tail_exact (G : Nat → Bool) : ∀ n t,
    forcedTail (B G) (L G) n t = X G (n+32) t := by
  have hb (t : Nat) : forcedTail (B G) (L G) 1 t = X G 33 t := by
    simp only [forcedTail,B,L,X]
    rw [show 33=31+2 by omega,recon_two]
    cases recon (boundary G) 32 (t+1) <;> cases recon (boundary G) 32 t <;>
      cases recon (boundary G) 31 t <;> rfl
  have key : ∀ n, (∀ t, forcedTail (B G) (L G) n t = X G (n+32) t) ∧
      (∀ t, forcedTail (B G) (L G) (n+1) t = X G (n+33) t) := by
    intro n
    induction n with
    | zero => exact ⟨fun _ => rfl,hb⟩
    | succ n ih =>
        refine ⟨ih.2,?_⟩
        intro t
        rw [show n+1+1=n+2 by omega,forcedTail,ih.2 (t+1),ih.2 t,ih.1 t]
        change _ = recon (boundary G) (n+1+33) t
        rw [show n+1+33=(n+32)+2 by omega,recon_two]
  exact fun n => (key n).1

theorem actual_forced_tail (n t : Nat) :
    forcedTail (B refinedGate) (L refinedGate) n t = zrow (Psi empty) (t+311) (n+32) := by
  rw [forced_tail_exact,actual_reconstruction]

end Ruliology.CellularAutomata.Rule30Cut31ForcedMapResearch
