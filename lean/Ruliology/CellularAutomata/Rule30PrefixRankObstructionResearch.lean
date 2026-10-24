module

public import Ruliology.CellularAutomata.Rule30StripePrefixResearch

/-!
# Exact obstructions to two prefix-automaton additive ranks

These finite accepted transitions preserve every feature in the specified
model, independently of the weights. They refute these particular candidate
rank classes. They do not refute more general ranks or prove Q01.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PrefixRankObstructionResearch

open Rule30ZeroBoundary Rule30StripePrefixResearch

def packedRow (a : Nat) : Nat → Bool
  | 0 => false
  | k+1 => a.testBit k

def packedStep (a : Nat) : Nat := (a >>> 1) ^^^ (a ||| (a <<< 1))

theorem packedStep_bit (a j : Nat) :
    (packedStep a).testBit j = xor (a.testBit (j+1))
      (a.testBit j || if j=0 then false else a.testBit (j-1)) := by
  simp only [packedStep,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  cases j <;> simp [Nat.add_comm]

theorem packedStep_sound (a : Nat) : zrow (packedRow a) 1=packedRow (packedStep a) := by
  funext k
  cases k with
  | zero => rfl
  | succ j =>
      rw [zrow_succ]
      simp only [zrow_zero_self (show packedRow a 0=false from rfl)]
      change xor (a.testBit (j+1)) (a.testBit j || packedRow a j) = _
      rw [packedRow,packedStep_bit]
      cases j <;> rfl

theorem packedStep_two (a : Nat) :
    zrow (packedRow a) 2=packedRow (packedStep (packedStep a)) := by
  funext k
  rw [show 2=1+1 by rfl,zrow_shift,packedStep_sound,packedStep_sound]

theorem packedRow_finite (a W : Nat) (ha : a<2^W) : FinSupp (packedRow a) := by
  refine ⟨W,?_⟩
  intro k hk
  cases k with
  | zero => rfl
  | succ j =>
      change a.testBit j=false
      have h := Nat.testBit_mod_two_pow a W j
      rw [Nat.mod_eq_of_lt ha] at h
      simpa [show ¬j<W by omega] using h

/-- Spatial parity, the first deviation from the stripe, and optionally the
parity of all black cells strictly before the current window. -/
def advance (parity : Bool) (state bit : Nat) : Nat :=
  let core := if parity then state/2 else state
  let phase := core/3
  let mode := core%3
  let nextMode := if mode=0 ∧ bit≠1-phase then (if phase=0 then 1 else 2) else mode
  let nextCore := (1-phase)*3+nextMode
  if parity then 2*nextCore+((state%2+bit)%2) else nextCore

def scoreLoop (r : Nat) (parity : Bool) (w : Nat → Int) : Nat → Nat → Nat → Int
  | 0, _, _ => 0
  | n+1, state, a =>
      (if a%2^r=0 then 0 else w (state*2^r+a%2^r)) +
        scoreLoop r parity w n (advance parity state (a%2)) (a/2)

def score (r : Nat) (parity : Bool) (w : Nat → Int) (a : Nat) : Int :=
  scoreLoop r parity w (a.log2+1) 0 a

theorem transition203 : zrow (packedRow 203) 2=packedRow 803 := by
  rw [packedStep_two]
  rfl

theorem transition143659 : zrow (packedRow 143659) 2=packedRow 805387 := by
  rw [packedStep_two]
  rfl

theorem features203 (parity : Bool) (w : Nat → Int) :
    score 2 parity w 203=score 2 parity w 803 := by
  cases parity <;> dsimp [score,scoreLoop,advance] <;> omega

theorem features143659 (w : Nat → Int) :
    score 4 false w 143659=score 4 false w 805387 := by
  dsimp [score,scoreLoop,advance]
  omega

theorem packedRow_good (a W : Nat) (ha : a<2^W)
    (h1 : a.testBit 0=true) (h2 : a.testBit 1=true) : Good (packedRow a) := by
  refine ⟨packedRow_finite a W ha,2,?_,by decide⟩
  refine ⟨by decide,?_,?_⟩
  · intro k hk hk2
    have : k=1 := by omega
    subst k
    exact h1
  · change a.testBit 1≠false
    rw [h2]
    decide

theorem good203 : Good (packedRow 203) := packedRow_good 203 8 (by decide) (by decide) (by decide)
theorem good803 : Good (packedRow 803) := packedRow_good 803 10 (by decide) (by decide) (by decide)
theorem good143659 : Good (packedRow 143659) :=
  packedRow_good 143659 18 (by decide) (by decide) (by decide)
theorem good805387 : Good (packedRow 805387) :=
  packedRow_good 805387 20 (by decide) (by decide) (by decide)

/-- The accepted-transition strict descent required by the proposed rank. -/
def Descent (r : Nat) (parity : Bool) (w : Nat → Int) : Prop :=
  ∀ a, Good (packedRow a) → Good (zrow (packedRow a) 2) →
    score r parity w (packedStep (packedStep a))+1≤score r parity w a

theorem no_descent_r2 (parity : Bool) (w : Nat → Int) : ¬Descent 2 parity w := by
  intro h
  have hn : Good (zrow (packedRow 203) 2) := by rw [transition203]; exact good803
  have hh := h 203 good203 hn
  change score 2 parity w 803+1≤score 2 parity w 203 at hh
  rw [features203 parity w] at hh
  omega

theorem no_descent_r4 (w : Nat → Int) : ¬Descent 4 false w := by
  intro h
  have hn : Good (zrow (packedRow 143659) 2) := by rw [transition143659]; exact good805387
  have hh := h 143659 good143659 hn
  change score 4 false w 805387+1≤score 4 false w 143659 at hh
  rw [features143659 w] at hh
  omega

theorem no_integerRanking_r2 (parity : Bool) (w : Nat → Int) (V : (Nat → Bool) → Int)
    (hs : ∀ a, V (packedRow a)=score 2 parity w a) : ¬IntegerRanking V := by
  intro h
  apply no_descent_r2 parity w
  intro a ha hn
  have hh := h.2 (packedRow a) ha hn
  rw [packedStep_two,hs,hs] at hh
  exact hh

theorem no_integerRanking_r4 (w : Nat → Int) (V : (Nat → Bool) → Int)
    (hs : ∀ a, V (packedRow a)=score 4 false w a) : ¬IntegerRanking V := by
  intro h
  apply no_descent_r4 w
  intro a ha hn
  have hh := h.2 (packedRow a) ha hn
  rw [packedStep_two,hs,hs] at hh
  exact hh

/-- A finite, decidable witness for a good packed row. -/
def GoodWitness (a W d : Nat) : Prop :=
  a<2^W ∧ 1≤d ∧ d%2=0 ∧
  (∀ k : Fin d, 1≤k.val → packedRow a k.val=stripe k.val) ∧
  packedRow a d≠stripe d

instance (a W d : Nat) : Decidable (GoodWitness a W d) := by
  unfold GoodWitness
  infer_instance

theorem goodWitness_sound {a W d : Nat} (h : GoodWitness a W d) : Good (packedRow a) := by
  refine ⟨packedRow_finite a W h.1,d,⟨h.2.1,?_,h.2.2.2.2⟩,h.2.2.1⟩
  intro k hk hkd
  exact h.2.2.2.1 ⟨k,hkd⟩ hk

def Accepted (a : Nat) : Prop := Good (packedRow a) ∧ Good (zrow (packedRow a) 2)

theorem accepted_of_witness {a d e : Nat}
    (h : GoodWitness a 16 d) (hn : GoodWitness (packedStep (packedStep a)) 16 e) : Accepted a := by
  refine ⟨goodWitness_sound h,?_⟩
  rw [packedStep_two]
  exact goodWitness_sound hn

/-- A weaker candidate descent that charges only changes of the odd-time
boundary bit. The second spatial bit determines that boundary bit on an
accepted two-step transition. No certificate satisfying this is asserted. -/
def FreeFlipDescent (r : Nat) (parity : Bool) (w : Nat → Int) : Prop :=
  ∀ a, Accepted a →
    score r parity w (packedStep (packedStep a))+
      (if a.testBit 1=(packedStep (packedStep a)).testBit 1 then 0 else 1)≤score r parity w a

/-- An exact positive combination of nine actual transitions rules out even
this weaker descent for length-two windows, with either prefix parity model. -/
theorem no_freeFlip_descent_r2 (parity : Bool) (w : Nat → Int) :
    ¬FreeFlipDescent 2 parity w := by
  intro h
  have h1 := h 323 (accepted_of_witness (d:=2) (e:=4) (by decide) (by decide))
  have h2 := h 1277 (accepted_of_witness (d:=4) (e:=2) (by decide) (by decide))
  have h3 := h 1341 (accepted_of_witness (d:=4) (e:=2) (by decide) (by decide))
  have h4 := h 1917 (accepted_of_witness (d:=4) (e:=2) (by decide) (by decide))
  have h5 := h 2371 (accepted_of_witness (d:=2) (e:=4) (by decide) (by decide))
  have h6 := h 2429 (accepted_of_witness (d:=4) (e:=2) (by decide) (by decide))
  have h7 := h 2653 (accepted_of_witness (d:=4) (e:=2) (by decide) (by decide))
  have h8 := h 4035 (accepted_of_witness (d:=2) (e:=4) (by decide) (by decide))
  have h9 := h 4093 (accepted_of_witness (d:=4) (e:=2) (by decide) (by decide))
  have hw1 := Int.mul_le_mul_of_nonneg_left h1 (by decide : (0:Int)≤3)
  have hw2 := Int.mul_le_mul_of_nonneg_left h2 (by decide : (0:Int)≤8)
  have hw3 := Int.mul_le_mul_of_nonneg_left h3 (by decide : (0:Int)≤6)
  have hw4 := Int.mul_le_mul_of_nonneg_left h4 (by decide : (0:Int)≤7)
  have hw5 := Int.mul_le_mul_of_nonneg_left h5 (by decide : (0:Int)≤38)
  have hw6 := Int.mul_le_mul_of_nonneg_left h6 (by decide : (0:Int)≤13)
  have hw7 := Int.mul_le_mul_of_nonneg_left h7 (by decide : (0:Int)≤5)
  have hw8 := Int.mul_le_mul_of_nonneg_left h8 (by decide : (0:Int)≤2)
  have hw9 := Int.mul_le_mul_of_nonneg_left h9 (by decide : (0:Int)≤4)
  have hh := Int.add_le_add (Int.add_le_add (Int.add_le_add (Int.add_le_add
    (Int.add_le_add (Int.add_le_add (Int.add_le_add (Int.add_le_add
      hw1 hw2) hw3) hw4) hw5) hw6) hw7) hw8) hw9
  cases parity <;> dsimp [score,scoreLoop,advance,packedStep,Nat.testBit] at hh <;> omega

end Ruliology.CellularAutomata.Rule30PrefixRankObstructionResearch
