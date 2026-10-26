import HeightTwoMixedControl

/-! Saturation of a pointwise two-phase abstraction starting at a genuine
finite-white first clock birth. Abstract paths are NOT claimed to be actual
temporal trajectories: the two new initial phase bits are chosen independently.
The state retains two adjacent columns at t,t+1,t+16,t+17 and time parity.
Half-clock defects and signed one-step height increments are functions of
these observations; accumulated heights and cross-time compatibility are not. -/
namespace AnchoredDefectAbstraction
open CedarSafetySoundness CedarSafety HeightOneSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def code4 (a b c d : Bool) : Nat := a.toNat+2*b.toNat+4*c.toNat+8*d.toNat
def pack (a u : Nat) : Fin 256 := ⟨(a+16*u)%256,by omega⟩
def aBit (s : Fin 256) (k : Nat) : Bool := (s.val%16).testBit k
def uBit (s : Fin 256) (k : Nat) : Bool := (s.val/16).testBit k

def observe (a u : Nat → Bool) (t : Nat) : Fin 256 :=
  pack (code4 (a t) (a (t+1)) (a (t+16)) (a (t+17)))
    (code4 (u t) (u (t+1)) (u (t+16)) (u (t+17)))

/-- Exact update at the two sampled temporal edges. The new b(t) and
b(t+16) are independent choices in this overapproximation. -/
def next (s : Fin 256) (choice : Fin 4) : Fin 256 :=
  let x := choice.val.testBit 1
  let y := choice.val.testBit 0
  pack (code4 x (xor x (aBit s 0 || uBit s 0))
    y (xor y (aBit s 2 || uBit s 2))) (s.val%16)

def valid (s : Fin 256) : Bool :=
  ((!uBit s 0 || xor (aBit s 0) (aBit s 1)) &&
    (!(xor (aBit s 0) (aBit s 1)) || (uBit s 0 || uBit s 1))) &&
  ((!uBit s 2 || xor (aBit s 2) (aBit s 3)) &&
    (!(xor (aBit s 2) (aBit s 3)) || (uBit s 2 || uBit s 3)))

def choiceOf (x y : Bool) : Fin 4 := ⟨(2*x.toNat+y.toNat)%4,by omega⟩

theorem encode_step : ∀ a0 a1 a16 a17 u0 u1 u16 u17 x y : Bool,
    pack (code4 x (xor x (a0 || u0)) y (xor y (a16 || u16)))
      (code4 a0 a1 a16 a17) =
    next (pack (code4 a0 a1 a16 a17) (code4 u0 u1 u16 u17)) (choiceOf x y) := by
  decide +kernel

theorem actual_extension_observed (a u b : Nat → Bool)
    (hr : RootEventHeight.Recurrence a u b) (t : Nat) :
    observe b a t=next (observe a u t) (choiceOf (b t) (b (t+16))) := by
  have h0 := hr t
  have h16 := hr (t+16)
  rw [show t+16+1=t+17 by omega] at h16
  unfold observe
  rw [h0,h16]
  exact encode_step _ _ _ _ _ _ _ _ _ _

theorem cover_preserved : ∀ s : Fin 256, ∀ c : Fin 4,
    valid s=true → valid (next s c)=true := by decide +kernel

/-- The genuine known word11011001001 first fails return16 at its prefix
1101100100. These finite words use the literal white-boundary evolution. -/
def older : List Bool := [true,true,false,true,true,false,false,true,false]
def birth : List Bool := older++[false]
def actualA (t : Nat) : Bool := newest (evolution t birth)
def actualU (t : Nat) : Bool := newest (evolution t older)

theorem genuine_birth_certificate :
    evolution 16 older=older ∧ evolution 16 birth=older++[true] ∧
    evolution 32 birth=birth ∧
    (∀ n : Fin 10, evolution 16 (birth.take n.val)=birth.take n.val) := by
  decide +kernel

theorem genuine_birth_nonreturn : evolution 16 birth≠birth := by decide +kernel

theorem genuine_older_periodic (t : Nat) : actualU (t+16)=actualU t := by
  unfold actualU
  rw [evolution_add,genuine_birth_certificate.1]

theorem genuine_birth_antiperiodic (t : Nat) : actualA (t+16)=!actualA t := by
  have h := trace_restart birth 16 t
  rw [genuine_birth_certificate.2.1] at h
  change tr (older++[!false]) t=tr birth (16+t) at h
  rw [leaf_flip_trace] at h
  simpa only [birth,trace_eq,Nat.add_comm,actualA] using h.symm

@@TABLES@@

def seed (p : Fin 2) (s : Fin 256) : Bool := (seedTable p).contains s.val
def rank (p : Fin 2) (s : Fin 256) : Nat := (rankTable p).getD s.val 0
def previous (p : Fin 2) (s : Fin 256) : Fin 256 :=
  ⟨(predTable p).getD s.val 0 % 256,by omega⟩
def stepChoice (p : Fin 2) (s : Fin 256) : Fin 4 :=
  ⟨(choiceTable p).getD s.val 0 % 4,by omega⟩
def witnessTime (p : Fin 2) (s : Fin 256) : Nat := (witnessTable p).getD s.val 0

/-- Every seed-table entry comes from the certified genuine first birth at
an actual temporal phase of the stated parity. No free strip supplies a seed. -/
theorem seed_certificate : ∀ p : Fin 2, ∀ s : Fin 256, seed p s=true →
    witnessTime p s<32 ∧ witnessTime p s%2=p.val ∧
    observe actualA actualU (witnessTime p s)=s := by decide +kernel

theorem descent_certificate : ∀ p : Fin 2, ∀ s : Fin 256, valid s=true →
    seed p s=true ∨ (valid (previous p s)=true ∧ rank p (previous p s)<rank p s ∧
      next (previous p s) (stepChoice p s)=s) := by decide +kernel

theorem rank_bound : ∀ p : Fin 2, ∀ s : Fin 256, valid s=true → rank p s≤4 := by
  decide +kernel

/-- Every predicate closed under this pointwise abstract extension and true
on the genuine birth observations includes every cover-admissible state.
This is a theorem about an abstraction, not actual trajectory reachability. -/
theorem invariant_saturation (I : Fin 2 → Fin 256 → Prop)
    (hs : ∀ p s, seed p s=true → I p s)
    (hc : ∀ p s c, I p s → I p (next s c)) :
    ∀ p s, valid s=true → I p s := by
  intro p s
  have all : ∀ n : Nat, ∀ s : Fin 256, rank p s=n → valid s=true → I p s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hn hv
      rcases descent_certificate p s hv with hseed | ⟨hvalid,hrank,hnext⟩
      · exact hs p s hseed
      · have hprev := ih (rank p (previous p s)) (by omega) (previous p s) rfl hvalid
        rw [← hnext]
        exact hc p _ _ hprev
  exact all (rank p s) s rfl

theorem genuine_invariant_saturation (I : Fin 2 → Fin 256 → Prop)
    (hb : ∀ t, I ⟨t%2,by omega⟩ (observe actualA actualU t))
    (hc : ∀ p s c, I p s → I p (next s c)) :
    ∀ p s, valid s=true → I p s := by
  apply invariant_saturation I ?_ hc
  intro p s hs
  obtain ⟨_,hp,ho⟩ := seed_certificate p s hs
  have h := hb (witnessTime p s)
  rw [ho] at h
  have he : (⟨witnessTime p s%2,by omega⟩ : Fin 2)=p := Fin.ext hp
  rwa [he] at h

theorem mixed_observations_valid : ∀ t : Fin 32,
    valid (observe (HeightTwoMixedControl.col 5) (HeightTwoMixedControl.col 4) t.val)=true ∧
    valid (observe (HeightTwoMixedControl.col 6) (HeightTwoMixedControl.col 5) t.val)=true := by
  decide +kernel

/-- No inductive separator in this precise pointwise domain can reject even
one of these observed mixed-control states while accepting the genuine seed.
Different observation times may use DIFFERENT abstract paths. -/
theorem mixed_control_not_separated (I : Fin 2 → Fin 256 → Prop)
    (hb : ∀ t, I ⟨t%2,by omega⟩ (observe actualA actualU t))
    (hc : ∀ p s c, I p s → I p (next s c)) (t : Fin 32) :
    I ⟨t.val%2,by omega⟩
      (observe (HeightTwoMixedControl.col 5) (HeightTwoMixedControl.col 4) t.val) ∧
    I ⟨t.val%2,by omega⟩
      (observe (HeightTwoMixedControl.col 6) (HeightTwoMixedControl.col 5) t.val) := by
  have h := genuine_invariant_saturation I hb hc
  exact ⟨h _ _ (mixed_observations_valid t).1,h _ _ (mixed_observations_valid t).2⟩

end AnchoredDefectAbstraction
