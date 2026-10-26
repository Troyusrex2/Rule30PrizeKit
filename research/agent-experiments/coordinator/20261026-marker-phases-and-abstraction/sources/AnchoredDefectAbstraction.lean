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

def seedTable (p : Fin 2) : List Nat :=
  if p.val=0 then [
    3,12,86,89,163,166,169,172,246,249]
  else [
    86,89,166,169]

def rankTable (p : Fin 2) : List Nat :=
  if p.val=0 then [
    4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,2,2,0,0,0,0,0,0,0,0,0,0,2,2,0,
    3,2,2,3,0,0,0,0,0,0,0,0,3,2,2,3,0,1,1,0,0,0,0,0,0,0,0,0,0,1,1,0,
    0,0,0,0,2,0,0,2,2,0,0,2,0,0,0,0,0,0,0,0,0,2,0,0,0,0,2,0,0,0,0,0,
    0,0,0,0,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,2,2,0,0,2,2,0,0,0,0,0,
    3,0,0,3,2,0,0,2,2,0,0,2,3,0,0,3,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,
    4,2,2,0,2,3,0,2,2,0,3,2,0,2,2,4,0,3,3,0,0,2,2,0,0,2,2,0,0,3,3,0,
    0,0,0,0,1,0,0,1,1,0,0,1,0,0,0,0,0,0,0,0,0,2,2,0,0,2,2,0,0,0,0,0,
    0,0,0,0,3,2,2,3,3,2,2,3,0,0,0,0,0,0,0,0,0,4,0,0,0,0,4,0,0,0,0,0]
  else [
    4,0,0,4,0,0,0,0,0,0,0,0,4,0,0,4,0,2,2,0,0,0,0,0,0,0,0,0,0,2,2,0,
    3,2,2,3,0,0,0,0,0,0,0,0,3,2,2,3,0,4,4,0,0,0,0,0,0,0,0,0,0,4,4,0,
    0,0,0,0,2,0,0,2,2,0,0,2,0,0,0,0,0,0,0,0,0,2,0,0,0,0,2,0,0,0,0,0,
    0,0,0,0,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,2,2,0,0,2,2,0,0,0,0,0,
    3,0,0,3,2,0,0,2,2,0,0,2,3,0,0,3,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,
    4,2,2,4,2,3,0,2,2,0,3,2,4,2,2,4,0,3,3,0,0,2,2,0,0,2,2,0,0,3,3,0,
    0,0,0,0,4,0,0,4,4,0,0,4,0,0,0,0,0,0,0,0,0,2,2,0,0,2,2,0,0,0,0,0,
    0,0,0,0,3,2,2,3,3,2,2,3,0,0,0,0,0,0,0,0,0,4,4,0,0,4,4,0,0,0,0,0]

def predTable (p : Fin 2) : List Nat :=
  if p.val=0 then [
    32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,49,49,0,0,0,0,0,0,0,0,0,0,49,49,0,
    34,50,50,34,0,0,0,0,0,0,0,0,34,50,50,34,0,3,3,0,0,0,0,0,0,0,0,0,0,3,3,0,
    0,0,0,0,196,0,0,196,196,0,0,196,0,0,0,0,0,0,0,0,0,101,0,0,0,0,101,0,0,0,0,0,
    0,0,0,0,166,86,86,166,166,86,86,166,0,0,0,0,0,0,0,0,0,199,199,0,0,199,199,0,0,0,0,0,
    136,0,0,136,200,0,0,200,200,0,0,200,136,0,0,136,0,169,169,0,0,89,89,0,0,89,89,0,0,169,169,0,
    170,154,154,0,106,218,0,106,106,0,218,106,0,154,154,170,0,139,139,0,0,203,203,0,0,203,203,0,0,139,139,0,
    0,0,0,0,12,0,0,12,12,0,0,12,0,0,0,0,0,0,0,0,0,61,61,0,0,61,61,0,0,0,0,0,
    0,0,0,0,46,62,62,46,46,62,62,46,0,0,0,0,0,0,0,0,0,47,0,0,0,0,47,0,0,0,0,0]
  else [
    128,0,0,128,0,0,0,0,0,0,0,0,128,0,0,128,0,145,145,0,0,0,0,0,0,0,0,0,0,145,145,0,
    162,146,146,162,0,0,0,0,0,0,0,0,162,146,146,162,0,131,131,0,0,0,0,0,0,0,0,0,0,131,131,0,
    0,0,0,0,100,0,0,100,100,0,0,100,0,0,0,0,0,0,0,0,0,101,0,0,0,0,101,0,0,0,0,0,
    0,0,0,0,166,86,86,166,166,86,86,166,0,0,0,0,0,0,0,0,0,103,103,0,0,103,103,0,0,0,0,0,
    168,0,0,168,104,0,0,104,104,0,0,104,168,0,0,168,0,169,169,0,0,89,89,0,0,89,89,0,0,169,169,0,
    170,154,154,170,106,90,0,106,106,0,90,106,170,154,154,170,0,171,171,0,0,107,107,0,0,107,107,0,0,171,171,0,
    0,0,0,0,140,0,0,140,140,0,0,140,0,0,0,0,0,0,0,0,0,157,157,0,0,157,157,0,0,0,0,0,
    0,0,0,0,174,158,158,174,174,158,158,174,0,0,0,0,0,0,0,0,0,143,143,0,0,143,143,0,0,0,0,0]

def choiceTable (p : Fin 2) : List Nat :=
  if p.val=0 then [
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,3,1,0,
    0,2,0,2,0,0,0,0,0,0,0,0,1,3,1,3,0,2,0,0,0,0,0,0,0,0,0,0,0,3,1,0,
    0,0,0,0,1,0,0,3,0,0,0,2,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,1,3,1,3,0,2,0,2,0,0,0,0,0,0,0,0,0,3,1,0,0,2,0,0,0,0,0,0,
    0,0,0,2,1,0,0,3,0,0,0,2,1,0,0,3,0,2,0,0,0,3,1,0,0,2,0,0,0,3,1,0,
    0,2,0,0,1,3,0,3,0,0,0,2,0,3,1,3,0,2,0,0,0,3,1,0,0,2,0,0,0,3,1,0,
    0,0,0,0,1,0,0,3,0,0,0,2,0,0,0,0,0,0,0,0,0,3,1,0,0,2,0,0,0,0,0,0,
    0,0,0,0,1,3,1,3,0,2,0,2,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0]
  else [
    0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,3,1,0,
    0,2,0,2,0,0,0,0,0,0,0,0,1,3,1,3,0,2,0,0,0,0,0,0,0,0,0,0,0,3,1,0,
    0,0,0,0,1,0,0,3,0,0,0,2,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,1,3,1,3,0,2,0,2,0,0,0,0,0,0,0,0,0,3,1,0,0,2,0,0,0,0,0,0,
    0,0,0,2,1,0,0,3,0,0,0,2,1,0,0,3,0,2,0,0,0,3,1,0,0,2,0,0,0,3,1,0,
    0,2,0,2,1,3,0,3,0,0,0,2,1,3,1,3,0,2,0,0,0,3,1,0,0,2,0,0,0,3,1,0,
    0,0,0,0,1,0,0,3,0,0,0,2,0,0,0,0,0,0,0,0,0,3,1,0,0,2,0,0,0,0,0,0,
    0,0,0,0,1,3,1,3,0,2,0,2,0,0,0,0,0,0,0,0,0,3,1,0,0,2,0,0,0,0,0,0]

def witnessTable (p : Fin 2) : List Nat :=
  if p.val=0 then [
    0,0,0,18,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20,0,0,4,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,12,0,0,0,0,0,16,0,0,14,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,26,0,0,10,0,0,0,0,0,0]
  else [
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,11,0,0,1,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,3,0,0,19,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]


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
