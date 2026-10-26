module
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-! A Golden stream obstruction, not an achievable finite-right-half witness.
The full temporal-profile cycle proves the spatial period for all depths.
No claim about CQ01, a finite R realizing this stream, or Prize P1 is made. -/
/- The candidate is credited to CoinAIlyzer wiki's round-three response.
The finite-profile formalization and count argument are by Troy Lowry with Codex. -/
@[expose] public section
namespace Rule30Slip94Research
open Ruliology.CellularAutomata
open Rule30ZeroBoundary
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def parity (n : Nat) : Bool := decide (n%2=1)
def stream (s : Nat) : Bool := parity (s + if 94 ≤ s then 1 else 0)

theorem parity_succ (n : Nat) : parity (n+1)=!parity n := by
  unfold parity
  by_cases h : n%2=0
  · have hn : n%2≠1 := by omega
    have hs : (n+1)%2=1 := by omega
    simp [hn,hs]
  · have hn : n%2=1 := by omega
    have hs : (n+1)%2≠1 := by omega
    simp [hn,hs]

theorem stream_next (s : Nat) (hs : s≠93) : stream (s+1)=!stream s := by
  by_cases h : 94 ≤ s
  · simp only [stream,if_pos h,if_pos (show 94 ≤ s+1 by omega)]
    exact parity_succ (s+1)
  · simp only [stream,if_neg h,if_neg (show ¬94 ≤ s+1 by omega),Nat.add_zero]
    exact parity_succ s

theorem stream_golden : (∀ s, (stream s || stream (s+1))=true) ∧
    (∀ s, (stream s && stream (s+1) && stream (s+2))=false) := by
  constructor <;> intro s <;> by_cases hs : s=93
  · subst s; decide +kernel
  · rw [stream_next s hs]; cases stream s <;> rfl
  · subst s; decide +kernel
  · rw [stream_next s hs]; cases stream s <;> rfl

def timeAt (t : Nat) : Nat := if t<188 then t else 188+(t-188)%4
def timeNext (i : Nat) : Nat := if i=191 then 188 else i+1
def spaceAt (d : Nat) : Nat := if d<906 then d else 906+(d-906)%28
def spaceNext (d : Nat) : Nat := if d=933 then 906 else d+1
def shiftWord (c : Nat) : Nat :=
  ((c >>> 1)%2^191) ||| (if c.testBit 188 then 2^191 else 0)
def nextWord (a b : Nat) : Nat := (shiftWord b ^^^ (b ||| a))%2^192

-- COLUMN_WORDS_INSERTED_HERE

def word (d : Nat) : Nat := columns.getD d 0
def model (d t : Nat) : Bool := (word (spaceAt d)).testBit (timeAt t)
def left (d : Nat) : Bool := model d 0

theorem timeAt_lt (t : Nat) : timeAt t<192 := by unfold timeAt; split <;> omega
theorem spaceAt_lt (d : Nat) : spaceAt d<934 := by unfold spaceAt; split <;> omega
theorem timeAt_succ (t : Nat) : timeAt (t+1)=timeNext (timeAt t) := by
  unfold timeAt timeNext
  split <;> split <;> split <;> omega
theorem spaceAt_succ (d : Nat) : spaceAt (d+1)=spaceNext (spaceAt d) := by
  unfold spaceAt spaceNext
  split <;> split <;> split <;> omega

theorem injected_bit (b : Bool) (i : Nat) :
    (if b then 2^191 else 0).testBit i=(b && decide (191=i)) := by
  cases b
  · simp only [Bool.false_eq_true,ite_false,Nat.zero_testBit,Bool.false_and]
  · exact Nat.testBit_two_pow

theorem shift_bit (c i : Nat) (hi : i<192) :
    (shiftWord c).testBit i=c.testBit (timeNext i) := by
  unfold shiftWord
  rw [Nat.testBit_or,Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,injected_bit]
  by_cases hlast : i=191
  · subst i; simp [timeNext]
  · have hsmall : i<191 := by omega
    have hne : (191 : Nat)≠i := by omega
    simp [timeNext,hlast,hsmall,hne,Nat.add_comm]

theorem next_bit (a b i : Nat) (hi : i<192) :
    (nextWord a b).testBit i=
      xor (b.testBit (timeNext i)) (b.testBit i || a.testBit i) := by
  simp only [nextWord,Nat.testBit_mod_two_pow,hi,decide_true,Bool.true_and,
    Nat.testBit_xor,Nat.testBit_or]
  rw [shift_bit b i hi]

def blockOK (b : Nat) : Bool := (List.range 32).all fun i =>
  let d := 32*b+i
  if d<934 then word (spaceNext (spaceNext d)) == nextWord (word d) (word (spaceNext d)) else true

-- BLOCK_CHECKS_INSERTED_HERE

theorem table_word_rule (d : Nat) (hd : d<934) :
    word (spaceNext (spaceNext d))=nextWord (word d) (word (spaceNext d)) := by
  have checked := all_blocks (d/32) (by omega)
  have h := List.all_eq_true.mp checked (d%32) (List.mem_range.mpr (by omega))
  have he : 32*(d/32)+d%32=d := by omega
  simpa only [he,if_pos hd,beq_iff_eq] using h

theorem model_rule (d t : Nat) : model (d+2) t=
    xor (model (d+1) (t+1)) (model (d+1) t || model d t) := by
  unfold model
  rw [show d+2=(d+1)+1 by omega,spaceAt_succ,spaceAt_succ,timeAt_succ]
  rw [table_word_rule _ (spaceAt_lt d)]
  exact next_bit _ _ _ (timeAt_lt t)

theorem alt_time_fold (t : Nat) : alt stream (timeAt t)=alt stream t := by
  by_cases ht : t<188
  · simp [timeAt,ht]
  · have hfold : 188 ≤ timeAt t := by unfold timeAt; split <;> omega
    have h4 : timeAt t%4=t%4 := by unfold timeAt; split <;> omega
    have h2 : timeAt t%2=t%2 := by omega
    have hh : (timeAt t/2)%2=(t/2)%2 := by omega
    simp [alt,stream,parity,if_pos (show 94 ≤ t/2 by omega),
      if_pos (show 94 ≤ timeAt t/2 by omega),h2,Nat.add_mod,hh]

theorem model_zero (t : Nat) : model 0 t=false := by
  have hz : word 0=0 := by decide +kernel
  simp [model,spaceAt,hz]

theorem model_one (t : Nat) : model 1 t=alt stream t := by
  have checked : (List.range 192).all (fun t => (word 1).testBit t == alt stream t)=true := by
    decide +kernel
  have h := beq_iff_eq.mp (List.all_eq_true.mp checked (timeAt t) (List.mem_range.mpr (timeAt_lt t)))
  simpa [model,spaceAt,alt_time_fold] using h

theorem recon_model_pair (d : Nat) :
    (∀ t, recon (alt stream) d t=model d t) ∧
    (∀ t, recon (alt stream) (d+1) t=model (d+1) t) := by
  induction d with
  | zero => exact ⟨fun t => (model_zero t).symm,fun t => (model_one t).symm⟩
  | succ d ih =>
    refine ⟨ih.2,fun t => ?_⟩
    rw [recon,ih.2 (t+1),ih.2 t,ih.1 t]
    exact (model_rule d t).symm

theorem theta_left : Theta stream=left := by
  funext d
  exact (recon_model_pair d).1 0

theorem theta_periodic_28 (d : Nat) (hd : 906 ≤ d) : Theta stream (d+28)=Theta stream d := by
  rw [theta_left]
  have he : spaceAt (d+28)=spaceAt d := by unfold spaceAt; split <;> split <;> omega
  simp only [left,model,he]

def ones (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => ones f n + if f n then 1 else 0
def zeros (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => zeros f n + if f n then 0 else 1

theorem ones_add (f : Nat → Bool) (a n : Nat) :
    ones f (a+n)=ones f a+ones (fun j => f (a+j)) n := by
  induction n with
  | zero => simp [ones]
  | succ n ih => simp [ones,ih,Nat.add_assoc]

theorem zeros_add (f : Nat → Bool) (a n : Nat) :
    zeros f (a+n)=zeros f a+zeros (fun j => f (a+j)) n := by
  induction n with
  | zero => simp [zeros]
  | succ n ih => simp [zeros,ih,Nat.add_assoc]

theorem ones_le (f : Nat → Bool) (n : Nat) : ones f n≤n := by
  induction n with
  | zero => simp [ones]
  | succ n ih => simp only [ones]; split <;> omega

theorem left_align (k j : Nat) : left (907+28*k+j)=left (907+j) := by
  have h : spaceAt (907+28*k+j)=spaceAt (907+j) := by
    unfold spaceAt; split <;> split <;> omega
  simp only [left,model,h]

theorem stream_align (k j : Nat) : stream (453+14*k+j)=stream (453+j) := by
  simp only [stream,if_pos (show 94 ≤ 453+14*k+j by omega),
    if_pos (show 94 ≤ 453+j by omega),parity]
  have h : (453+14*k+j+1)%2=(453+j+1)%2 := by omega
  rw [h]

theorem ones_tail_count (k : Nat) : ones left (907+28*k)=ones left 907+6*k := by
  have block : ones (fun j => left (907+j)) 28=6 := by decide +kernel
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 907+28*(k+1)=(907+28*k)+28 by omega,ones_add,ih]
    have hf : (fun j => left (907+28*k+j))=(fun j => left (907+j)) := funext (left_align k)
    rw [hf,block]
    omega

theorem zeros_count (k : Nat) : zeros stream (453+14*k)=226+7*k := by
  have base : zeros stream 453=226 := by decide +kernel
  have block : zeros (fun j => stream (453+j)) 14=7 := by decide +kernel
  induction k with
  | zero => simpa using base
  | succ k ih =>
    rw [show 453+14*(k+1)=(453+14*k)+14 by omega,zeros_add,ih]
    have hf : (fun j => stream (453+14*k+j))=(fun j => stream (453+j)) := funext (stream_align k)
    rw [hf,block]
    omega

def StreamCharge (C B : Nat) (f : Nat → Bool) : Prop :=
  ∀ n, 5*zeros f n ≤ n+B+C*ones (Theta f) (2*n+1)

/-- Golden alone cannot prove a coefficient-three charge with any allowance.
No finite right half realizing the stream has been exhibited. -/
theorem golden_stream_charge_three_false (B : Nat) : ¬StreamCharge 3 B stream := by
  intro hc
  let k := B+1000
  have h := hc (453+14*k)
  rw [zeros_count,show 2*(453+14*k)+1=907+28*k by omega,theta_left,ones_tail_count] at h
  have bound := ones_le left 907
  dsimp [k] at h
  omega

end Rule30Slip94Research
