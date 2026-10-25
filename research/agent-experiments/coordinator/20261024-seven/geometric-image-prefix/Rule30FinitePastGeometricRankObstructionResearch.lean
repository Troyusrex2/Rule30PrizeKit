import Rule30WeightedSuffixPumpResearch
import Rule30FiniteImageBlackPumpResearch
import Rule30GeometricImageConeResearch
import Rule30FinitePastPrefixRankObstructionResearch
import Mathlib.Tactic.Positivity

/-! A signed finite-image prefix-rank obstruction for EVERY integer geometric
scale >=1. Finite tails, signed costs, phase offsets and additive lower
bounds are retained. This is a proof-method obstruction, not CQ01. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Rule30FinitePastGeometricRankObstructionResearch
open Rule30WeightedWordPumpResearch (score run scale copies score_append scale_ge_one)
open Rule30WeightedSuffixPumpResearch (suffix_loop_nonnegative)
open Rule30VacuumPrefixRankObstructionResearch (transition reader_absorbing Safe13)
open Rule30FiniteLeftWordResearch (Canonical)
open Rule30FiniteImagePumpResearch
  (HasPastOne frontWord backWord currentWord reader_front current_canonical current_safe current_has_past)
open Rule30FiniteImageBlackPumpResearch
  (imageWord frontTail image_canonical image_safe image_has_past)
open Rule30GeometricImageConeResearch
  (whiteA whiteB whiteCharge blackCharge delta delta0 delta1 delta_nonnegative)
open Rule30FinitePastPrefixRankObstructionResearch (startWord middleWord endWord)

def LowerBound (lam : Nat) (C : Nat → Bool → Int) (H B : Int) : Prop :=
  ∀ w,Canonical w → Safe13 w 0 → HasPastOne w → B≤H+score transition C lam 0 w

theorem copies_single (b : Bool) (n : Nat) : copies [b] n=List.replicate n b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [copies,ih,List.replicate_add];rfl

theorem copies_triple (b : Bool) (n : Nat) : copies [b,b,b] n=List.replicate (3*n) b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [copies,ih,Nat.mul_succ,List.replicate_add];rfl

theorem white_tail : backWord false=[true,false,false,true,true] := by decide +kernel

theorem white_cone {lam : Nat} (hlam : 1≤lam) (C : Nat → Bool → Int) (H B : Int)
    (hb : LowerBound lam C H B) : 0≤whiteCharge (lam:Int) (C 1 false) (C 1 true) := by
  have hbound : ∃ K:Int,∀ n,K≤score transition C lam 0
      (frontWord false++copies [false] n++backWord false) := by
    refine ⟨B-H,fun n=>?_⟩
    rw [copies_single]
    have h:=hb _ (current_canonical false n) (current_safe false n) (current_has_past false n)
    change B≤H+score transition C lam 0
      (frontWord false++List.replicate n false++backWord false) at h
    omega
  have h:=suffix_loop_nonnegative transition C hlam 0 1 (frontWord false) [false]
    (backWord false) (reader_front false) reader_absorbing hbound
  rw [white_tail] at h
  have he : score transition C lam 1 [false]+(scale lam [false].length-1)*
      score transition C lam 1 [true,false,false,true,true]=
      whiteCharge (lam:Int) (C 1 false) (C 1 true) := by
    simp only [score,reader_absorbing,List.length_cons,List.length_nil,scale]
    unfold whiteCharge whiteA whiteB
    ring
  rw [he] at h
  exact h

theorem black_cone {lam : Nat} (hlam : 1≤lam) (C : Nat → Bool → Int) (H B : Int)
    (hb : LowerBound lam C H B) : 0≤blackCharge (lam:Int) (C 1 false) (C 1 true) := by
  have hbound : ∃ K:Int,∀ n,K≤score transition C lam 0
      (frontWord true++copies [true,true,true] n++frontTail) := by
    refine ⟨B-H,fun n=>?_⟩
    rw [copies_triple]
    have h:=hb _ (image_canonical n) (image_safe n) (image_has_past n)
    change B≤H+score transition C lam 0
      (frontWord true++List.replicate (3*n) true++frontTail) at h
    omega
  have h:=suffix_loop_nonnegative transition C hlam 0 1 (frontWord true) [true,true,true]
    frontTail (reader_front true) reader_absorbing hbound
  have he : score transition C lam 1 [true,true,true]+(scale lam [true,true,true].length-1)*
      score transition C lam 1 frontTail=
      (lam:Int)^3*((lam:Int)^2+(lam:Int)+1)*blackCharge (lam:Int) (C 1 false) (C 1 true) := by
    simp only [score,reader_absorbing,frontTail,List.length_cons,List.length_nil,scale]
    unfold blackCharge whiteB
    ring
  rw [he] at h
  have hp : 0<(lam:Int) := by omega
  have hfactor : 0<(lam:Int)^3*((lam:Int)^2+(lam:Int)+1) := by positivity
  apply Classical.byContradiction
  intro hn
  have hneg : blackCharge (lam:Int) (C 1 false) (C 1 true)<0 := by omega
  have hm:=Int.mul_lt_mul_of_pos_left hneg hfactor
  simp only [Int.mul_zero] at hm
  omega

def commonWord : List Bool := startWord.take 26
theorem common_length : commonWord.length=26 := by decide +kernel
theorem reader_common : run transition 0 commonWord=1 := by decide +kernel
theorem end_common : endWord.take 26=commonWord := by decide +kernel
theorem start_tail : startWord.drop 26=[false,true,true,true,true,false,true,true] := by decide +kernel
theorem end_tail : endWord.drop 26=[true,true,true,false,false,true,true,true,true,false,true,true] := by decide +kernel

theorem score_tail (lam : Nat) (C : Nat → Bool → Int) (w : List Bool) (hw : w.take 26=commonWord) :
    score transition C lam 0 w=score transition C lam 0 commonWord+
      scale lam 26*score transition C lam 1 (w.drop 26) := by
  have he : commonWord++w.drop 26=w := by rw [←hw];exact List.take_append_drop 26 w
  have h:=score_append transition C lam commonWord (w.drop 26) 0
  rw [he,reader_common,common_length] at h
  exact h

theorem tail_difference (lam : Nat) (C : Nat → Bool → Int) :
    score transition C lam 1 (endWord.drop 26)-score transition C lam 1 (startWord.drop 26)=
      delta (lam:Int) (C 1 false) (C 1 true) := by
  rw [start_tail,end_tail]
  simp only [score,reader_absorbing]
  unfold delta delta0 delta1
  ring

theorem score_difference (lam : Nat) (C : Nat → Bool → Int) :
    score transition C lam 0 endWord=score transition C lam 0 startWord+
      scale lam 26*delta (lam:Int) (C 1 false) (C 1 true) := by
  rw [score_tail lam C endWord end_common,score_tail lam C startWord rfl]
  have h:=tail_difference lam C
  have he : score transition C lam 1 (endWord.drop 26)=
      score transition C lam 1 (startWord.drop 26)+delta (lam:Int) (C 1 false) (C 1 true) := by omega
  rw [he]
  ring

theorem no_integer_geometric_finite_past_prefix_rank {lam : Nat} (hlam : 1≤lam)
    (C0 C1 : Nat → Bool → Int) (H0 H1 B : Int) (hb : LowerBound lam C1 H1 B)
    (hfirst : H0+score transition C0 lam 0 middleWord < H1+score transition C1 lam 0 startWord)
    (hsecond : H1+score transition C1 lam 0 endWord ≤ H0+score transition C0 lam 0 middleWord) :
    False := by
  have hw:=white_cone hlam C1 H1 B hb
  have hk:=black_cone hlam C1 H1 B hb
  have hd:=delta_nonnegative (show 1≤(lam:Int) by omega) (C1 1 false) (C1 1 true) hw hk
  have hs:=scale_ge_one hlam 26
  have hp:=Int.mul_nonneg (show 0≤scale lam 26 by omega) hd
  have he:=score_difference lam C1
  omega

end Rule30FinitePastGeometricRankObstructionResearch
