import Rule30FinitePastGeometricRankObstructionResearch

/-! Uniform over every reader that absorbs after the specified 26-cell
period-seven prefix. The reader need not have a fixed number of states.
Actual finite images and every integer geometric scale >=1 are retained. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Rule30GenericAbsorbingPrefixBarrierResearch
open Rule30WeightedWordPumpResearch (score run scale copies score_append run_append run_absorbing scale_ge_one)
open Rule30WeightedSuffixPumpResearch (suffix_loop_nonnegative)
open Rule30VacuumPrefixRankObstructionResearch (Safe13)
open Rule30FiniteLeftWordResearch (Canonical)
open Rule30FiniteImagePumpResearch
  (HasPastOne frontWord backWord currentWord current_canonical current_safe current_has_past)
open Rule30FiniteImageBlackPumpResearch (frontTail image_canonical image_safe image_has_past)
open Rule30GeometricImageConeResearch
  (whiteA whiteB whiteCharge blackCharge delta delta0 delta1 delta_nonnegative)
open Rule30FinitePastPrefixRankObstructionResearch (startWord middleWord endWord)
open Rule30FinitePastGeometricRankObstructionResearch
  (commonWord common_length end_common start_tail end_tail copies_single copies_triple white_tail)

def LowerBound (T : Nat → Bool → Nat) (p lam : Nat) (C : Nat → Bool → Int) (H B : Int) : Prop :=
  ∀ w,Canonical w → Safe13 w 0 → HasPastOne w → B≤H+score T C lam p w

theorem front_common (b : Bool) : (frontWord b).take 26=commonWord := by
  cases b <;> decide +kernel

theorem run_front (T : Nat → Bool → Nat) (p s : Nat) (hs : ∀ a,T s a=s)
    (hw : run T p commonWord=s) (b : Bool) : run T p (frontWord b)=s := by
  have he:=List.take_append_drop 26 (frontWord b)
  calc
    run T p (frontWord b)=run T p ((frontWord b).take 26++(frontWord b).drop 26) :=
      congrArg (run T p) he.symm
    _=run T (run T p commonWord) ((frontWord b).drop 26) := by rw [run_append,front_common]
    _=s := by rw [hw];exact run_absorbing T s hs _

theorem white_cone (T : Nat → Bool → Nat) (p s : Nat) (hs : ∀ a,T s a=s)
    (hw : run T p commonWord=s) {lam : Nat} (hlam : 1≤lam)
    (C : Nat → Bool → Int) (H B : Int) (hb : LowerBound T p lam C H B) :
    0≤whiteCharge (lam:Int) (C s false) (C s true) := by
  have hbound : ∃ K:Int,∀ n,K≤score T C lam p
      (frontWord false++copies [false] n++backWord false) := by
    refine ⟨B-H,fun n=>?_⟩
    rw [copies_single]
    have h:=hb _ (current_canonical false n) (current_safe false n) (current_has_past false n)
    change B≤H+score T C lam p (frontWord false++List.replicate n false++backWord false) at h
    omega
  have h:=suffix_loop_nonnegative T C hlam p s (frontWord false) [false] (backWord false)
    (run_front T p s hs hw false) hs hbound
  rw [white_tail] at h
  have he : score T C lam s [false]+(scale lam [false].length-1)*
      score T C lam s [true,false,false,true,true]=whiteCharge (lam:Int) (C s false) (C s true) := by
    simp only [score,hs,List.length_cons,List.length_nil,scale]
    unfold whiteCharge whiteA whiteB
    ring
  rw [he] at h
  exact h

theorem black_cone (T : Nat → Bool → Nat) (p s : Nat) (hs : ∀ a,T s a=s)
    (hw : run T p commonWord=s) {lam : Nat} (hlam : 1≤lam)
    (C : Nat → Bool → Int) (H B : Int) (hb : LowerBound T p lam C H B) :
    0≤blackCharge (lam:Int) (C s false) (C s true) := by
  have hbound : ∃ K:Int,∀ n,K≤score T C lam p
      (frontWord true++copies [true,true,true] n++frontTail) := by
    refine ⟨B-H,fun n=>?_⟩
    rw [copies_triple]
    have h:=hb _ (image_canonical n) (image_safe n) (image_has_past n)
    change B≤H+score T C lam p (frontWord true++List.replicate (3*n) true++frontTail) at h
    omega
  have h:=suffix_loop_nonnegative T C hlam p s (frontWord true) [true,true,true] frontTail
    (run_front T p s hs hw true) hs hbound
  have he : score T C lam s [true,true,true]+(scale lam [true,true,true].length-1)*
      score T C lam s frontTail=
      (lam:Int)^3*((lam:Int)^2+(lam:Int)+1)*blackCharge (lam:Int) (C s false) (C s true) := by
    simp only [score,hs,frontTail,List.length_cons,List.length_nil,scale]
    unfold blackCharge whiteB
    ring
  rw [he] at h
  have hp : 0<(lam:Int) := by omega
  have hfactor : 0<(lam:Int)^3*((lam:Int)^2+(lam:Int)+1) := by positivity
  apply Classical.byContradiction
  intro hn
  have hneg : blackCharge (lam:Int) (C s false) (C s true)<0 := by omega
  have hm:=Int.mul_lt_mul_of_pos_left hneg hfactor
  simp only [Int.mul_zero] at hm
  omega

theorem score_tail (T : Nat → Bool → Nat) (p s : Nat) (hw : run T p commonWord=s)
    (lam : Nat) (C : Nat → Bool → Int) (w : List Bool) (hprefix : w.take 26=commonWord) :
    score T C lam p w=score T C lam p commonWord+scale lam 26*score T C lam s (w.drop 26) := by
  have he : commonWord++w.drop 26=w := by rw [←hprefix];exact List.take_append_drop 26 w
  have h:=score_append T C lam commonWord (w.drop 26) p
  rw [he,hw,common_length] at h
  exact h

theorem tail_difference (T : Nat → Bool → Nat) (s : Nat) (hs : ∀ a,T s a=s)
    (lam : Nat) (C : Nat → Bool → Int) :
    score T C lam s (endWord.drop 26)-score T C lam s (startWord.drop 26)=
      delta (lam:Int) (C s false) (C s true) := by
  rw [start_tail,end_tail]
  simp only [score,hs]
  unfold delta delta0 delta1
  ring

theorem score_difference (T : Nat → Bool → Nat) (p s : Nat) (hs : ∀ a,T s a=s)
    (hw : run T p commonWord=s) (lam : Nat) (C : Nat → Bool → Int) :
    score T C lam p endWord=score T C lam p startWord+
      scale lam 26*delta (lam:Int) (C s false) (C s true) := by
  rw [score_tail T p s hw lam C endWord end_common,score_tail T p s hw lam C startWord rfl]
  have h:=tail_difference T s hs lam C
  have he : score T C lam s (endWord.drop 26)=
      score T C lam s (startWord.drop 26)+delta (lam:Int) (C s false) (C s true) := by omega
  rw [he]
  ring

theorem no_absorbing_prefix_geometric_rank (T : Nat → Bool → Nat) (p s : Nat)
    (hs : ∀ a,T s a=s) (hw : run T p commonWord=s) {lam : Nat} (hlam : 1≤lam)
    (C0 C1 : Nat → Bool → Int) (H0 H1 B : Int) (hb : LowerBound T p lam C1 H1 B)
    (hfirst : H0+score T C0 lam p middleWord < H1+score T C1 lam p startWord)
    (hsecond : H1+score T C1 lam p endWord ≤ H0+score T C0 lam p middleWord) : False := by
  have hwc:=white_cone T p s hs hw hlam C1 H1 B hb
  have hkc:=black_cone T p s hs hw hlam C1 H1 B hb
  have hd:=delta_nonnegative (show 1≤(lam:Int) by omega) (C1 s false) (C1 s true) hwc hkc
  have hscale:=scale_ge_one hlam 26
  have hp:=Int.mul_nonneg (show 0≤scale lam 26 by omega) hd
  have he:=score_difference T p s hs hw lam C1
  omega

theorem specified_reader_instance {lam : Nat} (hlam : 1≤lam)
    (C0 C1 : Nat → Bool → Int) (H0 H1 B : Int)
    (hb : Rule30FinitePastGeometricRankObstructionResearch.LowerBound lam C1 H1 B)
    (hfirst : H0+score Rule30VacuumPrefixRankObstructionResearch.transition C0 lam 0 middleWord <
      H1+score Rule30VacuumPrefixRankObstructionResearch.transition C1 lam 0 startWord)
    (hsecond : H1+score Rule30VacuumPrefixRankObstructionResearch.transition C1 lam 0 endWord ≤
      H0+score Rule30VacuumPrefixRankObstructionResearch.transition C0 lam 0 middleWord) : False :=
  no_absorbing_prefix_geometric_rank _ 0 1 Rule30VacuumPrefixRankObstructionResearch.reader_absorbing
    Rule30FinitePastGeometricRankObstructionResearch.reader_common hlam C0 C1 H0 H1 B hb hfirst hsecond

end Rule30GenericAbsorbingPrefixBarrierResearch
