import Rule30GoldenPackedBitsResearch

/-! A packed-state budget checker. Each new anti-diagonal is normalized to
an integer before it becomes the next state. Projection to the official
reconstruction is proved separately from all finite calculations. -/

namespace Rule30GoldenPackedBudgetResearch
open Rule30GoldenDFAResearch (Golden Flags)
open Rule30GoldenEvenSupportResearch (State Matches code)
open Rule30GoldenBudgetResearch (count)
open Rule30GoldenPackedBitsResearch (pack bits bits_length bits_pack_project)
open Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes (AD)

structure Node where
  R : Nat
  Rm : Nat
  flags : Flags
  used : Nat

def decode (d : Nat) (q : Node) : State := ⟨bits q.R (2*d),bits q.Rm (2*d-1),q.flags⟩

def encode (st : State) (used : Nat) : Node := ⟨pack st.R,pack st.Rm,st.flags,used⟩

def start : Node := ⟨0,0,Rule30GoldenDFAResearch.initial 1,0⟩

noncomputable def child (d : Nat) (q : Node) (e : Bool) : Node :=
  encode (Rule30GoldenEvenSupportResearch.step 1 (fun _ => e.toNat) d (decode d q)) (q.used+e.toNat)

def prune (b : Nat) (q : Node) : Bool := Rule30GoldenDFAResearch.empty q.flags || decide (b<q.used)

noncomputable def dfs (b : Nat) : Nat → Nat → Node → Bool
  | 0,_,q => prune b q
  | fuel+1,d,q => if prune b q then true else
      dfs b fuel (d+1) (child d q false) && dfs b fuel (d+1) (child d q true)

noncomputable def check (b K : Nat) : Bool := dfs b K 0 start

noncomputable def path (u : Nat) : Nat → Node
  | 0 => start
  | d+1 => child d (path u d) (u.testBit d)

theorem AD_length (s : Nat → Bool) (k i n : Nat) : (AD s k i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [AD,List.length_cons,ih]

theorem encode_matches {s : Nat → Bool} {d used : Nat} {st : State}
    (hm : Matches s 0 d st) : Matches s 0 d (decode d (encode st used)) := by
  have hR : st.R.length = 2*d := by
    have h := congrArg List.length hm.1
    simpa only [List.length_map,AD_length] using h
  have hRm : st.Rm.length = 2*d-1 := by
    have h := congrArg List.length hm.2.1
    simpa only [List.length_map,AD_length] using h
  refine ⟨?_,?_,hm.2.2⟩
  · change (bits (pack st.R) (2*d)).map (fun a => a.testBit 0) = _
    have hp := bits_pack_project st.R
    rw [hR] at hp
    exact hp.trans hm.1
  · change (bits (pack st.Rm) (2*d-1)).map (fun a => a.testBit 0) = _
    have hp := bits_pack_project st.Rm
    rw [hRm] at hp
    exact hp.trans hm.2.1

theorem child_matches {s : Nat → Bool} {d : Nat} {q : Node} (hg : Golden s)
    (hm : Matches s 0 d (decode d q)) (hu : q.used=count s d) :
    Matches s 0 (d+1) (decode (d+1) (child d q (code s d))) ∧
      (child d q (code s d)).used = count s (d+1) := by
  have he : ((code s d).toNat).testBit 0 = code s d := by cases code s d <;> rfl
  have h := Rule30GoldenEvenSupportResearch.step_matches (ALL:=1) (p:=0)
    (E:=fun _ => (code s d).toNat) rfl hg he hm
  exact ⟨encode_matches h,by simp only [child,encode,hu,count]⟩

theorem prune_false {b d : Nat} {s : Nat → Bool} {q : Node} (hg : Golden s)
    (hm : Matches s 0 d (decode d q)) (hu : q.used=count s d) (hb : count s d ≤ b) :
    prune b q = false :=
  Rule30GoldenBudgetDFSResearch.prune_false (q:=⟨decode d q,q.used⟩) hg hm hu hb

theorem dfs_sound {b : Nat} {s : Nat → Bool} (hg : Golden s) :
    ∀ fuel d q, Matches s 0 d (decode d q) → q.used=count s d → count s (d+fuel) ≤ b →
      dfs b fuel d q ≠ true := by
  intro fuel
  induction fuel with
  | zero =>
    intro d q hm hu hb hc
    have hp := prune_false hg hm hu (by simpa only [Nat.add_zero] using hb)
    rw [dfs,hp] at hc
    cases hc
  | succ fuel ih =>
    intro d q hm hu hb hc
    have hd : count s d ≤ b := Nat.le_trans (Rule30GoldenBudgetDFSResearch.count_mono s (by omega)) hb
    have hp := prune_false hg hm hu hd
    rw [dfs,hp] at hc
    have hboth : dfs b fuel (d+1) (child d q false)=true ∧ dfs b fuel (d+1) (child d q true)=true := by simpa using hc
    have hchild := child_matches hg hm hu
    have hactual : dfs b fuel (d+1) (child d q (code s d))=true := by
      cases he : code s d
      · simpa only [he] using hboth.1
      · simpa only [he] using hboth.2
    apply ih (d+1) (child d q (code s d)) hchild.1 hchild.2 _ hactual
    simpa only [show d+1+fuel=d+(fuel+1) by omega] using hb

theorem no_golden_of_check {b K : Nat} (hc : check b K=true) (s : Nat → Bool)
    (hb : count s K ≤ b) : ¬ Golden s := by
  intro hg
  exact dfs_sound hg K 0 start (Rule30GoldenEvenSupportResearch.start_matches rfl s)
    rfl (by simpa using hb) hc

theorem dfs_of_prune {b fuel d : Nat} {q : Node} (h : prune b q=true) : dfs b fuel d q=true := by
  cases fuel with
  | zero => exact h
  | succ fuel => rw [dfs,h];rfl

theorem dfs_of_children {b fuel d : Nat} {q : Node}
    (h0 : dfs b fuel (d+1) (child d q false)=true)
    (h1 : dfs b fuel (d+1) (child d q true)=true) : dfs b (fuel+1) d q=true := by
  rw [dfs]
  cases h : prune b q
  · simp only [h,Bool.false_eq_true,↓reduceIte,h0,h1,Bool.and_self]
  · rfl

end Rule30GoldenPackedBudgetResearch
