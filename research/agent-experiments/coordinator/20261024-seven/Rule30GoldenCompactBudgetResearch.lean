import Rule30GoldenCompactCodecResearch
import Rule30GoldenPackedBudgetResearch

/-! A whole-state integer encoding for the finite budget checker. Soundness
is proved by projection to the official reconstruction; no all-budget
termination assertion is assumed. -/

namespace Rule30GoldenCompactBudgetResearch
open Rule30GoldenDFAResearch (Golden Flags)
open Rule30GoldenEvenSupportResearch (State Matches code)
open Rule30GoldenBudgetResearch (count)
open Rule30GoldenPackedBitsResearch (pack bits bits_pack_project)

def flagsPack (g : Flags) : Nat := pack [g.c0,g.c1,g.c2,g.c3,g.c4,g.c5]

def flagsDecode (f : Nat) : Flags :=
  ⟨(f.testBit 0).toNat,(f.testBit 1).toNat,(f.testBit 2).toNat,
   (f.testBit 3).toNat,(f.testBit 4).toNat,(f.testBit 5).toNat⟩

theorem flagsDecode_at (f r : Nat) (hr : r<6) :
    ((flagsDecode f).at r).testBit 0 = f.testBit r := by
  rcases (show r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases h : f.testBit _ <;> simp_all [flagsDecode,Flags.at]

theorem flagsPack_at (g : Flags) (r : Nat) (hr : r<6) :
    (flagsPack g).testBit r = (g.at r).testBit 0 := by
  have h := Rule30GoldenPackedBitsResearch.pack_testBit [g.c0,g.c1,g.c2,g.c3,g.c4,g.c5] r
    (by simpa using hr)
  rcases (show r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa only [flagsPack,Flags.at,List.getD_cons_zero,List.getD_cons_succ] using h

def encode (d : Nat) (st : State) (used : Nat) : Nat :=
  Rule30GoldenCompactCodecResearch.encode (2*d) (2*d-1) (pack st.R) (pack st.Rm)
    (flagsPack st.flags) used

def decode (d x : Nat) : State :=
  ⟨bits (Rule30GoldenCompactCodecResearch.getR x (2*d)) (2*d),
   bits (Rule30GoldenCompactCodecResearch.getRm x (2*d) (2*d-1)) (2*d-1),
   flagsDecode (Rule30GoldenCompactCodecResearch.getFlags x (2*d) (2*d-1))⟩

def cost (d x : Nat) : Nat := Rule30GoldenCompactCodecResearch.getUsed x (2*d) (2*d-1)

def start : Nat := 32

noncomputable def child (d x : Nat) (e : Bool) : Nat :=
  encode (d+1) (Rule30GoldenEvenSupportResearch.step 1 (fun _ => e.toNat) d (decode d x))
    (cost d x+e.toNat)

def prune (b d x : Nat) : Bool := Rule30GoldenDFAResearch.empty (decode d x).flags || decide (b<cost d x)

noncomputable def dfs (b : Nat) : Nat → Nat → Nat → Bool
  | 0,d,x => prune b d x
  | fuel+1,d,x => if prune b d x then true else
      dfs b fuel (d+1) (child d x false) && dfs b fuel (d+1) (child d x true)

noncomputable def check (b K : Nat) : Bool := dfs b K 0 start

noncomputable def path (u : Nat) : Nat → Nat
  | 0 => start
  | d+1 => child d (path u d) (u.testBit d)

theorem cost_encode (d : Nat) (st : State) (used : Nat) : cost d (encode d st used)=used :=
  Rule30GoldenCompactCodecResearch.getUsed_encode _ _ _ _ _ _

theorem encode_matches {s : Nat → Bool} {d used : Nat} {st : State}
    (hg : Golden s) (hm : Matches s 0 d st) : Matches s 0 d (decode d (encode d st used)) := by
  have hR : st.R.length = 2*d := by
    have h := congrArg List.length hm.1
    simpa only [List.length_map,Rule30GoldenPackedBudgetResearch.AD_length] using h
  have hRm : st.Rm.length = 2*d-1 := by
    have h := congrArg List.length hm.2.1
    simpa only [List.length_map,Rule30GoldenPackedBudgetResearch.AD_length] using h
  refine ⟨?_,?_,?_⟩
  · change (bits _ (2*d)).map (fun a => a.testBit 0) = _
    unfold encode
    rw [Rule30GoldenCompactCodecResearch.bits_congr (fun i hi =>
      Rule30GoldenCompactCodecResearch.getR_bit _ _ _ _ _ _ i hi)]
    have hp := bits_pack_project st.R
    rw [hR] at hp
    exact hp.trans hm.1
  · change (bits _ (2*d-1)).map (fun a => a.testBit 0) = _
    unfold encode
    rw [Rule30GoldenCompactCodecResearch.bits_congr (fun i hi =>
      Rule30GoldenCompactCodecResearch.getRm_bit _ _ _ _ _ _ i hi)]
    have hp := bits_pack_project st.Rm
    rw [hRm] at hp
    exact hp.trans hm.2.1
  · change ((flagsDecode _).at (Rule30GoldenDFAResearch.run s d)).testBit 0 = true
    rw [flagsDecode_at _ _ (Rule30GoldenDFAResearch.run_lt hg d)]
    unfold encode
    rw [Rule30GoldenCompactCodecResearch.getFlags_bit _ _ _ _ _ _ _ (Rule30GoldenDFAResearch.run_lt hg d)]
    rw [flagsPack_at _ _ (Rule30GoldenDFAResearch.run_lt hg d)]
    exact hm.2.2

theorem child_matches {s : Nat → Bool} {d q : Nat} (hg : Golden s)
    (hm : Matches s 0 d (decode d q)) (hu : cost d q=count s d) :
    Matches s 0 (d+1) (decode (d+1) (child d q (code s d))) ∧
      cost (d+1) (child d q (code s d)) = count s (d+1) := by
  have he : ((code s d).toNat).testBit 0 = code s d := by cases code s d <;> rfl
  have h := Rule30GoldenEvenSupportResearch.step_matches (ALL:=1) (p:=0)
    (E:=fun _ => (code s d).toNat) rfl hg he hm
  exact ⟨encode_matches hg h,by simp only [child,cost_encode,hu,count]⟩

theorem prune_false {b d q : Nat} {s : Nat → Bool} (hg : Golden s)
    (hm : Matches s 0 d (decode d q)) (hu : cost d q=count s d) (hb : count s d ≤ b) :
    prune b d q = false :=
  Rule30GoldenBudgetDFSResearch.prune_false (q:=⟨decode d q,cost d q⟩) hg hm hu hb

theorem dfs_sound {b : Nat} {s : Nat → Bool} (hg : Golden s) :
    ∀ fuel d q, Matches s 0 d (decode d q) → cost d q=count s d → count s (d+fuel) ≤ b →
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

theorem dfs_of_prune {b fuel d q : Nat} (h : prune b d q=true) : dfs b fuel d q=true := by
  cases fuel with
  | zero => exact h
  | succ fuel => rw [dfs,h];rfl

theorem dfs_of_children {b fuel d q : Nat}
    (h0 : dfs b fuel (d+1) (child d q false)=true)
    (h1 : dfs b fuel (d+1) (child d q true)=true) : dfs b (fuel+1) d q=true := by
  rw [dfs]
  cases h : prune b d q
  · simp only [h,Bool.false_eq_true,↓reduceIte,h0,h1,Bool.and_self]
  · rfl

end Rule30GoldenCompactBudgetResearch
