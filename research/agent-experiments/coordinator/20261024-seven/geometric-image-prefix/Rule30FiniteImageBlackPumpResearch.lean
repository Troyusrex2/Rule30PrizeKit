import Rule30FiniteImagePumpResearch

/-! A second all-black finite-image pump, with full front suffix 111011.
The extra final predecessor cell changes the geometric tail constraint. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Rule30FiniteImageBlackPumpResearch
open Ruliology.CellularAutomata.Rule30ZeroBoundary
open Rule30FiniteLeftWordResearch (row next row_support zrow_prefix getD_append_prefix getD_large)
open Rule30FiniteWordAppendResearch (getD_append_right row_append_prefix row_middle row_tail_shift)
open Rule30FiniteImagePumpResearch
  (predecessor base span frontWord prefix_length predecessor_zero_row predecessor_shift
    predecessor_wall predecessor_head predecessor_free current_bulk two_local front_left HasPastOne)

def extended (n d : Nat) : Bool := predecessor true n d || decide (d=38+3*n)
def frontTail : List Bool := [true,true,true,false,true,true]
def imageWord (n : Nat) : List Bool := frontWord true++List.replicate (3*n) true++frontTail

theorem row_snoc_true (w : List Bool) (d : Nat) :
    row (w++[true]) d=(row w d || decide (d=w.length+1)) := by
  cases d with
  | zero => simp [row]
  | succ i =>
    change (w++[true]).getD i false=(w.getD i false || decide (i+1=w.length+1))
    by_cases hi : i<w.length
    · rw [getD_append_prefix w [true] i hi]
      simp [show i≠w.length by omega]
    · have hle : w.length≤i := by omega
      rw [getD_append_right _ _ i hle,getD_large w i hle]
      by_cases he : i=w.length
      · subst i;simp
      · rw [getD_large [true] (i-w.length) (by simp;omega)]
        simp [he]

theorem extended_zero_row : extended 0=row (base true++[true,true]) := by
  funext d
  calc
    extended 0 d=(row (base true++[true]) d || decide (d=38)) := by
      rw [extended,predecessor_zero_row]
    _=row (base true++[true,true]) d := by
      have h:=row_snoc_true (base true++[true]) d
      simpa [Rule30FiniteImagePumpResearch.base_length,List.append_assoc] using h.symm

theorem extended_wall (n : Nat) : extended n 0=false := by
  simp [extended,predecessor_wall,show (0:Nat)≠38+3*n by omega]

theorem extended_before (n d : Nat) (hd : d≤36+3*n) : extended n d=predecessor true n d := by
  simp [extended,show d≠38+3*n by omega]

theorem extended_shift (n i : Nat) (hi : 33≤i) : extended n (i+3*n)=extended 0 i := by
  have h:=predecessor_shift true n i hi
  change predecessor true n (i+3*n)=predecessor true 0 i at h
  simp only [extended,h,Nat.mul_zero,Nat.add_zero,Nat.add_right_cancel_iff]

theorem extended_current_shift (n k : Nat) (hk : 33≤k) :
    zrow (extended n) 2 (k+2+3*n)=zrow (extended 0) 2 (k+2) := by
  rw [show k+2+3*n=(k+3*n)+2 by omega,two_local (extended_wall n),two_local (extended_wall 0)]
  have h (j : Nat) (hj : j≤4) : extended n (k+3*n+j)=extended 0 (k+j) := by
    rw [show k+3*n+j=(k+j)+3*n by omega]
    exact extended_shift n (k+j) (by omega)
  rw [show k+3*n=k+3*n+0 by omega,h 0 (by omega),h 1 (by omega),h 2 (by omega),
    h 3 (by omega),h 4 (by omega)]
  rfl

theorem zero_word : frontWord true++frontTail=next (base true++[true,true]) := by decide +kernel
theorem zero_physical : row (frontWord true++frontTail)=zrow (extended 0) 2 := by
  rw [zero_word,Rule30FiniteLeftWordResearch.row_next,extended_zero_row]

theorem extended_current_prefix (n d : Nat) (hd : d≤34) :
    zrow (extended n) 2 d=zrow (extended 0) 2 d := by
  apply zrow_prefix 36 (t:=2) (d:=d) (h:=?_) (by omega)
  intro i hi
  rw [extended_before n i (by omega),extended_before 0 i (by omega)]
  simp only [predecessor,hi,↓reduceIte]

theorem extended_current_bulk (n d : Nat) (h0 : 35≤d) (h1 : d≤34+3*n) :
    zrow (extended n) 2 d=true := by
  rw [zrow_prefix (36+3*n) (fun i hi=>extended_before n i hi) 2 d (by omega)]
  exact current_bulk true n d h0 h1

theorem image_physical (n : Nat) : row (imageWord n)=zrow (extended n) 2 := by
  funext d
  by_cases h0 : d≤34
  · calc
      row (imageWord n) d=row (frontWord true) d := by
        unfold imageWord
        rw [List.append_assoc,row_append_prefix _ _ d (by rw [prefix_length];omega)]
      _=row (frontWord true++frontTail) d := (row_append_prefix _ _ d (by rw [prefix_length];omega)).symm
      _=zrow (extended 0) 2 d := congrFun zero_physical d
      _=zrow (extended n) 2 d := (extended_current_prefix n d h0).symm
  · by_cases h1 : d≤34+3*n
    · rw [extended_current_bulk n d (by omega) h1]
      exact row_middle _ _ true _ d (by rw [prefix_length];omega) (by rw [prefix_length];omega)
    · have htail : row (imageWord n) d=row (frontWord true++frontTail) (d-3*n) :=
        row_tail_shift _ _ true _ d (by rw [prefix_length];omega)
      rw [htail,zero_physical]
      let k:=d-3*n-2
      have h:=extended_current_shift n k (by dsimp only [k];omega)
      have hl : k+2+3*n=d := by dsimp only [k];omega
      have hr : k+2=d-3*n := by dsimp only [k];omega
      rw [hl,hr] at h
      exact h.symm

theorem extended_finite (n : Nat) : FinSupp (extended n) := by
  refine ⟨38+3*n,fun d hd=>?_⟩
  simp [extended,predecessor,span,show ¬ d≤36 by omega,show ¬ d≤36+3*n by omega,
    show d≠37+3*n by omega,show d≠38+3*n by omega]

theorem extended_head (n : Nat) : extended n 1=true := by
  rw [extended_before n 1 (by omega)]
  exact predecessor_head true n

theorem extended_free (n : Nat) : zrow (extended n) 1 1=true := by
  rw [zrow_prefix 2 (fun d hd=>extended_before n d (by omega)) 1 1 (by omega)]
  exact predecessor_free true n

theorem image_has_past (n : Nat) : HasPastOne (imageWord n) :=
  ⟨extended n,extended_finite n,extended_head n,extended_free n,image_physical n⟩

theorem image_left (n d : Nat) (hd : d≤30) :
    row (imageWord n) d=Rule30CriticalChargeOneCoreResearch.left d := by
  unfold imageWord
  rw [List.append_assoc,row_append_prefix _ _ d (by rw [prefix_length];omega)]
  exact front_left true d hd

theorem image_safe (n : Nat) : Rule30VacuumPrefixRankObstructionResearch.Safe13 (imageWord n) 0 := by
  have hp:=zrow_prefix 30 (image_left n)
  constructor
  · intro i hi
    rw [hp (2*i) 1 (by omega)]
    exact Rule30CriticalChargeOneCoreResearch.left_inX i
  · intro i hi
    rw [hp (2*i+1) 1 (by omega)]
    simpa only [Nat.add_zero] using Rule30CriticalChargeOneCoreResearch.left_free i

theorem image_canonical (n : Nat) : Rule30FiniteLeftWordResearch.Canonical (imageWord n) := by
  constructor
  · rfl
  · unfold imageWord
    simp only [List.reverse_append]
    rfl

end Rule30FiniteImageBlackPumpResearch
