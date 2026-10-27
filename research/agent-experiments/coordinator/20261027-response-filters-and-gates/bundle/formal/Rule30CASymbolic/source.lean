module
public import Rule30BoolPolynomial
public import Rule30CAObserverResearch

/-! Symbolic CA identities, certified in the Boolean polynomial ring.
Coefficient checks are followed by the general evaluation theorem. -/
@[expose] public section
namespace Rule30CASymbolic
open Rule30BoolPolynomial
open Rule30CAObserverResearch
set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

abbrev Row := Nat → Bool
def rstep (x : Row) : Row := rowStep true false (rowStep false false x)
def rit (x : Row) : Nat → Row
  | 0 => x
  | t+1 => rstep (rit x t)

def bstep (x : Row) : Row
  | 0 => !x 0
  | 1 => xor true (xor (x 0) (x 1))
  | 2 => x 2
  | 3 => xor (x 3) (x 0 && !(xor (x 1) (x 2)))
  | 4 => xor (x 4) ((x 0 || x 1) && !(xor (x 2) (x 3)))
  | 5 => xor (x 5) ((x 1 || x 2) && !(xor (x 3) (x 4)))
  | 6 => xor (x 6) ((x 2 || x 3) && !(xor (x 4) (x 5)))
  | 7 => xor (x 7) ((x 3 || x 4) && !(xor (x 5) (x 6)))
  | _ => false

theorem eight_cases (j : Nat) (hj : j<8) :
    j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega

theorem two_tick (a b c d e : Bool) :
    xor (xor e (d || c)) ((xor d (c || b)) || xor c (b || a)) =
      xor e ((b || a) && !(xor c d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

theorem macro_eight (x : Row) (j : Nat) (hj : j<8) : rstep x j=bstep x j := by
  rcases eight_cases j hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · dsimp only [rstep,rowStep,bstep]; cases x 0 <;> rfl
  · dsimp only [rstep,rowStep,bstep]; cases x 0 <;> cases x 1 <;> rfl
  · dsimp only [rstep,rowStep,bstep]; cases x 0 <;> cases x 1 <;> cases x 2 <;> rfl
  · simpa only [rstep,rowStep,bstep,Bool.or_false] using two_tick false (x 0) (x 1) (x 2) (x 3)
  · simpa only [rstep,rowStep,bstep,Bool.or_comm] using two_tick (x 0) (x 1) (x 2) (x 3) (x 4)
  · simpa only [rstep,rowStep,bstep,Bool.or_comm] using two_tick (x 1) (x 2) (x 3) (x 4) (x 5)
  · simpa only [rstep,rowStep,bstep,Bool.or_comm] using two_tick (x 2) (x 3) (x 4) (x 5) (x 6)
  · simpa only [rstep,rowStep,bstep,Bool.or_comm] using two_tick (x 3) (x 4) (x 5) (x 6) (x 7)

theorem macro_congr {x y : Row} (h : ∀ j, j<8 → x j=y j) (j : Nat) (hj : j<8) :
    rstep x j=rstep y j := by
  rw [macro_eight x j hj,macro_eight y j hj]
  rcases eight_cases j hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [bstep,h 0 (by omega),h 1 (by omega),h 2 (by omega),h 3 (by omega),
      h 4 (by omega),h 5 (by omega),h 6 (by omega),h 7 (by omega)]

def peval (p : List Poly) (x : Row) : Row := fun j => eval 8 (p.getD j []) x
def vars : List Poly := [var 0,var 1,var 2,var 3,var 4,var 5,var 6,var 7]
def pstep (p : List Poly) : List Poly :=
  let x := fun j => p.getD j []
  [neg (x 0), add one (add (x 0) (x 1)), x 2,
   add (x 3) (mul (x 0) (neg (add (x 1) (x 2)))),
   add (x 4) (mul (bor (x 0) (x 1)) (neg (add (x 2) (x 3)))),
   add (x 5) (mul (bor (x 1) (x 2)) (neg (add (x 3) (x 4)))),
   add (x 6) (mul (bor (x 2) (x 3)) (neg (add (x 4) (x 5)))),
   add (x 7) (mul (bor (x 3) (x 4)) (neg (add (x 5) (x 6))))]

theorem vars_eval (x : Row) (j : Nat) (hj : j<8) : peval vars x j=x j := by
  rcases eight_cases j hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [peval,vars,var,eval,mon,Nat.testBit_succ]

theorem pstep_eval (p : List Poly) (x : Row) (j : Nat) (hj : j<8) :
    peval (pstep p) x j=rstep (peval p x) j := by
  rw [macro_eight _ j hj]
  rcases eight_cases j hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [peval,pstep,bstep,eval_add,eval_mul,eval_one,eval_neg,eval_bor]

def inv (x : Row) : Bool :=
  !x 2 && xor (xor (x 5) (x 4 && xor (xor true (x 1)) (x 0 && x 1)))
    ((xor (x 0) (x 1)) && !x 3)

def invPoly (p : List Poly) : Poly :=
  let x := fun j => p.getD j []
  mul (neg (x 2)) (add (add (x 5) (mul (x 4) (add (add one (x 1)) (mul (x 0) (x 1)))))
    (mul (add (x 0) (x 1)) (neg (x 3))))

theorem inv_congr {x y : Row} (h : ∀ j, j<6 → x j=y j) : inv x=inv y := by
  simp only [inv,h 0 (by omega),h 1 (by omega),h 2 (by omega),h 3 (by omega),
    h 4 (by omega),h 5 (by omega)]

theorem invPoly_eval (p : List Poly) (x : Row) : eval 8 (invPoly p) x=inv (peval p x) := by
  simp only [invPoly,inv,peval,eval_add,eval_mul,eval_neg,eval_one]

theorem inv_coefficients : invPoly (pstep vars)=invPoly vars := by decide +kernel

theorem invariant_macro (x : Row) : inv (rstep x)=inv x := by
  calc
    inv (rstep x) = inv (rstep (peval vars x)) :=
      inv_congr (fun j hj => (macro_congr (vars_eval x) j (by omega)).symm)
    _ = inv (peval (pstep vars) x) := inv_congr (fun j hj => (pstep_eval vars x j (by omega)).symm)
    _ = eval 8 (invPoly (pstep vars)) x := (invPoly_eval _ _).symm
    _ = eval 8 (invPoly vars) x := by rw [inv_coefficients]
    _ = inv (peval vars x) := invPoly_eval _ _
    _ = inv x := inv_congr (fun j hj => vars_eval x j (by omega))

def stageTable : List (List Poly) := [
  [[1], [2], [4], [8], [16], [32], [64], [128]],
  [[0,1], [0,1,2], [4], [1,3,5,8], [1,2,3,5,6,7,9,10,11,16], [2,4,6,10,12,14,18,20,22,32], [4,8,12,20,24,28,36,40,44,64], [8,16,24,40,48,56,72,80,88,128]],
  [[1], [0,2], [4], [1,2,4,8], [0,2,4,6,7,8,10,16], [0,1,3,4,5,8,9,11,12,14,16,17,20,21,32], [4,9,11,12,14,17,19,20,21,23,26,30,33,35,37,39,64], [1,3,5,8,9,11,13,17,18,19,21,22,24,25,27,28,29,33,34,35,37,38,39,40,41,42,43,45,46,47,49,51,52,53,55,57,59,60,61,63,65,66,67,69,70,74,78,79,81,83,85,128]],
  [[0,1], [1,2], [4], [1,2,3,4,5,8], [1,4,6,7,11,16], [0,4,5,6,8,9,11,12,17,18,20,21,22,32], [8,10,11,12,15,25,26,29,30,34,35,36,38,39,40,44,64], [9,10,13,14,15,19,20,26,27,30,31,32,34,35,37,39,40,41,43,46,47,48,50,51,53,55,56,60,64,65,66,71,73,75,78,80,82,83,84,85,88,128]],
  [[1], [2], [4], [0,8], [0,2,3,4,5,6,8,16], [0,1,3,5,6,7,8,10,11,13,14,15,32], [1,5,7,13,14,19,23,24,28,33,37,64], [4,5,6,10,11,17,18,19,21,22,26,27,29,30,31,32,33,34,35,39,40,43,45,46,47,49,52,54,57,61,64,67,68,69,71,72,76,79,81,128]],
  [[0,1], [0,1,2], [4], [0,1,3,5,8], [0,2,3,4,7,8,9,10,11,16], [0,1,6,7,8,10,11,13,14,15,18,20,22,32], [0,2,4,5,8,9,10,12,13,16,19,23,32,33,37,40,44,64], [3,4,5,10,12,13,14,17,18,21,22,23,26,28,29,30,31,34,35,37,39,41,42,44,45,47,49,52,54,56,67,68,69,71,74,75,77,78,79,81,88,128]],
  [[1], [0,2], [4], [0,1,2,4,8], [0,2,3,5,7,10,16], [2,4,5,6,8,10,15,16,17,20,21,32], [1,3,5,6,9,13,15,17,18,20,21,22,24,26,28,30,35,39,64], [0,1,2,3,6,7,8,12,14,16,20,24,28,30,31,33,34,35,39,42,44,47,51,52,53,54,55,59,60,63,64,67,68,69,71,72,73,74,75,76,77,78,83,85,128]],
  [[0,1], [1,2], [4], [0,1,2,3,4,5,8], [0,1,2,5,7,8,11,16], [0,1,3,7,15,17,18,20,21,22,32], [1,4,5,7,10,11,12,14,15,17,18,19,21,22,23,24,25,26,28,29,30,32,33,34,35,37,38,39,40,44,64], [4,6,7,9,10,11,12,13,14,15,17,18,19,25,26,28,30,32,33,35,38,39,43,44,45,46,47,49,50,51,53,54,55,56,60,66,68,69,70,72,73,75,76,79,81,82,83,84,85,88,128]],
  [[1], [2], [4], [8], [0,16], [0,2,3,5,6,7,32], [0,2,3,4,5,7,8,9,10,12,13,14,16,20,64], [3,5,6,7,9,13,15,17,18,20,21,24,30,32,33,38,44,45,46,64,65,68,73,128]],
  [[0,1], [0,1,2], [4], [1,3,5,8], [0,1,2,3,5,6,7,9,10,11,16], [0,2,3,5,6,7,10,12,14,18,20,22,32], [0,2,3,7,9,11,13,15,16,24,28,36,40,44,64], [0,3,4,5,7,8,10,12,14,15,16,17,18,21,22,24,33,38,44,45,46,48,56,65,68,73,80,88,128]],
  [[1], [0,2], [4], [1,2,4,8], [2,4,6,7,8,10,16], [0,2,5,6,7,8,9,11,12,14,16,17,20,21,32], [0,2,3,4,5,7,8,11,13,14,16,17,19,21,23,26,30,33,35,37,39,64], [2,3,4,7,8,9,10,11,13,14,17,18,23,26,29,31,32,33,34,36,40,42,45,49,51,52,53,55,57,59,60,61,63,64,65,66,68,70,73,74,78,79,81,83,85,128]],
  [[0,1], [1,2], [4], [1,2,3,4,5,8], [0,1,4,6,7,11,16], [1,3,5,6,7,8,9,11,12,17,18,20,21,22,32], [0,2,3,7,8,12,14,16,20,25,26,29,30,34,35,36,38,39,40,44,64], [1,3,4,5,9,12,14,15,16,19,22,23,24,25,26,30,32,33,38,41,43,45,47,48,50,51,53,55,56,60,64,67,69,71,72,75,78,80,82,83,84,85,88,128]],
  [[1], [2], [4], [0,8], [2,3,4,5,6,8,16], [1,2,8,10,11,13,14,15,32], [0,2,4,5,7,9,10,16,19,20,23,24,28,33,37,64], [2,3,4,6,11,12,16,20,23,25,26,28,33,34,35,36,39,40,41,43,44,45,47,49,52,54,57,61,67,69,71,72,73,76,79,81,128]],
  [[0,1], [0,1,2], [4], [0,1,3,5,8], [2,3,4,7,8,9,10,11,16], [1,3,4,5,6,8,10,11,13,14,15,18,20,22,32], [1,2,3,6,7,8,10,11,12,15,19,20,23,32,33,37,40,44,64], [1,2,3,5,6,7,8,9,10,11,12,13,14,15,19,25,26,28,30,31,32,34,35,36,37,39,40,41,42,46,47,49,52,54,56,64,67,69,71,72,73,74,75,77,78,79,81,88,128]],
  [[1], [0,2], [4], [0,1,2,4,8], [2,3,5,7,10,16], [1,3,5,7,8,10,15,16,17,20,21,32], [0,3,5,15,16,17,18,21,22,24,26,28,30,35,39,64], [0,4,5,6,8,10,12,15,17,18,19,21,22,23,24,25,26,27,28,30,32,34,36,37,42,43,44,45,46,51,52,53,54,55,59,60,63,65,71,72,74,75,76,77,78,83,85,128]],
  [[0,1], [1,2], [4], [0,1,2,3,4,5,8], [1,2,5,7,8,11,16], [4,15,17,18,20,21,22,32], [1,2,3,5,8,16,17,18,19,20,21,22,23,24,25,26,28,29,30,32,33,34,35,37,38,39,40,44,64], [0,3,4,6,8,10,14,15,18,19,20,22,23,24,25,28,29,33,34,37,38,40,43,44,47,49,50,51,53,54,55,56,60,64,67,68,70,75,76,79,81,82,83,84,85,88,128]],
  [[1], [2], [4], [8], [16], [32], [0,4,64], [1,2,5,6,10,14,16,17,20,21,25,29,128]],
  [[0,1], [0,1,2], [4], [1,3,5,8], [1,2,3,5,6,7,9,10,11,16], [2,4,6,10,12,14,18,20,22,32], [0,8,12,20,24,28,36,40,44,64], [1,2,5,6,10,12,14,16,17,21,25,28,29,40,48,56,72,80,88,128]],
  [[1], [0,2], [4], [1,2,4,8], [0,2,4,6,7,8,10,16], [0,1,3,4,5,8,9,11,12,14,16,17,20,21,32], [0,9,11,12,14,17,19,20,21,23,26,30,33,35,37,39,64], [1,5,7,8,9,11,13,16,17,18,20,21,22,23,24,27,28,33,34,35,37,38,39,40,41,42,43,45,46,47,49,51,52,53,55,57,59,60,61,63,65,66,67,69,70,74,78,79,81,83,85,128]]
]

def stage (t : Nat) : List Poly := stageTable.getD t []
theorem stage_zero : stage 0=vars := by decide +kernel
theorem stage_step_0 : stage 1=pstep (stage 0) := by decide +kernel
theorem stage_step_1 : stage 2=pstep (stage 1) := by decide +kernel
theorem stage_step_2 : stage 3=pstep (stage 2) := by decide +kernel
theorem stage_step_3 : stage 4=pstep (stage 3) := by decide +kernel
theorem stage_step_4 : stage 5=pstep (stage 4) := by decide +kernel
theorem stage_step_5 : stage 6=pstep (stage 5) := by decide +kernel
theorem stage_step_6 : stage 7=pstep (stage 6) := by decide +kernel
theorem stage_step_7 : stage 8=pstep (stage 7) := by decide +kernel
theorem stage_step_8 : stage 9=pstep (stage 8) := by decide +kernel
theorem stage_step_9 : stage 10=pstep (stage 9) := by decide +kernel
theorem stage_step_10 : stage 11=pstep (stage 10) := by decide +kernel
theorem stage_step_11 : stage 12=pstep (stage 11) := by decide +kernel
theorem stage_step_12 : stage 13=pstep (stage 12) := by decide +kernel
theorem stage_step_13 : stage 14=pstep (stage 13) := by decide +kernel
theorem stage_step_14 : stage 15=pstep (stage 14) := by decide +kernel
theorem stage_step_15 : stage 16=pstep (stage 15) := by decide +kernel
theorem stage_step_16 : stage 17=pstep (stage 16) := by decide +kernel
theorem stage_step_17 : stage 18=pstep (stage 17) := by decide +kernel

theorem stage_step (t : Nat) (ht : t<18) : stage (t+1)=pstep (stage t) := by
  have h : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 ∨ t=10 ∨ t=11 ∨ t=12 ∨ t=13 ∨ t=14 ∨ t=15 ∨ t=16 ∨ t=17 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact stage_step_0
  · exact stage_step_1
  · exact stage_step_2
  · exact stage_step_3
  · exact stage_step_4
  · exact stage_step_5
  · exact stage_step_6
  · exact stage_step_7
  · exact stage_step_8
  · exact stage_step_9
  · exact stage_step_10
  · exact stage_step_11
  · exact stage_step_12
  · exact stage_step_13
  · exact stage_step_14
  · exact stage_step_15
  · exact stage_step_16
  · exact stage_step_17

theorem stage_sound (x : Row) (t : Nat) (ht : t≤18) (j : Nat) (hj : j<8) :
    peval (stage t) x j=rit x t j := by
  induction t generalizing j with
  | zero => rw [stage_zero]; exact vars_eval x j hj
  | succ t ih =>
    rw [stage_step t (by omega),pstep_eval _ _ _ hj]
    exact macro_congr (fun k hk => ih (by omega) k hk) j hj

def terms : List (Nat × Nat) := [(0,1),(1,0),(3,0),(3,1),(4,2),(4,5),(5,3),(5,5),
  (6,1),(6,2),(6,5),(6,6),(7,0),(7,2),(7,16),(7,18)]
def samples (R : Nat → Row) : Bool :=
  terms.foldr (fun jt acc => xor (R jt.2 jt.1) acc) false
def streamPoly : Poly := terms.foldr
  (fun jt acc => add ((stage jt.2).getD jt.1 []) acc) []

theorem stream_coefficients : streamPoly=invPoly vars := by decide +kernel
theorem eval_nil (n : Nat) (x : Row) : eval n [] x=false := rfl

theorem stream_eval (x : Row) : eval 8 streamPoly x=samples (rit x) := by
  simp only [streamPoly,samples,terms,List.foldr,eval_add,eval_nil]
  change xor (peval (stage 1) x 0) (xor (peval (stage 0) x 1) (xor (peval (stage 0) x 3) (xor (peval (stage 1) x 3) (xor (peval (stage 2) x 4) (xor (peval (stage 5) x 4) (xor (peval (stage 3) x 5) (xor (peval (stage 5) x 5) (xor (peval (stage 1) x 6) (xor (peval (stage 2) x 6) (xor (peval (stage 5) x 6) (xor (peval (stage 6) x 6) (xor (peval (stage 0) x 7) (xor (peval (stage 2) x 7) (xor (peval (stage 16) x 7) (xor (peval (stage 18) x 7) (false)))))))))))))))) = xor (rit x 1 0) (xor (rit x 0 1) (xor (rit x 0 3) (xor (rit x 1 3) (xor (rit x 2 4) (xor (rit x 5 4) (xor (rit x 3 5) (xor (rit x 5 5) (xor (rit x 1 6) (xor (rit x 2 6) (xor (rit x 5 6) (xor (rit x 6 6) (xor (rit x 0 7) (xor (rit x 2 7) (xor (rit x 16 7) (xor (rit x 18 7) (false))))))))))))))))
  rw [stage_sound x 1 (by omega) 0 (by omega), stage_sound x 0 (by omega) 1 (by omega), stage_sound x 0 (by omega) 3 (by omega), stage_sound x 1 (by omega) 3 (by omega), stage_sound x 2 (by omega) 4 (by omega), stage_sound x 5 (by omega) 4 (by omega), stage_sound x 3 (by omega) 5 (by omega), stage_sound x 5 (by omega) 5 (by omega), stage_sound x 1 (by omega) 6 (by omega), stage_sound x 2 (by omega) 6 (by omega), stage_sound x 5 (by omega) 6 (by omega), stage_sound x 6 (by omega) 6 (by omega), stage_sound x 0 (by omega) 7 (by omega), stage_sound x 2 (by omega) 7 (by omega), stage_sound x 16 (by omega) 7 (by omega), stage_sound x 18 (by omega) 7 (by omega)]

theorem coordinate_stream_identity (x : Row) : inv x=samples (rit x) := by
  calc
    inv x = inv (peval vars x) := (inv_congr (fun j hj => vars_eval x j (by omega))).symm
    _ = eval 8 (invPoly vars) x := (invPoly_eval _ _).symm
    _ = eval 8 streamPoly x := by rw [stream_coefficients]
    _ = samples (rit x) := stream_eval x

end Rule30CASymbolic
