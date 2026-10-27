module
public import Rule30CAInvariantResearch
public import Rule30LinearObservationModule
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases

/-! A method barrier for arbitrary two scalar output streams of finite CA.
It excludes affine F2-linear full-state decoding, not nonlinear observability. -/
@[expose] public section
namespace Rule30CALinearBarrier
open Rule30CAObserverResearch Rule30CAInvariantResearch Rule30CASymbolic
open Rule30LinearObservationModule
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev F := ZMod 2
abbrev State (m : Nat) := Fin m → Bool
abbrev Obs (m : Nat) := State m → F

def bit (b : Bool) : F := if b then 1 else 0
theorem bit_false : bit false=0 := rfl
theorem bit_true : bit true=1 := rfl
theorem bit_xor (a b : Bool) : bit (xor a b)=bit a+bit b := by
  cases a <;> cases b <;> decide +kernel
theorem bit_not (a : Bool) : bit (!a)=1+bit a := by
  cases a <;> decide +kernel

def row {m : Nat} (x : State m) (j : Nat) : Bool := if h:j<m then x ⟨j,h⟩ else false
def word {m : Nat} (x : State m) : List Bool := takeBits (row x) m
def turn {m : Nat} (x : State m) : State m := fun i => (T (word x)).getD i.val false

theorem take_length (x : Row) (n : Nat) : (takeBits x n).length=n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [takeBits,List.length_cons,ih]
theorem word_length {m : Nat} (x : State m) : (word x).length=m := take_length _ _
theorem row_word {m : Nat} (x : State m) (j : Nat) (hj : j<m) :
    initial (word x) j=row x j := getD_take _ _ _ hj
theorem row_turn {m : Nat} (x : State m) (j : Nat) (hj : j<m) :
    row (turn x) j=initial (T (word x)) j := by simp only [row,hj,dif_pos,turn,initial]

theorem word_turn {m : Nat} (x : State m) : word (turn x)=T (word x) := by
  have hl : (T (word x)).length=m := by rw [T_length,word_length]
  calc
    word (turn x)=takeBits (fun j => (T (word x)).getD j false) m :=
      take_congr _ _ _ (fun j hj => row_turn x j hj)
    _ = T (word x) := by simpa only [hl] using (take_initial (T (word x)))

def U (m : Nat) : Obs m →ₗ[F] Obs m where
  toFun f := fun x => f (turn x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def oneFn (m : Nat) : Obs m := fun _ => 1
def coord (m j : Nat) : Obs m := fun x => bit (row x j)
def label (m : Nat) : Obs m := fun x => bit (invariant (word x))

theorem one_fixed (m : Nat) : U m (oneFn m)=oneFn m := rfl
theorem first_flip (m : Nat) (hm : 0<m) : U m (coord m 0)=oneFn m+coord m 0 := by
  funext x
  change bit (row (turn x) 0)=1+bit (row x 0)
  rw [row_turn x 0 hm,first_T _ (by rw [word_length]; exact hm),row_word x 0 hm,bit_not]
theorem third_fixed (m : Nat) (hm : 3≤m) : U m (coord m 2)=coord m 2 := by
  funext x
  change bit (row (turn x) 2)=bit (row x 2)
  rw [row_turn x 2 (by omega),third_T _ (by rw [word_length]; exact hm),row_word x 2 (by omega)]
theorem label_fixed (m : Nat) (hm : 6≤m) : U m (label m)=label m := by
  funext x
  change bit (invariant (word (turn x)))=bit (invariant (word x))
  rw [word_turn,invariant_T _ (by rw [word_length]; exact hm)]

theorem iterate_coord (m t j : Nat) (hj : j<m) (x : State m) :
    ((U m)^[t] (coord m j)) x=bit (coordinate (word x) t j) := by
  induction t generalizing x with
  | zero => exact congrArg bit (row_word x j hj).symm
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    change ((U m)^[t] (coord m j)) (turn x)=_
    rw [ih,word_turn]
    simp only [coordinate,titer_step]

def combo (m : Nat) (ts : List (Nat × Nat)) : Obs m :=
  ts.foldr (fun jt acc => ((U m)^[jt.2] (coord m jt.1))+acc) 0

theorem combo_eval (m : Nat) (ts : List (Nat × Nat))
    (hb : ∀ jt∈ts, jt.1<m) (x : State m) :
    combo m ts x=bit (ts.foldr (fun jt acc => xor (coordinate (word x) jt.2 jt.1) acc) false) := by
  induction ts with
  | nil => rfl
  | cons jt ts ih =>
    change ((U m)^[jt.2] (coord m jt.1)) x + combo m ts x = _
    rw [List.foldr,bit_xor]
    rw [iterate_coord m jt.2 jt.1 (hb jt (by simp)),ih (fun p hp => hb p (by simp [hp]))]

theorem terms_bound : ∀ jt∈terms, jt.1<8 := by decide +kernel
theorem label_combo (m : Nat) (hm : 8≤m) : label m=combo m terms := by
  funext x
  rw [combo_eval m terms (fun jt hj => lt_of_lt_of_le (terms_bound jt hj) hm)]
  change bit (invariant (word x))=bit (stream (word x))
  rw [invariant_coordinate_stream _ (by rw [word_length]; exact hm)]

theorem iterate_mem (m : Nat) (a b : Obs m) {f : Obs m}
    (hf : f∈OrbitSpan (U m) a b) (t : Nat) : (U m)^[t] f∈OrbitSpan (U m) a b := by
  induction t with
  | zero => exact hf
  | succ t ih => rw [Function.iterate_succ_apply']; exact orbitSpan_stable _ _ _ ih

theorem label_mem (m : Nat) (hm : 8≤m) (a b : Obs m)
    (hc : ∀ j, j<m → coord m j∈OrbitSpan (U m) a b) : label m∈OrbitSpan (U m) a b := by
  rw [label_combo m hm]
  have hcombo : ∀ ts : List (Nat × Nat), (∀ jt∈ts, jt.1<m) →
      combo m ts∈OrbitSpan (U m) a b := by
    intro ts
    induction ts with
    | nil => intro _; exact (OrbitSpan (U m) a b).zero_mem
    | cons jt ts ih =>
      intro hb
      exact (OrbitSpan (U m) a b).add_mem
        (iterate_mem m a b (hc jt.1 (hb jt (by simp))) jt.2)
        (ih (fun p hp => hb p (by simp [hp])))
  exact hcombo terms (fun jt hj => lt_of_lt_of_le (terms_bound jt hj) hm)

def three (m : Nat) : Fin 3 → Obs m := ![oneFn m,coord m 2,label m]
def zeroState (m : Nat) : State m := fun _ => false
def oneState (m : Nat) : State m := fun i => decide (i.val=0)
def fourState (m : Nat) : State m := fun i => decide (i.val=2)

theorem label_formula (m : Nat) (hm : 6≤m) (x : State m) :
    label m x=bit (inv (row x)) := by
  apply congrArg bit
  exact inv_congr (fun j hj => row_word x j (by omega))

theorem three_independent (m : Nat) (hm : 8≤m) : LinearIndependent F (three m) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have h0 := congrFun hc (zeroState m)
  have h1 := congrFun hc (oneState m)
  have h4 := congrFun hc (fourState m)
  have hm0 : 0<m := by omega
  have hm1 : 1<m := by omega
  have hm2 : 2<m := by omega
  have hm3 : 3<m := by omega
  have hm4 : 4<m := by omega
  have hm5 : 5<m := by omega
  have h6 : 6≤m := by omega
  simp [Fin.sum_univ_succ,three,oneFn,coord,label_formula m h6,
    zeroState,oneState,fourState,row,inv,bit,hm0,hm1,hm2,hm3,hm4,hm5] at h0 h1 h4
  intro i
  fin_cases i <;> simp_all

/-- A precise affine decoder condition: every coordinate is a constant plus
a finite F2-linear combination of the two output streams at fixed times. -/
def AffineDecodes (m : Nat) (a b : Obs m) : Prop :=
  ∀ j, j<m → ∃ c : F, ∃ w : Obs m,
    w∈OrbitSpan (U m) a b ∧ coord m j=(fun _ => c)+w

theorem no_two_output_affine_decoder (m : Nat) (hm : 8≤m) (a b : Obs m) :
    ¬ AffineDecodes m a b := by
  intro hd
  obtain ⟨c,w,hw,he⟩ := hd 0 (by omega)
  have hu := orbitSpan_stable (U m) a b hw
  have hconst : oneFn m∈OrbitSpan (U m) a b := by
    have hh : U m w-w=oneFn m := by
      have hc0 : U m (coord m 0)-coord m 0=oneFn m := by
        rw [first_flip m (by omega)]
        simp
      rw [he] at hc0
      have hk : U m (fun _ : State m => c)=(fun _ => c) := rfl
      rw [map_add,hk] at hc0
      simpa only [add_sub_add_left_eq_sub] using hc0
    rw [←hh]
    exact (OrbitSpan (U m) a b).sub_mem hu hw
  have hcoords : ∀ j, j<m → coord m j∈OrbitSpan (U m) a b := by
    intro j hj
    obtain ⟨c,w,hw,he⟩ := hd j hj
    rw [he]
    have hc : (fun _ : State m => c)∈OrbitSpan (U m) a b := by
      have hs := (OrbitSpan (U m) a b).smul_mem c hconst
      have heq : c • oneFn m=(fun _ : State m => c) := by
        funext x
        simp [oneFn]
      rw [heq] at hs
      exact hs
    exact (OrbitSpan (U m) a b).add_mem hc hw
  apply not_three_fixed_independent (U m) a b (three m) ?_ ?_ (three_independent m hm)
  · intro i
    fin_cases i
    · exact hconst
    · exact hcoords 2 (by omega)
    · exact label_mem m hm a b hcoords
  · intro i
    fin_cases i
    · exact one_fixed m
    · exact third_fixed m (by omega)
    · exact label_fixed m (by omega)

end Rule30CALinearBarrier
