module
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Realization

/-! Exact source-arrival aliasing and small actual-seed Hankel witnesses.
The packed-row adapter is copied from official Rule30Window, with attribution;
no novelty is claimed for packing, elementary Schur algebra, or finite data. -/
@[expose] public section
namespace HankelSourceResearch
open Ruliology.CellularAutomata Rule30Jen Rule30Prize Rule30Realization
namespace Packed
def stepRow (r : Nat) : Nat := (r <<< 1) ^^^ (r ||| (r >>> 1))

/-- The packed row at time `t`, seeded at bit `K`. -/
def row (K : Nat) : Nat → Nat
  | 0 => 2 ^ K
  | t + 1 => stepRow (row K t)

theorem cell_congr' {t : Nat} {p q : Int} (h : p = q) : cell t p = cell t q := h ▸ rfl

/-- **The packed rows are rule 30**: while `t ≤ K`, bit `k` of the row is the cell at `k − K`. -/
theorem row_testBit (K : Nat) : ∀ t, t ≤ K → ∀ k : Nat, (row K t).testBit k = cell t ((k : Int) - K)
  | 0, _, k => by
    simp only [row, Nat.testBit_two_pow, cell]
    by_cases h : K = k
    · subst h; simp
    · rw [decide_eq_false h, decide_eq_false (by omega)]
  | t + 1, ht, k => by
    have ih := row_testBit K t (by omega)
    have e : cell (t + 1) ((k : Int) - K) = rule (cell t ((k : Int) - K - 1))
        (cell t ((k : Int) - K)) (cell t ((k : Int) - K + 1)) := rfl
    rw [e]
    simp only [row, stepRow, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, rule]
    rw [ih k, ih (1 + k), cell_congr' (show ((1 + k : Nat) : Int) - K = (k : Int) - K + 1 by omega)]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [cell_eq_false_of_lt t ((((0 : Nat) : Int)) - K - 1) (by omega)]
      simp
    · rw [show decide (k ≥ 1) = true from decide_eq_true hk, Bool.true_and, ih (k - 1),
        cell_congr' (show ((k - 1 : Nat) : Int) - K = (k : Int) - K - 1 by omega)]


end Packed

def observedBits : List Bool :=
  [true,true,false,true,true,true,false,false,true,true,false,false,false,true,false]

theorem center_prefix (t : Nat) (ht : t<15) : center t=observedBits.getD t false := by
  have h := Packed.row_testBit 16 t (by omega) 16
  have hd : ∀ i : Fin 15, (Packed.row 16 i).testBit 16=observedBits.getD i false := by decide
  have he : (Packed.row 16 t).testBit 16=center t := by simpa only [center,Int.sub_self] using h
  exact he.symm.trans (hd ⟨t,ht⟩)

def zbit (b : Bool) : Int := if b then 1 else 0
def hankel8 (i j : Fin 8) : Int := zbit (center (i.val+j.val))
def dataHankel8 (i j : Fin 8) : Int := zbit (observedBits.getD (i.val+j.val) false)
def null8 (j : Fin 8) : Int := [-1,-1,0,0,1,1,1,0].getD j.val 0

theorem hankel8_eq_data : hankel8=dataHankel8 := by
  funext i j
  simp only [hankel8,dataHankel8,center_prefix (i.val+j.val) (by omega)]

/-- An INTEGER null vector: the leading dyadic minor fails over Q as well as F2. -/
theorem integer_hankel8_null :
    null8 0≠0 ∧ ∀ i : Fin 8, (List.ofFn (fun j : Fin 8 => hankel8 i j*null8 j)).sum=0 := by
  constructor
  · decide
  · rw [hankel8_eq_data]
    decide

theorem fresh_source_cancels :
    (center 3 && cell 3 1)=true ∧
    (cell 1 (-1) && center 1)=true ∧ xor (center 3) (center 4)=false := by decide

def det2 (a b c d : Int) : Int := a*d-b*c
def det3 (a b c d e f g h i : Int) : Int :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

theorem rational_pivot_lifts :
    det2 (zbit (center 0)) (zbit (center 1)) (zbit (center 1)) (zbit (center 2)) = -1 ∧
    det3 (zbit (center 0)) (zbit (center 1)) (zbit (center 2))
         (zbit (center 1)) (zbit (center 2)) (zbit (center 3))
         (zbit (center 2)) (zbit (center 3)) (zbit (center 4)) = -2 := by decide

/-- The binary alphabet forces this border over Q before the next bit is known. -/
theorem alphabet_forces_third_border (b : Bool) :
    det3 1 1 0 1 0 1 0 1 (zbit b)= -(1+zbit b) ∧
    det3 1 1 0 1 0 1 0 1 (zbit b)≠0 := by cases b <;> decide

def feedback (a b u v : Bool) : Bool := if b then u else v && !(xor a u)

theorem even_two_step (l a b u v : Bool) :
    rule (rule l u a) (rule u a v) (rule a v b)=
      xor (xor l (!a && b)) (feedback a b u v) := by
  cases l <;> cases a <;> cases b <;> cases u <;> cases v <;> decide

theorem odd_two_step (a b u v w : Bool) :
    rule (rule u a v) (rule a v b) (rule v b w)=
      xor (xor u (!a && b)) (feedback a b v w) := by
  cases a <;> cases b <;> cases u <;> cases v <;> cases w <;> decide

theorem spaced_even (l a b : Bool) :
    rule (rule l false a) (rule false a false) (rule a false b)=xor l (!a && b) := by
  cases l <;> cases a <;> cases b <;> decide

theorem spaced_odd (a b : Bool) :
    rule (rule false a false) (rule a false b) (rule false b false)=(!a && b) := by
  cases a <;> cases b <;> decide

theorem green_symm (t : Nat) (p : Int) : run g150 t (-p)=run g150 t p :=
  run_symm g150 (by intro a b c;cases a <;> cases b <;> cases c <;> rfl) t p

theorem green_right_edge (d : Nat) : run g150 d (d : Int)=true := by
  rw [←green_symm]
  exact run_left_edge g150 rfl rfl d

theorem green_before (t d : Nat) (h : t<d) : run g150 t (d : Int)=false := by
  rw [←green_symm]
  exact run_eq_false_of_lt g150 rfl t _ (by omega)

/-- Center response to one source injected after step s, d cells away. -/
def impulse (s d t : Nat) : Bool :=
  if s<t then run g150 (t-s-1) (d : Int) else false

theorem first_arrival (s d t : Nat) (ht : t≤s+d+1) :
    impulse s d t=decide (t=s+d+1) := by
  by_cases hs : s<t
  · rw [impulse,ite_eq_left hs]
    by_cases he : t=s+d+1
    · rw [he,show s+d+1-s-1=d by omega,green_right_edge]
      simp
    · rw [green_before _ _ (by omega),decide_eq_false he]
  · simp only [impulse,ite_eq_right hs,decide_eq_false (show t≠s+d+1 by omega)]

/-- Every source on one backwards characteristic has the SAME observed prefix. -/
theorem coincident_arrivals (s d a b : Nat) (h : s+d=a+b) (t : Nat) (ht : t≤s+d+1) :
    impulse s d t=impulse a b t := by
  rw [first_arrival s d t ht,first_arrival a b t (by omega),h]

/-- No functional using only this prefix can distinguish the two source responses.
This is a finite-horizon source-isolation obstruction, not eternal invisibility. -/
theorem cannot_separate_at_arrival (s d a b : Nat) (h : s+d=a+b)
    (F : (Nat → Bool) → Bool)
    (hF : ∀ x y, (∀ t, t≤s+d+1 → x t=y t) → F x=F y) :
    ¬(F (impulse s d)=true ∧ F (impulse a b)=false) := by
  intro he
  have hf := hF (impulse s d) (impulse a b) (fun t ht => coincident_arrivals s d a b h t ht)
  rw [he.1,he.2] at hf
  cases hf

end HankelSourceResearch
