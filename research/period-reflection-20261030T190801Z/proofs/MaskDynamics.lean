module
public import ReturnSections
@[expose] public section
namespace MaskDynamics
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration

theorem bool_stall (a b p q u v : Bool) (different : a≠b)
    (one : xor u (a||p)=xor u (b||q))
    (two : xor v (u||a)=xor v (u||b)) :
    xor u (a||p)=false ∧ xor u (b||q)=false := by
  cases a <;> cases b <;> cases p <;> cases q <;> cases u <;> cases v <;> simp_all

/-- A mask that stops a top difference turns white on the next tick. -/
theorem stall_turns_white (x y : Code) (j : Nat)
    (different : x (j+1)≠y (j+1))
    (above : x (j+2)=y (j+2)) (above2 : x (j+3)=y (j+3))
    (one : T x (j+2)=T y (j+2)) (two : T x (j+3)=T y (j+3)) :
    T x (j+2)=false ∧ T y (j+2)=false := by
  have h1 : xor (y (j+2)) (x (j+1)||x j)=xor (y (j+2)) (y (j+1)||y j) := by
    simpa only [T,above] using one
  have h2 : xor (y (j+3)) (y (j+2)||x (j+1))=
      xor (y (j+3)) (y (j+2)||y (j+1)) := by
    simpa only [T,above,above2] using two
  have h:=bool_stall _ _ _ _ _ _ different h1 h2
  simpa only [T,above] using h

/-- If the top difference persists through the stalled step, it escapes
two digits higher at the following step. No bound on j or time is used. -/
theorem two_step_escape (x y : Code) (j : Nat)
    (different : x (j+1)≠y (j+1))
    (above : x (j+2)=y (j+2)) (above2 : x (j+3)=y (j+3))
    (one : T x (j+2)=T y (j+2)) (two : T x (j+3)=T y (j+3))
    (persists : T x (j+1)≠T y (j+1)) :
    T (T x) (j+3)≠T (T y) (j+3) := by
  obtain ⟨whiteX,whiteY⟩:=stall_turns_white x y j different above above2 one two
  change xor (T x (j+3)) (T x (j+2)||T x (j+1))≠
    xor (T y (j+3)) (T y (j+2)||T y (j+1))
  rw [whiteX,whiteY,two]
  cases a:T x (j+1) <;> cases b:T y (j+1) <;>
    cases c:T y (j+3) <;> simp_all

-- Control: replace OR by (!previous && older). This is a different rule,
-- not Rule30. It has a genuinely trapped finite pair in the same edge frame.
def T210 (x : Code) : Code
  | 0 => x 0
  | 1 => x 1
  | j+2 => xor (x (j+2)) (!(x (j+1)) && x j)
def iter210 : Nat → Code → Code
  | 0,x => x
  | t+1,x => T210 (iter210 t x)
def Wall (x y : Code) : Prop := x 1=false ∧ y 1=true ∧ y 2=true ∧
  x 3=true ∧ y 3=true ∧ ∀ j,3≤j → x j=y j

theorem wall_step (x y : Code) (h : Wall x y) : Wall (T210 x) (T210 y) := by
  obtain ⟨hx1,hy1,hy2,hx3,hy3,high⟩:=h
  refine ⟨hx1,hy1,?_,?_,?_,?_⟩
  · simp only [T210,hy1,hy2];rfl
  · simp only [T210,hx1,hx3];cases x 2 <;> rfl
  · simp only [T210,hy2,hy3];rfl
  · intro j hj
    by_cases three : j=3
    · subst j;simp only [T210,hx1,hy2,hx3,hy3];cases x 2 <;> rfl
    by_cases four : j=4
    · subst j;simp only [T210,hx3,hy3,high 4 (by omega)];rfl
    obtain ⟨k,rfl⟩ : ∃ k,j=k+2 := ⟨j-2,by omega⟩
    simp only [T210,high (k+2) (by omega),high (k+1) (by omega),high k (by omega)]

def wallX (j : Nat) : Bool := decide (j=0 ∨ j=3)
def wallY (j : Nat) : Bool := decide (j=0 ∨ j=1 ∨ j=2 ∨ j=3)
theorem wall_initial : Wall wallX wallY := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro j hj
  by_cases three : j=3
  · subst j;rfl
  · simp only [wallX,wallY,show j≠0 by omega,show j≠1 by omega,
      show j≠2 by omega,three,or_self,decide_false]

theorem wall_forever : ∀ t,Wall (iter210 t wallX) (iter210 t wallY)
  | 0 => wall_initial
  | t+1 => wall_step _ _ (wall_forever t)

theorem different_gate_has_trapped_pair :
    wallX 0=true ∧ wallY 0=true ∧ wallX≠wallY ∧
    (∀ j,4≤j → wallX j=false ∧ wallY j=false) ∧
    ∀ t j,3≤j → iter210 t wallX j=iter210 t wallY j := by
  refine ⟨rfl,rfl,?_,?_,?_⟩
  · intro eq
    have no:=congrFun eq 1
    cases no
  · intro j hj
    simp only [wallX,wallY,show j≠0 by omega,show j≠1 by omega,
      show j≠2 by omega,show j≠3 by omega,or_self,decide_false]
    exact ⟨True.intro,True.intro⟩
  · intro t j hj;exact (wall_forever t).2.2.2.2.2 j hj

end MaskDynamics
