module
public import ReturnSections
@[expose] public section
namespace ControlledAlias
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration ReturnSections
open State

abbrev Phase := Fin 16
def advance (p : Phase) : Phase := ⟨(p.val+1)%16,Nat.mod_lt _ (by decide)⟩
def drive (p : Phase) : State :=
  [C,C,C,B,C,A,A,A,C,C,C,B,C,A,A,A][p.val]'(by exact p.isLt)
def left (p : Phase) : Nat :=
  [42,85,42,85,42,85,43,85,43,84,47,80,49,86,42,86][p.val]'(by exact p.isLt)
def right (p : Phase) : Nat :=
  [43,84,47,80,49,86,42,86,42,85,42,85,42,85,43,85][p.val]'(by exact p.isLt)
def code (n : Nat) : Code := n.testBit
def lowerC (q : State) : Bool := q==C
def lowerH (q : State) : Bool := q==B

/-- The ordinary edge recurrence on the interior, with two external lower
controls replacing the true black-edge ancestry. -/
def U (c h : Bool) (x : Code) : Code
  | 0 => xor (x 0) (c||h)
  | 1 => xor (x 1) (x 0||c)
  | j+2 => xor (x (j+2)) (x (j+1)||x j)

theorem act_is_controlled (q : State) (x : Code) : act q x=U (lowerC q) (lowerH q) x := by
  funext j
  cases j with
  | zero => cases q <;> rfl
  | succ j =>
    cases j with
    | zero => cases q <;> cases h:x 0 <;>
        simp only [act,stateAfter,next,ReturnSections.flip,U,lowerC,h] <;> rfl
    | succ j => simp only [act,after_two,memory_flip,U]

theorem table_step : ∀ p : Phase,∀ j : Fin 7,
    act (drive p) (code (left p)) j.val=code (left (advance p)) j.val ∧
    act (drive p) (code (right p)) j.val=code (right (advance p)) j.val := by decide

theorem table_interfaces : ∀ p : Phase,∀ j : Fin 2,
    code (left p) (j.val+5)=code (right p) (j.val+5) := by decide

/-- Even the necessary immediate ancestor condition is obeyed: if h is
black, the next c must differ from the current c. This is not full ancestry. -/
theorem ancestor_compatible : ∀ p : Phase,
    lowerH (drive p)=true → lowerC (drive (advance p))≠lowerC (drive p) := by decide

def Matches (p : Phase) (x y : Code) : Prop :=
  AgreeBelow 7 x (code (left p)) ∧ AgreeBelow 7 y (code (right p)) ∧
  ∀ j,7≤j → x j=y j

theorem matches_agree (p : Phase) (x y : Code) (h : Matches p x y) :
    ∀ j,5≤j → x j=y j := by
  intro j hj
  by_cases low : j<7
  · have eq := table_interfaces p ⟨j-5,by omega⟩
    have ix : j-5+5=j := by omega
    simp only [ix] at eq
    exact (h.1 j low).trans (eq.trans (h.2.1 j low).symm)
  · exact h.2.2 j (by omega)

theorem matches_step (p : Phase) (x y : Code) (h : Matches p x y) :
    Matches (advance p) (act (drive p) x) (act (drive p) y) := by
  refine ⟨?_,?_,?_⟩
  · intro j hj
    exact (act_agree (drive p) _ _ 7 h.1 j hj).trans (table_step p ⟨j,hj⟩).1
  · intro j hj
    exact (act_agree (drive p) _ _ 7 h.2.1 j hj).trans (table_step p ⟨j,hj⟩).2
  · intro j hj
    obtain ⟨k,rfl⟩ : ∃ k,j=k+2 := ⟨j-2,by omega⟩
    simp only [act,after_two,memory_flip,matches_agree p x y h (k+2) (by omega),
      matches_agree p x y h (k+1) (by omega),matches_agree p x y h k (by omega)]

def phase : Nat → Phase
  | 0 => ⟨0,by decide⟩
  | t+1 => advance (phase t)
def driven : Nat → Code → Code
  | 0,x => x
  | t+1,x => act (drive (phase t)) (driven t x)

theorem initial : Matches (phase 0) (code 42) (code 43) := by
  refine ⟨fun _ _ => rfl,fun _ _ => rfl,?_⟩
  intro j hj
  have big : 2^7≤2^j := Nat.pow_le_pow_right (by decide) hj
  have x : Nat.testBit 42 j=false := Nat.testBit_lt_two_pow (by omega)
  have y : Nat.testBit 43 j=false := Nat.testBit_lt_two_pow (by omega)
  exact x.trans y.symm

theorem matching_forever : ∀ t,Matches (phase t) (driven t (code 42)) (driven t (code 43))
  | 0 => initial
  | t+1 => matches_step _ _ _ (matching_forever t)

/-- A synthetic driven defect remains inside five digits forever. The
external controls obey one-step ancestor compatibility; they are not proved
to come from an actual finite black-edge prefix. No Rule30 counterexample. -/
theorem controlled_confined : ∀ t j,5≤j → driven t (code 42) j=driven t (code 43) j := by
  intro t j hj
  exact matches_agree _ _ _ (matching_forever t) j hj

theorem different_forever (t : Nat) : driven t (code 42) 0≠driven t (code 43) 0 := by
  have different : ∀ p : Phase,code (left p) 0≠code (right p) 0 := by decide
  have h:=matching_forever t
  rw [h.1 0 (by omega),h.2.1 0 (by omega)]
  exact different _

theorem phase_val : ∀ t,(phase t).val=t%16
  | 0 => rfl
  | t+1 => by change ((phase t).val+1)%16=(t+1)%16;rw [phase_val t];omega

theorem recurrent_black_control (n : Nat) : lowerC (drive (phase (16*n)))=true := by
  have hv : phase (16*n)=⟨0,by decide⟩ := by
    apply Fin.ext
    rw [phase_val]
    simp only [Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod]
  rw [hv]
  rfl

end ControlledAlias
