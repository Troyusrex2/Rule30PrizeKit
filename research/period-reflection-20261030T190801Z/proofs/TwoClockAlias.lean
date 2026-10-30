module
public import ReturnSections
@[expose] public section
namespace TwoClockAlias
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration ReturnSections
open State

abbrev Phase := Fin 16
def advance (p : Phase) : Phase := ⟨(p.val+1)%16,Nat.mod_lt _ (by decide)⟩
def drive (p : Phase) : State :=
  [C,B,C,A,B,C,C,B,C,B,C,A,B,C,C,B][p.val]'(by exact p.isLt)
def left (p : Phase) : Nat :=
  [106,21,106,21,107,20,111,16,113,22,107,20,108,21,106,21][p.val]'(by exact p.isLt)
def right (p : Phase) : Nat :=
  [113,22,107,20,108,21,106,21,106,21,106,21,107,20,111,16][p.val]'(by exact p.isLt)
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

theorem initial : Matches (phase 0) (code 106) (code 113) := by
  refine ⟨fun _ _ => rfl,fun _ _ => rfl,?_⟩
  intro j hj
  have big : 2^7≤2^j := Nat.pow_le_pow_right (by decide) hj
  have x : Nat.testBit 106 j=false := Nat.testBit_lt_two_pow (by omega)
  have y : Nat.testBit 113 j=false := Nat.testBit_lt_two_pow (by omega)
  exact x.trans y.symm

theorem matching_forever : ∀ t,Matches (phase t) (driven t (code 106)) (driven t (code 113))
  | 0 => initial
  | t+1 => matches_step _ _ _ (matching_forever t)

/-- A synthetic driven defect remains inside five digits forever. The
external controls obey one-step ancestor compatibility; they are not proved
to come from an actual finite black-edge prefix. No Rule30 counterexample. -/
theorem controlled_confined : ∀ t j,5≤j → driven t (code 106) j=driven t (code 113) j := by
  intro t j hj
  exact matches_agree _ _ _ (matching_forever t) j hj

theorem different_forever (t : Nat) : driven t (code 106) 0≠driven t (code 113) 0 := by
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

def clockC (p : Phase) : Bool :=
  [true,false,true,false,false,true,true,false,true,false,true,false,false,true,true,false][p.val]'(by exact p.isLt)
def clockH (p : Phase) : Bool :=
  [false,true,true,false,true,false,false,true,false,true,true,false,true,false,false,true][p.val]'(by exact p.isLt)
def clockG (p : Phase) : Bool :=
  [true,false,false,false,true,false,true,true,true,false,false,false,true,false,true,true][p.val]'(by exact p.isLt)
def clockF (p : Phase) : Bool :=
  [false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true][p.val]'(by exact p.isLt)

/-- Both lower cells obey the genuine recurrence with the same two older
controls. This is stronger than the earlier one-step compatibility test. -/
theorem two_ancestor_recurrences : ∀ p : Phase,
    clockC (advance p)=xor (clockC p) (clockH p||clockG p) ∧
    clockH (advance p)=xor (clockH p) (clockG p||clockF p) := by decide

theorem actual_clock_compatible : ∀ p : Phase,
    clockH p=true → clockC (advance p)≠clockC p := by decide

theorem driver_memory : ∀ p : Phase,drive p=memory (clockC p) (clockH p) := by decide

theorem actual_control_step (p : Phase) (x : Code) :
    act (drive p) x=U (clockC p) (clockH p) x := by
  rw [driver_memory,act_is_controlled]
  cases c:clockC p <;> cases h:clockH p <;> rfl

/-- The stronger source-free example respects the universal ACC exclusion. -/
theorem no_ACC_driver : ∀ p : Phase,drive p=A → drive (advance p)=C →
    drive (advance (advance p))≠C := by decide

theorem actual_recurrent_black (n : Nat) : clockC (phase (16*n))=true := by
  have hv : phase (16*n)=⟨0,by decide⟩ := by
    apply Fin.ext
    rw [phase_val]
    simp only [Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod]
  rw [hv]
  rfl

def boundaryWord : List State := [B,C,C,B,A,C,B,C]

theorem boundary_word_swaps_prefixes : ∀ j : Fin 7,
    run boundaryWord (code 106) j.val=code 113 j.val ∧
    run boundaryWord (code 113) j.val=code 106 j.val := by decide

theorem boundary_word_root_flip : parity boundaryWord=true := by decide

theorem square_word_alias :
    sectionWord (boundaryWord++boundaryWord) (code 106) 7=
    sectionWord (boundaryWord++boundaryWord) (code 113) 7 := by decide

end TwoClockAlias
