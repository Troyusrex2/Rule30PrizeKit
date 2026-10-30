module
public import LeakDescent
@[expose] public section
namespace ReturnActions
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration LeakDescent

def drop (n : Nat) (x : Code) : Code := fun j => x (n+j)
def join (n : Nat) (x z : Code) : Code :=
  fun j => if j<n then x j else z (j-n)

theorem join_low (n : Nat) (x z : Code) (j : Nat) (hj : j<n) :
    join n x z j=x j := by simp only [join,ite_eq_left hj]
theorem join_high (n : Nat) (x z : Code) (j : Nat) (hj : n≤j) :
    join n x z j=z (j-n) := by simp only [join,ite_eq_right (by omega : ¬j<n)]

theorem iter_xor (n : Nat) (x y : Code) (h : AgreeBelow n x y) (t : Nat) :
    xor (iter t x n) (iter t y n)=xor (x n) (y n) := by
  by_cases eq : x n=y n
  · have full : AgreeBelow (n+1) x y := by
      intro j hj
      by_cases low : j<n
      · exact h j low
      · have : j=n := by omega
        subst j;exact eq
    have it := iter_agree full t n (by omega)
    simp only [it,eq,Bool.xor_self]
  · have ne := iter_diff h eq t
    cases a:iter t x n <;> cases b:iter t y n <;>
      cases c:x n <;> cases d:y n <;> simp_all

/-- Every n-bit prefix returns after 2^n ticks, for every infinite code. -/
theorem prefix_period (n : Nat) (x : Code) :
    AgreeBelow n (iter (2^n) x) x := by
  induction n generalizing x with
  | zero => intro j hj;omega
  | succ n ih =>
    let P:=2^n
    have twice : 2^(n+1)=P+P := by simp only [Nat.pow_succ];dsimp [P];omega
    have low : AgreeBelow n x (iter P x) := by
      intro j hj;exact (ih x j hj).symm
    have delta := iter_xor n x (iter P x) low P
    rw [←iter_add x P P] at delta
    intro j hj
    rw [twice]
    by_cases below : j<n
    · rw [iter_add x P P]
      exact (ih (iter P x) j below).trans (ih x j below)
    · have : j=n := by omega
      subst j
      cases a:iter P x n <;> cases b:iter (P+P) x n <;>
        cases c:x n <;> simp_all

def tailReturn (n P : Nat) (cfg : Code) : Code → Code :=
  fun z => drop n (iter P (join n cfg z))
def Returns (n P : Nat) (cfg : Code) (F : Code → Code) : Prop :=
  ∀ z,iter P (join n cfg z)=join n cfg (F z)

theorem prefix_factorization (n P : Nat) (x : Code)
    (fixed : AgreeBelow n (iter P x) x) : Returns n P x (tailReturn n P x) := by
  intro z
  funext j
  by_cases low : j<n
  · rw [join_low n x _ j low]
    have agree : AgreeBelow n (join n x z) x := by
      intro i hi;exact join_low n x z i hi
    exact (iter_agree agree P j low).trans (fixed j low)
  · rw [join_high n x _ j (by omega)]
    simp only [tailReturn,drop]
    congr 1
    omega

theorem dyadic_factorization (n : Nat) (x : Code) :
    Returns n (2^n) x (tailReturn n (2^n) x) :=
  prefix_factorization n (2^n) x (prefix_period n x)

def zero : Code := fun _ => false

/-- Equal return actions with fixed prefixes produce a fixed-width defect,
including all intermediate ticks, for arbitrary return periods P>0. -/
theorem shared_return_confines (n P : Nat) (hP : 0<P) (x y : Code) (F : Code → Code)
    (rx : Returns n P x F) (ry : Returns n P y F) :
    Confined (n+2*P) 0 (join n x zero) (join n y zero) := by
  apply sampled_agreement_confines n P hP
  have sampled : ∀ q,∃ z,
      iter (q*P) (join n x zero)=join n x z ∧
      iter (q*P) (join n y zero)=join n y z := by
    intro q
    induction q with
    | zero => exact ⟨zero,by simp only [Nat.zero_mul,iter],by simp only [Nat.zero_mul,iter]⟩
    | succ q ih =>
      obtain ⟨z,hx,hy⟩:=ih
      refine ⟨F z,?_,?_⟩
      · rw [show (q+1)*P=q*P+P by rw [Nat.add_mul,Nat.one_mul],iter_add,hx,rx]
      · rw [show (q+1)*P=q*P+P by rw [Nat.add_mul,Nat.one_mul],iter_add,hy,ry]
  intro q j hj
  obtain ⟨z,hx,hy⟩:=sampled q
  rw [hx,hy,join_high n x z j (by omega),join_high n y z j (by omega)]

def DyadicReturnInjective : Prop := ∀ (n : Nat) (x y : Code),
  0<n → x 0=true → y 0=true →
  tailReturn n (2^n) x=tailReturn n (2^n) y → AgreeBelow n x y

theorem return_injective_of_rigidity (rigid : SameEdgeRigidity) :
    DyadicReturnInjective := by
  intro n x y hn hx hy equal
  have rx:=dyadic_factorization n x
  have ry : Returns n (2^n) y (tailReturn n (2^n) x) := by
    rw [equal];exact dyadic_factorization n y
  have confined:=shared_return_confines n (2^n) (Nat.two_pow_pos n) x y _ rx ry
  have same:=rigid (n+2*(2^n)) (join n x zero) (join n y zero)
    (by rw [join_low n x zero 0 hn];exact hx)
    (by rw [join_low n y zero 0 hn];exact hy) confined
  intro j hj
  have h:=congrFun same j
  simpa only [join_low n x zero j hj,join_low n y zero j hj] using h

theorem rigidity_of_return_injective (inj : DyadicReturnInjective) :
    SameEdgeRigidity := by
  intro K x y hx hy confined
  let n:=K+3
  have maps : tailReturn n (2^n) x=tailReturn n (2^n) y := by
    funext z j
    let u:=join n x z
    let v:=join n y z
    have xu : AgreeBelow (K+3) x u := by
      intro i hi;exact (join_low n x z i hi).symm
    have yv : AgreeBelow (K+3) y v := by
      intro i hi;exact (join_low n y z i hi).symm
    have initial : InitialTail K u v := by
      intro i hi
      by_cases low : i<n
      · rw [show u i=x i from join_low n x z i low,
          show v i=y i from join_low n y z i low]
        exact (confined 0 i hi).symm
      · rw [show u i=z (i-n) from join_high n x z i (by omega),
          show v i=z (i-n) from join_high n y z i (by omega)]
    have hc:=transplant_confined K x y u v xu yv initial confined
    exact (hc (2^n) (n+j) (by dsimp [n];omega)).symm
  have fixed:=inj n x y (by dsimp [n];omega) hx hy maps
  funext j
  by_cases low : j<n
  · exact fixed j low
  · exact (confined 0 j (by dsimp [n] at low;omega)).symm

theorem rigidity_iff_return_injective : SameEdgeRigidity ↔ DyadicReturnInjective :=
  ⟨return_injective_of_rigidity,rigidity_of_return_injective⟩

theorem canonical_iff_return_injective : CanonicalClassification ↔ DyadicReturnInjective :=
  classification_iff_same_edge.trans rigidity_iff_return_injective

end ReturnActions
