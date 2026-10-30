module
public import CanonicalDecoration
@[expose] public section
namespace LeakDescent
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration

def Parentless (x : Code) : Prop := x 1=x 2

theorem parentless_step (x : Code) (hx : x 0=true) :
    Parentless (T x) ↔ Parentless x := by
  simp only [Parentless,T,hx]
  cases x 1 <;> cases x 2 <;> decide

theorem iter_H (x : Code) (hx : x 0=true) (t : Nat) :
    iter t (H x)=H (iter t x) := by
  simpa only [decorate] using iter_decorate 1 x hx t

theorem H_read (x : Code) (hx : x 0=true) (t j : Nat) (hj : 1≤j) :
    iter t (H x) (j+1)=iter t x j := by
  rw [iter_H x hx t,H_shift _ _ hj]

theorem confined_H_iff (K : Nat) (x y : Code) (hx : x 0=true) (hy : y 0=true) :
    Confined (K+1) 0 (H x) (H y) ↔ Confined K 0 x y := by
  constructor
  · intro h t j hj
    have hc:=h t (j+1) (by omega)
    change iter t (H y) (j+1)=iter t (H x) (j+1) at hc
    rw [H_read y hy t j (by omega),H_read x hx t j (by omega)] at hc
    exact hc
  · intro h t j hj
    cases j with
    | zero => omega
    | succ j =>
      change iter t (H y) (j+1)=iter t (H x) (j+1)
      rw [H_read y hy t j (by omega),H_read x hx t j (by omega)]
      exact h t j (by omega)

theorem confined_zero (x y : Code) (hx : x 0=true) (hy : y 0=true)
    (h : Confined 0 0 x y) : x=y := by
  funext j
  cases j with
  | zero => exact hx.trans hy.symm
  | succ j => exact (h 0 (j+1) (by omega)).symm

def ParentlessRigidity : Prop := ∀ (K : Nat) (x y : Code),
  x 0=true → y 0=true → (Parentless x ∨ Parentless y) → Confined K 0 x y → x=y

theorem parentless_reduction (h : ParentlessRigidity) : SameEdgeRigidity := by
  intro K
  induction K with
  | zero => exact confined_zero
  | succ K ih =>
    intro x y hx hy hc
    by_cases px : Parentless x
    · exact h (K+1) x y hx hy (Or.inl px) hc
    by_cases py : Parentless y
    · exact h (K+1) x y hx hy (Or.inr py) hc
    have ex : H (parent x)=x := (H_parent_iff x hx).mpr (by
      cases h1:x 1 <;> cases h2:x 2 <;> simp_all [Parentless])
    have ey : H (parent y)=y := (H_parent_iff y hy).mpr (by
      cases h1:y 1 <;> cases h2:y 2 <;> simp_all [Parentless])
    have low : Confined K 0 (parent x) (parent y) :=
      (confined_H_iff K (parent x) (parent y) rfl rfl).mp (by
        rw [ex,ey];exact hc)
    have eq := ih (parent x) (parent y) rfl rfl low
    exact ex.symm.trans ((congrArg H eq).trans ey)

theorem same_edge_iff_parentless : SameEdgeRigidity ↔ ParentlessRigidity := by
  constructor
  · intro h K x y hx hy _ hc
    exact h K x y hx hy hc
  · exact parentless_reduction

theorem canonical_iff_parentless : CanonicalClassification ↔ ParentlessRigidity :=
  classification_iff_same_edge.trans same_edge_iff_parentless

-- Exact flip/freeze equation, including the permanent edge boundary.
theorem flip_freeze (x : Code) (j : Nat) :
    T x (j+2)=xor (x (j+2)) (!( !(x (j+1)) && !(x j))) := by
  simp only [T]
  cases x (j+1) <;> cases x j <;> rfl

def InitialTail (K : Nat) (x y : Code) : Prop := ∀ j,K+1≤j → x j=y j
def Interfaces (K : Nat) (x y : Code) : Prop := ∀ t,
  iter t x (K+1)=iter t y (K+1) ∧ iter t x (K+2)=iter t y (K+2)

/-- The finite two-interface test is exact for arbitrary infinite tails. -/
theorem confined_iff_interfaces (K : Nat) (x y : Code) :
    Confined K 0 x y ↔ InitialTail K x y ∧ Interfaces K x y := by
  constructor
  · intro h
    constructor
    · intro j hj; exact (h 0 j hj).symm
    · intro t;exact ⟨(h t (K+1) (by omega)).symm,(h t (K+2) (by omega)).symm⟩
  · rintro ⟨initial,interfaces⟩
    have all : ∀ t j,K+1≤j → iter t x j=iter t y j := by
      intro t
      induction t with
      | zero => exact initial
      | succ t ih =>
        intro j hj
        by_cases h1 : j=K+1
        · subst j;exact (interfaces (t+1)).1
        by_cases h2 : j=K+2
        · subst j;exact (interfaces (t+1)).2
        have high : K+3≤j := by omega
        obtain ⟨k,rfl⟩ : ∃ k,j=k+2 := ⟨j-2,by omega⟩
        change T (iter t x) (k+2)=T (iter t y) (k+2)
        simp only [T,ih (k+2) (by omega),ih (k+1) (by omega),ih k (by omega)]
    intro t j hj;exact (all t j hj).symm

/-- Any common bulk can be substituted above the autonomous band. -/
theorem transplant_confined (K : Nat) (x y u v : Code)
    (hx : AgreeBelow (K+3) x u) (hy : AgreeBelow (K+3) y v)
    (tail : InitialTail K u v) (h : Confined K 0 x y) : Confined K 0 u v := by
  apply (confined_iff_interfaces K u v).mpr
  refine ⟨tail,?_⟩
  intro t
  constructor
  · exact (iter_agree hx t (K+1) (by omega)).symm.trans
      ((h t (K+1) (by omega)).symm.trans (iter_agree hy t (K+1) (by omega)))
  · exact (iter_agree hx t (K+2) (by omega)).symm.trans
      ((h t (K+2) (by omega)).symm.trans (iter_agree hy t (K+2) (by omega)))

def truncate (n : Nat) (x : Code) : Code := fun j => if j<n then x j else false
def FiniteCode (x : Code) : Prop := ∃ n,∀ j,n≤j → x j=false
def FiniteRigidity : Prop := ∀ K x y,
  x 0=true → y 0=true → FiniteCode x → FiniteCode y → Confined K 0 x y → x=y

/-- A confined counterexample on infinite codes would already give one on
finite-support codes. This does not establish either rigidity property. -/
theorem rigidity_of_finite (h : FiniteRigidity) : SameEdgeRigidity := by
  intro K x y hx hy hc
  let u:=truncate (K+3) x
  let v:=truncate (K+3) y
  have xu : AgreeBelow (K+3) x u := by
    intro j hj;simp only [u,truncate,ite_eq_left hj]
  have yv : AgreeBelow (K+3) y v := by
    intro j hj;simp only [v,truncate,ite_eq_left hj]
  have uv : Confined K 0 u v := transplant_confined K x y u v xu yv (by
    intro j hj
    by_cases low : j<K+3
    · simp only [u,v,truncate,ite_eq_left low];exact (hc 0 j hj).symm
    · simp only [u,v,truncate,ite_eq_right low]) hc
  have eq : u=v := h K u v (by simpa [u,truncate] using hx)
    (by simpa [v,truncate] using hy)
    ⟨K+3,by intro j hj;simp [u,truncate,show ¬j<K+3 by omega]⟩
    ⟨K+3,by intro j hj;simp [v,truncate,show ¬j<K+3 by omega]⟩ uv
  funext j
  by_cases low : j<K+3
  · exact (xu j low).trans ((congrFun eq j).trans (yv j low).symm)
  · exact (hc 0 j (by omega)).symm

theorem same_edge_iff_finite : SameEdgeRigidity ↔ FiniteRigidity := by
  constructor
  · intro h K x y hx hy _ _ hc;exact h K x y hx hy hc
  · exact rigidity_of_finite

theorem high_agree_iter (K : Nat) (x y : Code) (h : InitialTail K x y) :
    ∀ t j,K+2*t+1≤j → iter t x j=iter t y j := by
  intro t
  induction t with
  | zero => exact h
  | succ t ih =>
    intro j hj
    obtain ⟨k,rfl⟩ : ∃ k,j=k+2 := ⟨j-2,by omega⟩
    change T (iter t x) (k+2)=T (iter t y) (k+2)
    simp only [T,ih (k+2) (by omega),ih (k+1) (by omega),ih k (by omega)]

/-- Agreement at every P-th tick already traps the difference in a fixed
wider band. This is the converse bridge needed by the return-section route. -/
theorem sampled_agreement_confines (K P : Nat) (hP : 0<P) (x y : Code)
    (h : ∀ q j,K+1≤j → iter (q*P) x j=iter (q*P) y j) :
    Confined (K+2*P) 0 x y := by
  intro t j hj
  have rem : t%P<P := Nat.mod_lt t hP
  have split : t/P*P+t%P=t := by simpa only [Nat.mul_comm] using Nat.div_add_mod t P
  have sample : InitialTail K (iter (t/P*P) x) (iter (t/P*P) y) := h (t/P)
  have equal := high_agree_iter K _ _ sample (t%P) j (by omega)
  rw [←iter_add x (t/P*P) (t%P),←iter_add y (t/P*P) (t%P),split] at equal
  exact equal.symm

end LeakDescent
