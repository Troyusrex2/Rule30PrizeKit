module
public import QuietClock
public import TwoLayerEscape
@[expose] public section
namespace ClockDelay
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration LeakDescent ReturnActions

def shift (x : Code) : Code
  | 0 => false
  | j+1 => x j

theorem T_shift (x : Code) : T (shift x)=shift (T x) := by
  funext j
  cases j with
  | zero => rfl
  | succ j =>
    cases j with
    | zero => simp only [T,shift];cases x 0 <;> rfl
    | succ j =>
      cases j with
      | zero => simp only [T,shift];cases x 0 <;> cases x 1 <;> rfl
      | succ j => rfl

theorem iter_shift (t : Nat) (x : Code) : iter t (shift x)=shift (iter t x) := by
  induction t with
  | zero => rfl
  | succ t ih => change T (iter t (shift x))=shift (T (iter t x));rw [ih,T_shift]

def raise : Nat → Code → Code
  | 0,x => x
  | n+1,x => shift (raise n x)

theorem raise_at (n : Nat) (x : Code) (j : Nat) : raise n x (n+j)=x j := by
  induction n with
  | zero => simp only [raise,Nat.zero_add]
  | succ n ih => simpa only [raise,shift,Nat.succ_add] using ih

theorem raise_before (n : Nat) (x : Code) (j : Nat) (hj : j<n) :
    raise n x j=false := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j (by omega)

theorem iter_raise (n t : Nat) (x : Code) : iter t (raise n x)=raise n (iter t x) := by
  induction n with
  | zero => rfl
  | succ n ih => change iter t (shift (raise n x))=shift (raise n (iter t x));rw [iter_shift,ih]

def two : Code := fun j => decide (j<2)
def left : Code := H two
def right : Code := shift two

/-- This is the already-known decoration/edge-shift alias, not same-edge rigidity. -/
theorem ideal_alias (t j : Nat) (hj : 2≤j) : iter t left j=iter t right j := by
  obtain ⟨k,rfl⟩ : ∃ k,j=k+1 := ⟨j-1,by omega⟩
  change iter t (H two) (k+1)=iter t (shift two) (k+1)
  rw [iter_H two rfl,iter_shift,H_shift _ _ (by omega)]
  rfl

def plant (x : Code) : Code := fun j => if j=0 then true else x j
def X (n : Nat) : Code := plant (raise (2*n+3) left)
def Y (n : Nat) : Code := plant (raise (2*n+3) right)

theorem plant_edge (x : Code) : plant x 0=true := rfl

theorem plant_cone (x : Code) (t j : Nat) (hj : 2*t+1≤j) :
    iter t (plant x) j=iter t x j := by
  apply high_agree_iter 0 _ _ ?_ t j (by omega)
  intro k hk
  simp only [plant,ite_eq_right (by omega : k≠0)]

theorem common_below (n : Nat) : AgreeBelow (2*n+3) (X n) (Y n) := by
  intro j hj
  by_cases z : j=0
  · subst j;rfl
  · simp only [X,Y,plant,ite_eq_right z,raise_before _ _ _ hj]

theorem first_difference (n : Nat) : X n (2*n+3)≠Y n (2*n+3) := by
  have pos : 2*n+3≠0 := by omega
  simp only [X,Y,plant,ite_eq_right pos]
  have a:=raise_at (2*n+3) left 0
  have b:=raise_at (2*n+3) right 0
  simp only [Nat.add_zero] at a b
  rw [a,b]
  decide

theorem parentless (n : Nat) : X n 1=X n 2 ∧ Y n 1=Y n 2 := by
  simp only [X,Y,plant,ite_eq_right (by decide : (1:Nat)≠0),ite_eq_right (by decide : (2:Nat)≠0),
    raise_before (2*n+3) left 1 (by omega),raise_before (2*n+3) left 2 (by omega),
    raise_before (2*n+3) right 1 (by omega),raise_before (2*n+3) right 2 (by omega)]
  trivial

theorem finite_pair (n j : Nat) (hj : 2*n+6≤j) : X n j=false ∧ Y n j=false := by
  have pos : j≠0 := by omega
  simp only [X,Y,plant,ite_eq_right pos]
  obtain ⟨k,rfl⟩ : ∃ k,j=(2*n+3)+(k+3) := ⟨j-(2*n+6),by omega⟩
  rw [raise_at,raise_at]
  simp only [left,right,H,shift,two]
  simp only [show ¬k+2<2 by omega,decide_false]
  trivial

/-- Arbitrarily long finite agreement above a band only one digit beyond
the first difference. The common prefix clock cannot be discarded. -/
theorem arbitrary_delay (n t j : Nat) (ht : t≤n+2) (hj : 2*n+5≤j) :
    iter t (X n) j=iter t (Y n) j := by
  rw [show X n=plant (raise (2*n+3) left) from rfl,
    plant_cone _ t j (by omega),
    show Y n=plant (raise (2*n+3) right) from rfl,plant_cone _ t j (by omega),
    iter_raise,iter_raise]
  obtain ⟨k,rfl⟩ : ∃ k,j=(2*n+3)+k := ⟨j-(2*n+3),by omega⟩
  rw [raise_at,raise_at]
  exact ideal_alias t k (by omega)

/-- There is no escape-time bound depending only on K-i, even for finite,
parentless pairs with the same black edge and a first difference i≥3. -/
theorem no_distance_only_bound : ¬ ∃ B : Nat → Nat,
    ∀ K i x y,3≤i → K=i+1 →
      x 0=true → y 0=true → x 1=x 2 → y 1=y 2 →
      AgreeBelow i x y → x i≠y i →
      (∃ R,∀ j,R≤j → x j=false ∧ y j=false) →
      ∃ t j,t≤B (K-i) ∧ K+1≤j ∧ iter t x j≠iter t y j := by
  rintro ⟨B,bound⟩
  let n:=B 1
  obtain ⟨t,j,ht,hj,ne⟩:=bound (2*n+4) (2*n+3) (X n) (Y n)
    (by omega) (by omega) (plant_edge _) (plant_edge _)
    (parentless n).1 (parentless n).2 (common_below n) (first_difference n)
    ⟨2*n+6,finite_pair n⟩
  have sub : 2*n+4-(2*n+3)=1 := by omega
  rw [sub] at ht
  exact ne (arbitrary_delay n t j (by omega) (by omega))

/-- The two-layer escape bound is attained at every odd first-difference
digit i=2n+3: agreement lasts through n+2 and escape occurs exactly at n+3. -/
theorem sharp_two_layer (n : Nat) :
    (∀ t j,t≤n+2 → 2*n+5≤j → iter t (X n) j=iter t (Y n) j) ∧
    (iter (n+3) (X n) (2*n+5)≠iter (n+3) (Y n) (2*n+5) ∨
     iter (n+3) (X n) (2*n+6)≠iter (n+3) (Y n) (2*n+6)) := by
  refine ⟨fun t j ht hj => arbitrary_delay n t j ht hj,?_⟩
  obtain ⟨t,ht,ne⟩:=TwoLayerEscape.two_layer_escape (2*n+2) (X n) (Y n)
    (plant_edge _) (common_below n) (first_difference n)
  have exact_time : t=n+3 := by
    by_cases eq : t=n+3
    · exact eq
    · have early : t≤n+2 := by omega
      have a:=arbitrary_delay n t (2*n+5) early (by omega)
      have b:=arbitrary_delay n t (2*n+6) early (by omega)
      exact False.elim (ne.elim (fun h => h a) (fun h => h b))
  subst t
  exact ne

end ClockDelay
