module
public import ReturnActions
@[expose] public section
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration LeakDescent ReturnActions

example (x : Nat → Bool) (j : Nat) :
    T x (j+2)=xor (x (j+2)) (x (j+1)||x j) := rfl
example : ∀ (n : Nat) (x : Nat → Bool),
    ∀ j,j<n → iter (2^n) x j=x j := prefix_period

-- Expanded actual return action: no unspecified abstract transition map.
example : SameEdgeRigidity ↔
    (∀ (n : Nat) (x y : Nat → Bool), 0<n → x 0=true → y 0=true →
      (fun (z : Nat → Bool) (j : Nat) =>
        iter (2^n) (fun k => if k<n then x k else z (k-n)) (n+j))=
      (fun (z : Nat → Bool) (j : Nat) =>
        iter (2^n) (fun k => if k<n then y k else z (k-n)) (n+j)) →
      ∀ j,j<n → x j=y j) := rigidity_iff_return_injective

example : ∀ (n P : Nat), 0<P → ∀ (x y : Nat → Bool) (F : Code → Code),
    (∀ z,iter P (join n x z)=join n x (F z)) →
    (∀ z,iter P (join n y z)=join n y (F z)) →
    ∀ t j,n+2*P+1≤j →
      iter t (join n y zero) j=iter t (join n x zero) j := shared_return_confines
