module
public import Ruliology.CellularAutomata.Rule30GroupCocycle
public import Ruliology.CellularAutomata.Rule30BoundaryProfileCounterexample
@[expose] public section
open Ruliology.CellularAutomata
open Rule30GroupCocycle
example (n : Nat) (w : Word (n+2)) (i : Fin n) :
    image w i=Rule30Jen.rule (w ⟨i.val,by omega⟩) (w ⟨i.val+1,by omega⟩) (w ⟨i.val+2,by omega⟩) := rfl
example : ∀ (G : Type) [GroupData G] (n : Nat)
    (L : Word (n+1) → G) (M : Word (n+2) → G),
    (∀ w : Word (n+3), L (image w)*M (WordOps.init w)=M (WordOps.tail w)*L (middle w)) →
    ∃ g : Word n → G, ∀ w : Word (n+1),
      L w=(g (WordOps.tail w))⁻¹*L (zeros (n+1))*g (WordOps.init w) :=
  background_gauge_all_groups
example : ∀ (n : Nat) (rho : Word (n+1) → Bool) (j : Word (n+2) → Bool),
    (∀ w : Word (n+3), xor (rho (image w)) (rho (middle w))=
      xor (j (WordOps.init w)) (j (WordOps.tail w))) →
    ∃ g : Word n → Bool, ∀ w : Word (n+1), rho w=
      xor (xor (g (WordOps.tail w)) (rho (zeros (n+1)))) (g (WordOps.init w)) :=
  boolean_flux_coboundary

example : ∀ (G : Type) [GroupData G] (n : Nat)
    (L : Word (n+1) → G) (M : Word (n+2) → G),
    (∀ w : Word (n+3), L (image w)*M (WordOps.init w)=M (WordOps.tail w)*L (middle w)) →
    ∃ g : Word n → G, g (zeros n)=1 ∧
      L (zeros (n+1))*M (zeros (n+2))=M (zeros (n+2))*L (zeros (n+1)) ∧
      (∀ w : Word (n+1), L w=(g (WordOps.tail w))⁻¹*L (zeros (n+1))*g (WordOps.init w)) ∧
      (∀ w : Word (n+2), M w=(g (image w))⁻¹*M (zeros (n+2))*g (middle w)) :=
  full_background_connection

open Ruliology.CellularAutomata.Rule30BoundaryProfileCounterexample in
example (i : State) (k t : Nat) :
    past i k (t+1)=Rule30Jen.rule (past i k t) (past i (k+1) t) (past i (k+2) t) :=
  recurrence i k t

open Ruliology.CellularAutomata.Rule30GroupCocycle in
example : ∀ (G : Type) [GroupData G] (N n m r s : Nat)
    (hr : r+(n+1)≤N+1) (hs : s+(m+1)≤N+2)
    (L : Word (n+1) → G) (M : Word (m+1) → G),
    (∀ w : Word (N+3),
      L (window r (n+1) hr (image w))*M (window s (m+1) hs (WordOps.init w))=
      M (window s (m+1) hs (WordOps.tail w))*L (window r (n+1) hr (middle w))) →
    ∃ g : Word N → G, g (zeros N)=1 ∧
      L (zeros (n+1))*M (zeros (m+1))=M (zeros (m+1))*L (zeros (n+1)) ∧
      (∀ v : Word (N+1), L (window r (n+1) hr v)=
        (g (WordOps.tail v))⁻¹*L (zeros (n+1))*g (WordOps.init v)) ∧
      (∀ v : Word (N+2), M (window s (m+1) hs v)=
        (g (image v))⁻¹*M (zeros (m+1))*g (middle v)) :=
  arbitrary_local_supports
