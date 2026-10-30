module
public import ReturnSections
@[expose] public section
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration LeakDescent ReturnActions ReturnSections
example : ∀ x : Code, act State.A x=T x := act_A
example : ∀ (n P : Nat) (x z : Code),
    (fun j => iter P (join n x z) (n+j))=run (returnWord n P x) z := return_action
example : SameEdgeRigidity ↔
    (∀ (n P : Nat) (x y : Code), 0<n → 0<P → x 0=true → y 0=true →
      (∀ j,j<n → iter P x j=x j) → (∀ j,j<n → iter P y j=y j) →
      returnWord n P x=returnWord n P y → ∀ j,j<n → x j=y j) := rigidity_iff_all_return_words
example : ∀ (P n : Nat) (x : Code),
    (∀ j,j<n → iter P x j=x j) ↔
    ∀ j,j<n → parity (sectionWord (List.replicate P State.A) x j)=false := fixed_prefix_iff
example : ∀ (w : List State), parity w=true → ∀ b,
    nextWord (w++w) b=nextWord w (!b)++nextWord w b := double_odd
