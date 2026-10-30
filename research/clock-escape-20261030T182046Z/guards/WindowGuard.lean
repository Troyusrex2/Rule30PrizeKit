module
import WindowBarrier
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration WindowBarrier
example (w : Nat → Nat → Int) :
    ¬ ∀ x y : Nat → Bool,
      (x 0=true ∧ y 0=true ∧
      x 1=x 2 ∧ y 1=y 2 ∧
      ((List.range 7).any (fun j => x j != y j))=true ∧
      x 7=y 7 ∧ x 8=y 8 ∧ T x 7=T y 7 ∧ T x 8=T y 8) →
      (w 0 (window (T x) (T y) 5)+w 1 (window (T x) (T y) 4)+
       w 2 (window (T x) (T y) 3)+w 3 (window (T x) (T y) 2)+
       w 4 (window (T x) (T y) 1)+w 5 (window (T x) (T y) 0)) <
      (w 0 (window x y 5)+w 1 (window x y 4)+w 2 (window x y 3)+
       w 3 (window x y 2)+w 4 (window x y 1)+w 5 (window x y 0)) :=
  no_ranking w
example (w : Nat → Nat → Int) :
    ¬ ∀ x y,Good x y → Good (T x) (T y) →
      potential w (iter 2 x) (iter 2 y)<potential w x y := no_two_step_ranking w
