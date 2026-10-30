module
import Ruliology.CellularAutomata.Rule30DefectClockBudget
import WordBoundary
import TemporalAncestry
import ControlledBudget
import MemorySeparation
open Ruliology.CellularAutomata.Rule30FrozenRuler
open CanonicalDecoration ReturnActions ReturnSections

example (j s : Nat) (x y : Nat → Bool) (hx : x 0=true)
    (low : ∀ k,k<j+1 → x k=y k) (ne : x (j+1)≠y (j+1)) :
    ∃ t,t≤7*((j+1)/2+1) ∧
      (iter (s+t) x (j+5)≠iter (s+t) y (j+5) ∨
       iter (s+t) x (j+6)≠iter (s+t) y (j+6)) :=
  Ruliology.CellularAutomata.Rule30DefectClockBudget.recurrent_four_layer_escape j s x y hx low ne

example (n P : Nat) (hP : 0<P) (x y : Nat → Bool)
    (fx : ∀ j,j<n → iter P x j=x j) (fy : ∀ j,j<n → iter P y j=y j)
    (eq : returnWord n P x=returnWord n P y) :
    ∀ z t,drop n (iter t (join n x z))=drop n (iter t (join n y z)) := by
  intro z;exact WordBoundary.shared_words_confine_at_cut n P hP x y z fx fy eq

example (n m : Nat) (x : Nat → Bool)
    (fixed : ∀ j,j<n → iter (8*(m+1)) x j=x j) :
    returnWord n (8*(m+1)) x≠TemporalAncestry.badPower (m+1) :=
  TemporalAncestry.all_bad_powers_unreachable n m x fixed

example : ∀ t j,5≤j →
    TwoClockAlias.driven t (Nat.testBit 106) j=TwoClockAlias.driven t (Nat.testBit 113) j :=
  TwoClockAlias.controlled_confined

example (t : Nat) (x : Nat → Bool) : TwoClockAlias.driven (t+1) x=
    TwoClockAlias.U (TwoClockAlias.clockC (TwoClockAlias.phase t))
      (TwoClockAlias.clockH (TwoClockAlias.phase t)) (TwoClockAlias.driven t x) :=
  TwoClockAlias.actual_control_step _ _

example (X Y : Nat → Nat → Bool) (c h : Nat → Bool)
    (xs : ∀ t,X (t+1)=TwoClockAlias.U (c t) (h t) (X t))
    (ys : ∀ t,Y (t+1)=TwoClockAlias.U (c t) (h t) (Y t))
    (compat : ∀ t,h t=true → c (t+1)≠c t)
    (different : X 0 0≠Y 0 0) (recurrent : ∀ s,∃ t,s≤t ∧ c t=true)
    (interfaces : ∀ t,X t 4=Y t 4 ∧ X t 5=Y t 5) : False :=
  ControlledBudget.no_four_digit_trap X Y c h xs ys compat different recurrent interfaces

example (n P i : Nat) (hP : 0<P) (hi : 0<i) (hin : i<n) (x y : Nat → Bool)
    (hx : x 0=true) (fx : AgreeBelow n (iter P x) x) (fy : AgreeBelow n (iter P y) y)
    (low : AgreeBelow i x y) (different : x i≠y i) (eq : returnWord n P x=returnWord n P y) :
    i+6≤n := MemorySeparation.source_collision_separation n P i hP hi hin x y hx fx fy low different eq
