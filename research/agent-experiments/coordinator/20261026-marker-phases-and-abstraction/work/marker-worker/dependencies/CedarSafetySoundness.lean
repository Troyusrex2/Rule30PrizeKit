import Ruliology.CellularAutomata.Rule30Prize

/-!
The old 13-state safety language has an all-width full-word return property.
This is soundness only: no converse from safe traces is claimed. The table
comes from the prior sound reader plus eleven reference patterns; the new
certificate records the first nine temporal values of all viable prefixes.

Words are older-first. Both older boundary cells are permanently false.
No periodic background, clock hypothesis, finite width bound, or fixed
physical-center assertion occurs in the headline theorem.
-/
namespace CedarSafetySoundness

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

structure Profile where
  t0 : Bool
  t1 : Bool
  t2 : Bool
  t3 : Bool
  t4 : Bool
  t5 : Bool
  t6 : Bool
  t7 : Bool
  t8 : Bool
deriving DecidableEq, Repr

def ofNat (n : Nat) : Profile :=
  ⟨n.testBit 0, n.testBit 1, n.testBit 2, n.testBit 3, n.testBit 4,
   n.testBit 5, n.testBit 6, n.testBit 7, n.testBit 8⟩

def zero : Profile := ofNat 0

/-- p is the previous (nearest older) cell, r the older cell before p. -/
def nextProfile (p r : Profile) (v : Bool) : Profile :=
  let c1 := xor v (p.t0 || r.t0)
  let c2 := xor c1 (p.t1 || r.t1)
  let c3 := xor c2 (p.t2 || r.t2)
  let c4 := xor c3 (p.t3 || r.t3)
  let c5 := xor c4 (p.t4 || r.t4)
  let c6 := xor c5 (p.t5 || r.t5)
  let c7 := xor c6 (p.t6 || r.t6)
  let c8 := xor c7 (p.t7 || r.t7)
  ⟨v,c1,c2,c3,c4,c5,c6,c7,c8⟩

/-- A parallel triangular update with the two supplied older boundary bits. -/
def change (p r : Bool) : List Bool → List Bool
  | [] => []
  | v :: vs => xor v (p || r) :: change v p vs

/-- The exact finite white-ended map in the conjecture. -/
def F (xs : List Bool) : List Bool := change false false xs

def evolution : Nat → List Bool → List Bool
  | 0, xs => xs
  | t+1, xs => F (evolution t xs)

theorem local_rule_bridge (current previous older : Bool) :
    xor current (previous || older) =
      Ruliology.CellularAutomata.Rule30Jen.rule current previous older := rfl

/-- Eight parallel updates with time-varying supplied boundary profiles. -/
def run8 (p r : Profile) (xs : List Bool) : List Bool :=
  change p.t7 r.t7 (change p.t6 r.t6 (change p.t5 r.t5 (change p.t4 r.t4
    (change p.t3 r.t3 (change p.t2 r.t2 (change p.t1 r.t1 (change p.t0 r.t0 xs)))))))

theorem run8_nil (p r : Profile) : run8 p r [] = [] := rfl

/-- The semantic spatial bridge is definitional, not an assumed clock rule. -/
theorem run8_cons (p r : Profile) (v : Bool) (vs : List Bool) :
    run8 p r (v :: vs) = (nextProfile p r v).t8 :: run8 (nextProfile p r v) p vs := rfl

theorem run8_white (xs : List Bool) : run8 zero zero xs = evolution 8 xs := rfl

def transition (q : Nat) (v : Bool) : Nat :=
  match q with
  | 0 => if v then 1 else 0
  | 1 => if v then 3 else 2
  | 2 => if v then 3 else 4
  | 3 => if v then 5 else 2
  | 4 => if v then 6 else 6
  | 5 => if v then 8 else 7
  | 6 => if v then 9 else 9
  | 7 => if v then 10 else 9
  | 8 => if v then 10 else 10
  | 9 => if v then 12 else 11
  | 10 => if v then 11 else 12
  | 11 => if v then 11 else 11
  | 12 => if v then 11 else 11
  | _ => 11

def accepted (q : Nat) : Bool := q == 1 || q == 2 || q == 3 || q == 4 || q == 5 || q == 12

def read (q : Nat) : List Bool → Nat
  | [] => q
  | v :: vs => read (transition q v) vs

structure CertificateState where
  q : Nat
  previous : Profile
  older : Profile
deriving DecidableEq, Repr

def state (i : Fin 28) : CertificateState :=
  match i.val with
  | 0 => ⟨0, ofNat 0, ofNat 0⟩
  | 1 => ⟨1, ofNat 511, ofNat 0⟩
  | 2 => ⟨2, ofNat 170, ofNat 511⟩
  | 3 => ⟨3, ofNat 341, ofNat 511⟩
  | 4 => ⟨4, ofNat 170, ofNat 170⟩
  | 5 => ⟨3, ofNat 341, ofNat 170⟩
  | 6 => ⟨2, ofNat 170, ofNat 341⟩
  | 7 => ⟨5, ofNat 341, ofNat 341⟩
  | 8 => ⟨6, ofNat 204, ofNat 170⟩
  | 9 => ⟨6, ofNat 307, ofNat 170⟩
  | 10 => ⟨7, ofNat 102, ofNat 341⟩
  | 11 => ⟨8, ofNat 409, ofNat 341⟩
  | 12 => ⟨9, ofNat 180, ofNat 204⟩
  | 13 => ⟨9, ofNat 331, ofNat 204⟩
  | 14 => ⟨9, ofNat 210, ofNat 307⟩
  | 15 => ⟨9, ofNat 301, ofNat 307⟩
  | 16 => ⟨9, ofNat 90, ofNat 102⟩
  | 17 => ⟨10, ofNat 421, ofNat 102⟩
  | 18 => ⟨10, ofNat 150, ofNat 409⟩
  | 19 => ⟨10, ofNat 361, ofNat 409⟩
  | 20 => ⟨12, ofNat 343, ofNat 180⟩
  | 21 => ⟨12, ofNat 373, ofNat 331⟩
  | 22 => ⟨12, ofNat 349, ofNat 210⟩
  | 23 => ⟨12, ofNat 469, ofNat 301⟩
  | 24 => ⟨12, ofNat 427, ofNat 90⟩
  | 25 => ⟨12, ofNat 186, ofNat 421⟩
  | 26 => ⟨12, ofNat 234, ofNat 150⟩
  | 27 => ⟨12, ofNat 174, ofNat 361⟩
  | _ => ⟨0,zero,zero⟩

def Good (q : Nat) (p r : Profile) : Prop :=
  ∃ i : Fin 28, (state i).q = q ∧ (state i).previous = p ∧ (state i).older = r

instance (q : Nat) (p r : Profile) : Decidable (Good q p r) :=
  inferInstanceAs (Decidable (∃ i : Fin 28, (state i).q = q ∧ (state i).previous = p ∧ (state i).older = r))

/-- Exhaustive finite certificate, checked by kernel reduction. -/
theorem transition_certificate :
    ∀ (i : Fin 28) (v : Bool), transition (state i).q v ≠ 11 →
      (nextProfile (state i).previous (state i).older v).t8 = v ∧
      Good (transition (state i).q v)
        (nextProfile (state i).previous (state i).older v) (state i).previous := by
  decide

theorem good_step {q : Nat} {p r : Profile} (h : Good q p r) (v : Bool)
    (hlive : transition q v ≠ 11) :
    (nextProfile p r v).t8 = v ∧ Good (transition q v) (nextProfile p r v) p := by
  obtain ⟨i,hq,hp,hr⟩ := h
  subst q p r
  exact transition_certificate i v hlive

theorem sink_read (xs : List Bool) : read 11 xs = 11 := by
  induction xs with
  | nil => rfl
  | cons v vs ih => cases v <;> simpa [read, transition] using ih

theorem good_return (xs : List Bool) :
    ∀ (q : Nat) (p r : Profile), Good q p r → accepted (read q xs) = true →
      run8 p r xs = xs := by
  induction xs with
  | nil => intro q p r hg ha; rfl
  | cons v vs ih =>
    intro q p r hg ha
    have htail : accepted (read (transition q v) vs) = true := ha
    have hlive : transition q v ≠ 11 := by
      intro he
      rw [he, sink_read] at htail
      contradiction
    obtain ⟨hreturn,hnext⟩ := good_step hg v hlive
    rw [run8_cons,hreturn,ih _ _ _ hnext htail]

/-- All widths: acceptance implies equality of the ENTIRE finite word after 8 updates.
Safety-language completeness is not asserted. -/
theorem accepted_return_eight (xs : List Bool) (h : accepted (read 0 xs) = true) :
    evolution 8 xs = xs := by
  rw [← run8_white]
  exact good_return xs 0 zero zero ⟨⟨0,by decide⟩,rfl,rfl,rfl⟩ h

end CedarSafetySoundness
