module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
Research obstruction for finite-horizon backward lifting. This does not prove
center observability, an infinite-horizon obstruction, or Prize Problem 1.
The target is the first seed row together with an isolated pulse at U >= 2.
It has no predecessor which is white sufficiently far to the left.
-/

@[expose] public section
namespace Rule30PreimageResearch
open Ruliology.CellularAutomata.Rule30Jen (rule)

def step (x : Int → Bool) (p : Int) := rule (x (p-1)) (x p) (x (p+1))

def pulseTarget (U p : Int) : Bool := decide (p = -1 ∨ p = 0 ∨ p = 1 ∨ p = U)

def unit (U p : Int) : Bool := decide (p = U)

def diffStep (A B h : Int → Bool) (p : Int) : Bool :=
  xor (xor (h (p-1)) ((! B (p+1)) && h p)) ((! A p) && h (p+1))

def Subset (A B h : Int → Bool) : Prop := ∀ p, (h p && xor (A p) (B p)) = h p

def Common (A B h : Int → Bool) : Prop := ∀ p,
  (xor (A (p+1)) (B (p+1)) && h p) = (xor (A p) (B p) && h (p+1))

theorem recombination_local : ∀ al ac ar bl bc br hl hc hr : Bool,
    (hr && xor ar br) = hr →
    ((xor ar br) && hc) = ((xor ac bc) && hr) →
    rule (xor bl hl) (xor bc hc) (xor br hr) =
      xor (rule bl bc br) (xor (xor hl ((!br) && hc)) ((!ac) && hr)) := by
  decide +kernel

theorem recombination (A B h : Int → Bool) (hs : Subset A B h) (hw : Common A B h)
    (p : Int) : step (fun p => xor (B p) (h p)) p = xor (step B p) (diffStep A B h p) := by
  exact recombination_local (A (p-1)) (A p) (A (p+1)) (B (p-1)) (B p) (B (p+1))
    (h (p-1)) (h p) (h (p+1)) (hs (p+1)) (hw p)

theorem first_seed_pulse (U : Int) (hU : 2 ≤ U) (p : Int) :
    xor (step (unit 0) p) (unit U p) = pulseTarget U p := by
  by_cases h1 : p = -1
  · subst p; simp [step, unit, rule, pulseTarget]; omega
  by_cases h0 : p = 0
  · subst p; simp [step, unit, rule, pulseTarget]; omega
  by_cases h2 : p = 1
  · subst p; simp [step, unit, rule, pulseTarget]; omega
  have hm : p-1 ≠ 0 := by omega
  have hp : p+1 ≠ 0 := by omega
  simp only [step, unit, hm, hp, h0, decide_false, rule, Bool.false_or,
    Bool.xor_false, Bool.false_xor, pulseTarget]
  by_cases hu : p=U <;> simp_all

theorem white_left {x : Int → Bool} {lo : Int}
    (hx : ∀ p, p < lo → x p = false)
    (hy : ∀ p, p < -1 → step x p = false) :
    ∀ p, p < 0 → x p = false := by
  have key : ∀ n : Nat, ∀ p : Int, p < lo + n → p < 0 → x p = false := by
    intro n
    induction n with
    | zero => intro p hp _; exact hx p (by omega)
    | succ n ih =>
      intro p hp hn
      by_cases hold : p < lo + n
      · exact ih p hold hn
      · have h1 := ih (p-1) (by omega) (by omega)
        have h2 := ih (p-2) (by omega) (by omega)
        have h := hy (p-1) (by omega)
        have a : p-1-1=p-2 := by omega
        have b : p-1+1=p := by omega
        simpa [step, a, b, h1, h2, rule] using h
  intro p hp
  exact key (p-lo+1).toNat p (by omega) hp

theorem pulseTarget_no_leftFinite_preimage (U : Int) (hU : 2 ≤ U)
    (x : Int → Bool) (lo : Int) (hx : ∀ p, p < lo → x p = false) :
    ¬ (∀ p, step x p = pulseTarget U p) := by
  intro he
  have hw := white_left hx (fun p hp => by
    have ht : pulseTarget U p = false := by
      simp only [pulseTarget, decide_eq_false_iff_not]
      omega
    exact (he p).trans ht)
  have hzero : x 0 = true := by
    have h := he (-1)
    simpa [step, rule, hw (-2) (by omega), hw (-1) (by omega), pulseTarget] using h
  have hone : x 1 = false ∧ x 2 = false := by
    have h := he 1
    simp only [step, (by omega : (1 : Int)-1=0), (by omega : (1 : Int)+1=2),
      hzero, pulseTarget] at h
    cases h1 : x 1 <;> cases h2 : x 2 <;> simp_all [rule]
  have gap : ∀ n : Nat, (n : Int)+2 ≤ U →
      x (n+1) = false ∧ x (n+2) = false := by
    intro n
    induction n with
    | zero => intro _; exact hone
    | succ n ih =>
      intro hle
      obtain ⟨hl,hc⟩ := ih (by omega)
      have hp := he ((n : Int)+2)
      have hp0 : pulseTarget U ((n : Int)+2) = false := by
        simp [pulseTarget]; omega
      have a : (n : Int)+2-1=(n : Int)+1 := by omega
      have b : (n : Int)+2+1=(n : Int)+3 := by omega
      have hr : x ((n : Int)+3) = false := by
        simpa [step, a, b, hl, hc, hp0, rule] using hp
      exact ⟨by simpa [Int.add_assoc] using hc, by simpa [Int.add_assoc] using hr⟩
  have hu0 : x U = false := by
    have hi : ((U-2).toNat : Int)+2=U := by omega
    rw [← hi]
    exact (gap (U-2).toNat (by omega)).2
  have hum : x (U-1) = false := by
    by_cases heq : U=2
    · simpa [heq] using hone.1
    · have hi : ((U-2).toNat : Int)+1=U-1 := by omega
      rw [← hi]
      exact (gap (U-2).toNat (by omega)).1
  have hup : x (U+1) = true := by
    have h := he U
    simpa [step, rule, hu0, hum, pulseTarget] using h
  have h := he (U+1)
  have a : U+1-1=U := by omega
  simp [step, rule, a, hu0, hup, pulseTarget] at h
  omega

theorem no_restricted_lift (U : Int) (hU : 2 ≤ U) (A h : Int → Bool) (lo : Int)
    (hl : ∀ p, p < lo → h p = false)
    (hs : Subset A (unit 0) h) (hw : Common A (unit 0) h) :
    ¬ (∀ p, diffStep A (unit 0) h p = unit U p) := by
  intro he
  apply pulseTarget_no_leftFinite_preimage U hU (fun p => xor (unit 0 p) (h p))
    (min lo 0)
  · intro p hp
    have hz : unit 0 p = false := by
      simp only [unit, decide_eq_false_iff_not]; omega
    rw [hz, hl p (by omega)]
    rfl
  · intro p
    rw [recombination A (unit 0) h hs hw p, he p]
    exact first_seed_pulse U hU p

end Rule30PreimageResearch
