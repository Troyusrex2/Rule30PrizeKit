module
public import Rule30PhysicalDefectBudgetResearch

/-! Finite-horizon charging for a forced Boolean recurrence. An injection at
time u first affects the reading at u+1. The weights retain its entire
survival multiplicity; no upper estimate for these weights is asserted. -/
@[expose] public section
namespace Rule30PhysicalDefectChargeResearch
open Rule30PhysicalDefectBudgetResearch Ruliology.CellularAutomata Rule30Jen

def bit : Bool → Nat | false => 0 | true => 1

def sumFrom (f : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | s, n+1 => f s + sumFrom f (s+1) n

/-- Product of the persistence bits on `[s,s+n)`; empty product is one. -/
def survival (a : Nat → Bool) : Nat → Nat → Nat
  | _, 0 => 1
  | s, n+1 => bit (a s) * survival a (s+1) n

/-- Number of masked readings reached from an initial contribution at s. -/
def weight (a mask : Nat → Bool) : Nat → Nat → Nat
  | _, 0 => 0
  | s, n+1 => bit (mask s) + bit (a s) * weight a mask (s+1) n

def injected (a b mask : Nat → Bool) : Nat → Nat → Nat
  | _, 0 => 0
  | s, n+1 => bit (b s) * weight a mask (s+1) n + injected a b mask (s+1) n

theorem bit_and (a b : Bool) : bit (a && b)=bit a * bit b := by
  cases a <;> cases b <;> rfl

theorem sumFrom_congr {f g : Nat → Nat} (s n : Nat)
    (h : ∀ t, s≤t → t<s+n → f t=g t) : sumFrom f s n=sumFrom g s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [sumFrom,sumFrom,h s (by omega) (by omega),ih (s+1) (by intros; apply h <;> omega)]

theorem sumFrom_mul (c : Nat) (f : Nat → Nat) (s n : Nat) :
    sumFrom (fun t => c*f t) s n=c*sumFrom f s n := by
  induction n generalizing s with
  | zero => simp [sumFrom]
  | succ n ih => simp only [sumFrom,ih,Nat.mul_add]

theorem weight_expanded (a mask : Nat → Bool) (s n : Nat) :
    weight a mask s n =
      sumFrom (fun t => bit (mask t)*survival a s (t-s)) s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [weight,sumFrom,Nat.sub_self,survival,Nat.mul_one,ih]
      congr 1
      rw [← sumFrom_mul]
      apply sumFrom_congr
      intro t ht _
      rw [show t-s=(t-(s+1))+1 by omega,survival]
      simp only [Nat.mul_left_comm]

/-- The last possible nonzero injection is at s+n-2. The formal sum has
length n-1, so it is empty for n=0 or n=1. -/
theorem injected_expanded (a b mask : Nat → Bool) (s n : Nat) :
    injected a b mask s n =
      sumFrom (fun u => bit (b u)*weight a mask (u+1) (s+n-(u+1))) s (n-1) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => simp [injected,weight,sumFrom]
      | succ n =>
          rw [injected,ih]
          change bit (b s)*weight a mask (s+1) (n+1) +
            sumFrom (fun u => bit (b u)*weight a mask (u+1) ((s+1)+(n+1)-(u+1))) (s+1) n =
            bit (b s)*weight a mask (s+1) (s+(n+1+1)-(s+1)) +
            sumFrom (fun u => bit (b u)*weight a mask (u+1) (s+(n+1+1)-(u+1))) (s+1) n
          rw [show s+(n+1+1)-(s+1)=n+1 by omega,
            show (s+1)+(n+1)=s+(n+1+1) by omega]

theorem count_as_sum (mask x : Nat → Bool) (s n : Nat) :
    intervalCount (fun t => mask t && x t) s (s+n)=
      sumFrom (fun t => bit (mask t)*bit (x t)) s n := by
  induction n generalizing s with
  | zero => simp [intervalCount,sumFrom]
  | succ n ih =>
      unfold intervalCount at ih ⊢
      simp only [Nat.add_sub_cancel_left,List.range'_succ,List.countP_cons,sumFrom]
      have h := ih (s+1)
      simp only [Nat.add_sub_cancel_left] at h
      rw [h]
      cases mask s <;> cases x s <;> simp [bit,Nat.add_comm]

/-- Generic finite-horizon charging inequality. The recurrence is required
only at and after s, and all survival multiplicities are retained. -/
theorem charge (x a b mask : Nat → Bool) (s n : Nat)
    (hx : ∀ t, s≤t → x (t+1)=xor (a t && x t) (b t)) :
    intervalCount (fun t => mask t && x t) s (s+n) ≤
      bit (x s)*weight a mask s n + injected a b mask s n := by
  rw [count_as_sum]
  induction n generalizing s with
  | zero => simp [sumFrom,weight,injected]
  | succ n ih =>
      have ht := ih (s+1) (fun t h => hx t (by omega))
      have hb : bit (x (s+1))≤bit (a s)*bit (x s)+bit (b s) := by
        rw [hx s (by omega)]
        cases a s <;> cases x s <;> cases b s <;> decide
      have hm := Nat.mul_le_mul_right (weight a mask (s+1) n) hb
      change bit (mask s)*bit (x s)+sumFrom (fun t => bit (mask t)*bit (x t)) (s+1) n ≤
        bit (x s)*(bit (mask s)+bit (a s)*weight a mask (s+1) n) +
          (bit (b s)*weight a mask (s+1) n+injected a b mask (s+1) n)
      have he : bit (x s)*(bit (mask s)+bit (a s)*weight a mask (s+1) n) +
          (bit (b s)*weight a mask (s+1) n+injected a b mask (s+1) n) =
        bit (mask s)*bit (x s)+(bit (a s)*bit (x s)+bit (b s))*weight a mask (s+1) n+
          injected a b mask (s+1) n := by
        simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_comm,Nat.add_assoc]
      rw [he]
      omega

/-- Literal physical CHARGE, including the initial contribution and the
strictly later readings of every forcing event. -/
theorem physical_charge {T Q n0 X : Nat}
    (hc : ∀ t, T≤t → cell (t+Q) 0=cell t 0)
    (hn0 : T+Q≤n0) (hX : n0≤X) :
    defectCount Q n0 X ≤
      bit (mismatch Q n0) *
        sumFrom (fun t => bit (!(cell t 0))*survival persists n0 (t-n0)) n0 (X-n0) +
      sumFrom (fun u => bit (forcing Q u) *
        sumFrom (fun t => bit (!(cell t 0))*survival persists (u+1) (t-(u+1)))
          (u+1) (X-(u+1))) n0 (X-n0-1) := by
  have hh := charge (mismatch Q) persists (forcing Q) (fun t => !(cell t 0)) n0 (X-n0)
    (fun t ht => periodic_mismatch_step hc t (by omega))
  rw [show n0+(X-n0)=X by omega] at hh
  change defectCount Q n0 X ≤ _ at hh
  rw [weight_expanded,injected_expanded] at hh
  rw [show n0+(X-n0)=X by omega] at hh
  simpa only [weight_expanded] using hh

end Rule30PhysicalDefectChargeResearch
