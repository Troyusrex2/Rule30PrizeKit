import CedarSafetySoundness

/-! Transition cover alone admits every nonzero Boolean temporal profile
with a power-of-two returning period. These chains are NOT asserted to
satisfy the shared two-predecessor OR recurrence of finite-white Rule30. -/
namespace CedarTCObstruction
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

abbrev Profile := Nat → Bool
def zero : Profile := fun _ => false
def one : Profile := fun _ => true
def derivative (b : Profile) : Profile := fun t => xor (b t) (b (t+1))
def iter : Nat → Profile → Profile
  | 0, b => b
  | n+1, b => derivative (iter n b)
def Periodic (p : Nat) (b : Profile) : Prop := ∀ t, b (t+p) = b t

/-- The two pointwise inclusions a <= Delta b <= a OR a_next. -/
def TC (a b : Profile) : Prop := ∀ t,
  (a t = true → derivative b t = true) ∧
  (derivative b t = true → a t = true ∨ a (t+1) = true)

theorem xor_cancel_middle (a b c : Bool) :
    xor (xor a b) (xor b c) = xor a c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem xor_false_eq (a b : Bool) (h : xor a b = false) : a = b := by
  cases a <;> cases b <;> simp_all

theorem iter_add (n m : Nat) (b : Profile) : iter (n+m) b = iter n (iter m b) := by
  induction n with
  | zero => simp only [Nat.zero_add,iter]
  | succ n ih => simpa only [Nat.succ_add,iter] using congrArg derivative ih

theorem derivative_power_two (k : Nat) (b : Profile) :
    iter (2^k) b = fun t => xor (b t) (b (t+2^k)) := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ,Nat.mul_two,iter_add]
    simp only [ih]
    funext t
    simpa only [Nat.add_assoc] using
      xor_cancel_middle (b t) (b (t+2^k)) (b (t+(2^k+2^k)))

theorem periodic_annihilation (k : Nat) (b : Profile) (hp : Periodic (2^k) b) :
    iter (2^k) b = zero := by
  rw [derivative_power_two]
  funext t
  rw [hp t]
  cases b t <;> rfl

theorem derivative_periodic (p : Nat) (b : Profile) (hp : Periodic p b) :
    Periodic p (derivative b) := by
  intro t
  dsimp only [derivative]
  rw [hp t, show t+p+1 = t+1+p by omega, hp (t+1)]

theorem iter_periodic (n p : Nat) (b : Profile) (hp : Periodic p b) :
    Periodic p (iter n b) := by
  induction n with
  | zero => exact hp
  | succ n ih => exact derivative_periodic p (iter n b) ih

theorem derivative_zero_constant (b : Profile) (hz : derivative b = zero) :
    b = fun _ => b 0 := by
  have hs : ∀ t, b (t+1) = b t := by
    intro t
    have h := congrFun hz t
    exact (xor_false_eq (b t) (b (t+1)) h).symm
  funext t
  induction t with
  | zero => rfl
  | succ t ih => exact (hs t).trans ih

theorem nonzero_derivative_zero_is_one (b : Profile)
    (hz : derivative b = zero) (hb : b ≠ zero) : b = one := by
  have hc := derivative_zero_constant b hz
  cases hv : b 0 with
  | false =>
    exfalso
    apply hb
    funext t
    change b t = false
    exact (congrFun hc t).trans hv
  | true =>
    funext t
    change b t = true
    exact (congrFun hc t).trans hv

theorem exists_last_nonzero (n : Nat) (b : Profile)
    (hz : iter n b = zero) (hb : b ≠ zero) :
    ∃ m : Nat, m < n ∧ iter m b = one := by
  induction n generalizing b with
  | zero => exact False.elim (hb hz)
  | succ n ih =>
    by_cases hd : derivative b = zero
    · exact ⟨0,Nat.zero_lt_succ n,nonzero_derivative_zero_is_one b hd hb⟩
    · have hh : iter n (derivative b) = zero := by
        rw [iter_add] at hz
        exact hz
      obtain ⟨m,hm,hmb⟩ := ih (derivative b) hh hd
      refine ⟨m+1,by omega,?_⟩
      rw [iter_add]
      exact hmb

theorem derivative_pair_tc (b : Profile) : TC (derivative b) b := by
  intro t
  exact ⟨fun h => h, fun h => Or.inl h⟩

theorem white_pair_tc : TC zero zero := by
  intro t
  constructor <;> simp [zero,derivative]

theorem white_to_black_tc : TC zero one := by
  intro t
  constructor <;> simp [zero,one,derivative]

/-- Every nonzero power-of-two-periodic terminal profile has a normalized
TC chain. No shared OR recurrence is included among the conclusions. -/
theorem normalized_tc_chain (k : Nat) (b : Profile)
    (hp : Periodic (2^k) b) (hb : b ≠ zero) :
    ∃ m : Nat, m < 2^k ∧ ∃ x : Nat → Profile,
      x 0 = one ∧ x m = b ∧ (∀ i, Periodic (2^k) (x i)) ∧
      (∀ i, i < m → derivative (x (i+1)) = x i) ∧
      (∀ i, i < m → TC (x i) (x (i+1))) := by
  obtain ⟨m,hm,hmb⟩ := exists_last_nonzero (2^k) b (periodic_annihilation k b hp) hb
  let x : Nat → Profile := fun i => iter (m-i) b
  have hd : ∀ i, i < m → derivative (x (i+1)) = x i := by
    intro i hi
    change derivative (iter (m-(i+1)) b) = iter (m-i) b
    rw [show m-i = (m-(i+1))+1 by omega]
    rfl
  refine ⟨m,hm,x,?_,?_,?_,hd,?_⟩
  · simpa [x] using hmb
  · simp [x,iter]
  · intro i
    exact iter_periodic (m-i) (2^k) b hp
  · intro i hi
    rw [← hd i hi]
    exact derivative_pair_tc (x (i+1))

end CedarTCObstruction
