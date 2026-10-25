import Rule30GoldenCompactBudgetResearch

/-! Prefix congruence for the exact compact decoder. These equations let
proof trees join already checked branches without normalizing entire
histories during every type comparison. -/

namespace Rule30GoldenCompactPathResearch
open Rule30GoldenCompactBudgetResearch (path child)

theorem path_congr {u v n : Nat}
    (h : ∀ i, i<n → u.testBit i=v.testBit i) : path u n=path v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [path,path,ih (fun i hi => h i (by omega)),h n (by omega)]

theorem path_or_pow_prefix (u n : Nat) : path (u ||| 2^n) n=path u n := by
  apply path_congr
  intro i hi
  rw [Nat.testBit_or,Nat.testBit_two_pow_of_ne (by omega),Bool.or_false]

theorem zero_extension (u n : Nat) (hu : u<2^n) :
    path u (n+1)=child n (path u n) false := by
  rw [path,Nat.testBit_lt_two_pow hu]

theorem one_extension (u n : Nat) :
    path (u ||| 2^n) (n+1)=child n (path u n) true := by
  rw [path,path_or_pow_prefix,Nat.testBit_or,Nat.testBit_two_pow_self,Bool.or_true]

end Rule30GoldenCompactPathResearch
