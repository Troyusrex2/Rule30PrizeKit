module
public import Ruliology.CellularAutomata.Rule30Prize
public import Mathlib.Data.Nat.Choose.Lucas

/-! Standard Lucas support implication, proved from Mathlib's Lucas theorem.
This is a bridge lemma, with no novelty or nonperiodicity claim. -/
@[expose] public section
namespace Rule30LucasMaskResearch

theorem choose_odd_submask (n k : Nat) (hc : n.choose k % 2=1) : k &&& n=k := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    by_cases hn : n=0
    · subst n
      by_cases hk : k=0
      · subst k; rfl
      · have hz : Nat.choose 0 k=0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hz] at hc
        contradiction
    have hdiv : n/2<n := Nat.div_lt_self (by omega) (by omega)
    have hluc : n.choose k % 2 =
        (Nat.choose (n%2) (k%2) * Nat.choose (n/2) (k/2))%2 :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat (p:=2)
    have hb : Nat.choose (n/2) (k/2)%2=1 := by
      by_cases hz : Nat.choose (n/2) (k/2)%2=0
      · rw [Nat.mul_mod,hz,Nat.mul_zero,Nat.zero_mod,hc] at hluc
        contradiction
      · have hlt := Nat.mod_lt (Nat.choose (n/2) (k/2)) (by omega : 0<2)
        omega
    have hi := ih (n/2) hdiv (k/2) hb
    have hlo : k%2≤n%2 := by
      have hkn := Nat.mod_lt k (by omega : 0<2)
      have hnn := Nat.mod_lt n (by omega : 0<2)
      by_cases hk0 : k%2=0
      · omega
      · have hk1 : k%2=1 := by omega
        by_cases hn0 : n%2=0
        · simp [hn0,hk1,hc] at hluc
        · omega
    have hquot : (k &&& n)/2=k/2 := by rw [Nat.and_div_two,hi]
    have hrem : (k &&& n)%2=k%2 := by
      have hm : (k &&& n)%2=(k%2) &&& (n%2) := Nat.and_mod_two_pow (n:=1)
      rw [hm]
      have hklt := Nat.mod_lt k (by omega : 0<2)
      have hnlt := Nat.mod_lt n (by omega : 0<2)
      by_cases hk0 : k%2=0
      · simp [hk0]
      · have hk1 : k%2=1 := by omega
        have hn1 : n%2=1 := by omega
        simp [hk1,hn1]
    have ha := Nat.mod_add_div (k &&& n) 2
    have hk := Nat.mod_add_div k 2
    omega

end Rule30LucasMaskResearch
