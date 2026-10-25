import Rule30GoldenCriticalDriftResearch

/-! A quantitative necessary condition for a finite constrained Golden row.
Jen's clock prevents an arbitrarily long defect plateau. Consequently the
defect count grows at least once per explicit dyadic scale. No counting
charge is asserted; the coupled period-two and full prize problems stay open.
-/
namespace Rule30GoldenQuantitativeDriftResearch
open Ruliology.CellularAutomata
open Rule30GoldenDFAResearch (Golden)
open Rule30GoldenCriticalDriftResearch
open Rule30CoupledChargeReductionResearch (zeros)

theorem period_five_window {s : Nat -> Bool} (hg : Golden s) (N M : Nat)
    (hz : forall k, N<=k -> k<=M+5 -> s k=false -> trailing s k=4) :
    forall n, N<=n -> n<=M -> s (n+5)=s n := by
  intro n hn hm
  cases hs : s n with
  | false =>
    have hnext (j : Nat) (hj : 1<=j) (hj4 : j<=4) : s (n+j)=true := by
      cases hv : s (n+j) with
      | true => rfl
      | false =>
        have hr := hz (n+j) (by omega) (by omega) hv
        have h := trailing_bit s (n+j) (j-1) (by omega)
        have he : n+j-((j-1)+1)=n := by omega
        rw [he,hs] at h
        cases h
    cases hv : s (n+5) with
    | false => rfl
    | true =>
      exact False.elim (hg.2 (n+1) ⟨hnext 1 (by omega) (by omega),
        by simpa [Nat.add_assoc] using hnext 2 (by omega) (by omega),
        by simpa [Nat.add_assoc] using hnext 3 (by omega) (by omega),
        by simpa [Nat.add_assoc] using hnext 4 (by omega) (by omega),
        by simpa [Nat.add_assoc] using hv⟩)
  | true =>
    cases hv : s (n+5) with
    | true => rfl
    | false =>
      have hr := hz (n+5) (by omega) (by omega) hv
      have hprev (j : Nat) (hj : 1<=j) (hj4 : j<=4) : s (n+j)=true := by
        have h := trailing_bit s (n+5) (4-j) (by omega)
        have he : n+5-((4-j)+1)=n+j := by omega
        simpa only [he] using h
      exact False.elim (hg.2 n ⟨by simpa using hs,hprev 1 (by omega) (by omega),
        hprev 2 (by omega) (by omega),hprev 3 (by omega) (by omega),hprev 4 (by omega) (by omega)⟩)

theorem period_five_of_defect_plateau {s : Nat -> Bool} (hg : Golden s) (N M : Nat)
    (hconst : defects s N=defects s (M+6)) :
    forall n, N<=n -> n<=M -> s (n+5)=s n := by
  apply period_five_window hg N M
  intro k hk hM hs
  have h0 := defects_mono s hk
  have h1 := defects_mono s (show k<=k+1 by omega)
  have h2 := defects_mono s (show k+1<=M+6 by omega)
  have he : defects s (k+1)=defects s k := by omega
  have hb := trailing_le_four hg k
  simp only [defects,hs,Bool.false_eq_true,↓reduceIte] at he
  omega

theorem defect_increase_by_clock {L : Nat -> Bool} {m : Nat}
    (hm : 1<=m) (hedge : L m=true)
    (hfin : forall k, m<k -> L k=false) (hX : Rule30ZeroBoundary.InX L)
    (hg : Golden (fun k => Rule30ZeroBoundary.zrow L (2*k+1) 1)) (N : Nat) :
    defects (fun k => Rule30ZeroBoundary.zrow L (2*k+1) 1) N+1 <=
      defects (fun k => Rule30ZeroBoundary.zrow L (2*k+1) 1) (2*N+m+16) := by
  let s := fun k => Rule30ZeroBoundary.zrow L (2*k+1) 1
  have hmono := defects_mono s (show N<=2*N+m+16 by omega)
  by_cases he : defects s N=defects s (2*N+m+16)
  · have hp := period_five_of_defect_plateau hg N (N+(N+m+10))
      (by simpa only [show N+(N+m+10)+6=2*N+m+16 by omega] using he)
    have hc := Rule30ZeroBoundary.free_bits_clock hm hedge hfin hX
      (s₀:=N) (ℓ:=N+m+10) (p:=5) (by decide)
      (fun k hk hM => hp k hk (by omega))
    omega
  · change defects s N+1<=defects s (2*N+m+16)
    omega

def cutoff (m : Nat) : Nat -> Nat
  | 0 => 0
  | k+1 => 2*cutoff m k+m+16

theorem cutoff_exponential (m k : Nat) : cutoff m k+(m+16)=(m+16)*2^k := by
  induction k with
  | zero => simp [cutoff]
  | succ k ih =>
    rw [cutoff,Nat.pow_succ]
    calc
      2*cutoff m k+m+16+(m+16)=2*(cutoff m k+(m+16)) := by omega
      _=2*((m+16)*2^k) := by rw [ih]
      _=((m+16)*2^k)*2 := Nat.mul_comm _ _
      _=(m+16)*(2^k*2) := Nat.mul_assoc _ _ _

theorem defects_at_cutoff {L : Nat -> Bool} {m : Nat}
    (hm : 1<=m) (hedge : L m=true)
    (hfin : forall k, m<k -> L k=false) (hX : Rule30ZeroBoundary.InX L)
    (hg : Golden (fun k => Rule30ZeroBoundary.zrow L (2*k+1) 1)) (k : Nat) :
    k<=defects (fun j => Rule30ZeroBoundary.zrow L (2*j+1) 1) (cutoff m k) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have h := defect_increase_by_clock hm hedge hfin hX hg (cutoff m k)
    rw [cutoff]
    omega

theorem excess_at_exponential_cutoff {L : Nat -> Bool} {m : Nat}
    (hm : 1<=m) (hedge : L m=true)
    (hfin : forall k, m<k -> L k=false) (hX : Rule30ZeroBoundary.InX L)
    (hg : Golden (fun k => Rule30ZeroBoundary.zrow L (2*k+1) 1)) (k : Nat) :
    cutoff m (k+5)+k <
      5*zeros (fun j => Rule30ZeroBoundary.zrow L (2*j+1) 1) (cutoff m (k+5)) := by
  have hd := defects_at_cutoff hm hedge hfin hX hg (k+5)
  have hi := count_identity hg (cutoff m (k+5))
  have ht := trailing_le_four hg (cutoff m (k+5))
  omega

end Rule30GoldenQuantitativeDriftResearch
