import Rule30VerifiedCoupledGoldenExtract

/-! A further forbidden word for the coupled free bits, at every onset and
for every right half, including infinite right halves. The finite light-cone
bridge is reused from Villafuerte/Antigravity's attributed, replayed block.
This theorem does not assert nonperiodicity or finite-support impossibility. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30CoupledSixWordResearch
open Ruliology.CellularAutomata
open Rule30Jen Rule30BlackRuns Rule30PeriodTwoSideways Rule30PeriodTwoCoupled
open Rule30Ether (drv drv_col0)

def bad (l : List Bool) : Bool :=
  l.getD 0 false && !l.getD 2 false && l.getD 4 false &&
    !l.getD 6 false && !l.getD 8 false && l.getD 10 false

theorem six_check : (allLists 13).all
    (fun l => !bad (Rule30PeriodTwo.col1 (Rule30PeriodTwo.alt 11) l)) = true := by
  decide +kernel

theorem no_u_101001 (R : Nat → Bool) (s : Nat) :
    ¬ (u R s=true ∧ u R (s+1)=false ∧ u R (s+2)=true ∧
       u R (s+3)=false ∧ u R (s+4)=false ∧ u R (s+5)=true) := by
  intro ⟨h0,h1,h2,h3,h4,h5⟩
  have hc : ∀ i, (hi : i < (Rule30PeriodTwo.alt 11).length) →
      drv altCol R (2*s+1+i) 0 = (Rule30PeriodTwo.alt 11)[i] := by
    intro i hi
    simp only [Rule30PeriodTwo.alt,List.getElem_map,List.getElem_range]
    rw [drv_col0]
    unfold altCol
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · have h1 : (2*s+1+i)%2=1 := by omega
      simp [h,h1]
    · have h1 : (2*s+1+i)%2=0 := by omega
      simp [h,h1]
  have hw := Rule30Submission.col1_drvRow R (Rule30PeriodTwo.alt 11) (2*s+1) 1 hc
  rw [Rule30PeriodTwo.alt_length] at hw
  have hmem : Rule30Submission.drvRow altCol R (2*s+1) 0 13 ∈ allLists 13 := by
    have h := mem_allLists (Rule30Submission.drvRow altCol R (2*s+1) 0 13)
    rwa [Rule30Submission.length_drvRow] at h
  have hck := List.all_eq_true.1 six_check _ hmem
  rw [hw] at hck
  have hv : ∀ i, i<11 →
      ((List.range 11).map (fun i => drv altCol R (2*s+1+i) 1)).getD i false =
        drv altCol R (2*s+1+i) 1 := by
    intro i hi
    simp [List.getD_eq_getElem?_getD,hi]
  have hu (i : Nat) : u R (s+i) = drv altCol R (2*s+1+2*i) 1 := by
    unfold u
    congr 1
    omega
  unfold bad at hck
  rw [hv 0 (by omega),hv 2 (by omega),hv 4 (by omega),hv 6 (by omega),
    hv 8 (by omega),hv 10 (by omega)] at hck
  rw [←hu 0,←hu 1,←hu 2,←hu 3,←hu 4,←hu 5] at hck
  simp only [Nat.add_zero,h0,h1,h2,h3,h4,h5] at hck
  cases hck

theorem psi_free_no010110 (R : Nat → Bool) (s : Nat) :
    ¬ (Rule30ZeroBoundary.zrow (Psi R) (2*s+1) 1=false ∧
       Rule30ZeroBoundary.zrow (Psi R) (2*(s+1)+1) 1=true ∧
       Rule30ZeroBoundary.zrow (Psi R) (2*(s+2)+1) 1=false ∧
       Rule30ZeroBoundary.zrow (Psi R) (2*(s+3)+1) 1=true ∧
       Rule30ZeroBoundary.zrow (Psi R) (2*(s+4)+1) 1=true ∧
       Rule30ZeroBoundary.zrow (Psi R) (2*(s+5)+1) 1=false) := by
  intro h
  apply no_u_101001 R s
  simpa [Psi_free,u] using h

end Rule30CoupledSixWordResearch
