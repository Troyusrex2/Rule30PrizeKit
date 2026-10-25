import Rule30VerifiedCoupledGoldenExtract

/-! Soundness of finite forbidden-word checks, uniformly over every onset
and arbitrary right halves. The light-cone bridge is attributed to the
Villafuerte/Antigravity block imported above. -/

namespace Rule30CoupledWordCertificateResearch
open Ruliology.CellularAutomata
open Rule30Jen Rule30BlackRuns Rule30PeriodTwoSideways Rule30PeriodTwoCoupled
open Rule30Ether (drv drv_col0)

def sample (l : List Bool) (n : Nat) : List Bool :=
  (List.range n).map (fun i => !l.getD (2*i) false)

def check (w : List Bool) : Bool := (allLists (2*w.length-1)).all (fun l =>
  sample (Rule30PeriodTwo.col1 (Rule30PeriodTwo.alt (2*w.length-1)) l) w.length != w)

theorem col1_drvRow_exact (R : Nat → Bool) : ∀ (cs : List Bool) (t : Nat),
    (∀ i, (hi : i<cs.length) → drv altCol R (t+i) 0=cs[i]) →
    Rule30PeriodTwo.col1 cs (Rule30Submission.drvRow altCol R t 0 cs.length) =
      (List.range cs.length).map (fun i => drv altCol R (t+i) 1)
  | [],t,_ => rfl
  | c::cs,t,h => by
    have h0 : drv altCol R t 0=c := h 0 (by simp)
    have hs : Rule30BlackRuns.stepRow c
        (Rule30Submission.drvRow altCol R t 0 (cs.length+1)) =
          Rule30Submission.drvRow altCol R (t+1) 0 cs.length := by
      rw [←h0]
      exact Rule30Submission.stepRow_drvRow altCol R t cs.length 0
    have ih := col1_drvRow_exact R cs (t+1) (fun i hi => by
      have hh := h (i+1) (by simp;omega)
      rw [show t+1+i=t+(i+1) by omega]
      simpa using hh)
    change (Rule30Submission.drvRow altCol R t 0 (cs.length+1)).headD false ::
      Rule30PeriodTwo.col1 cs (Rule30BlackRuns.stepRow c
        (Rule30Submission.drvRow altCol R t 0 (cs.length+1))) = _
    rw [hs,ih,List.length_cons,List.range_succ_eq_map]
    simp only [Rule30Submission.drvRow,List.headD_cons,List.map_cons,List.map_map,Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp]
    rw [show t+1+i=t+(i+1) by omega]

theorem sample_col1 (R : Nat → Bool) (s n : Nat) (hn : 0<n) :
    sample (Rule30PeriodTwo.col1 (Rule30PeriodTwo.alt (2*n-1))
      (Rule30Submission.drvRow altCol R (2*s+1) 0 (2*n-1))) n =
        (List.range n).map (fun i => !u R (s+i)) := by
  have hc : ∀ i, (hi : i < (Rule30PeriodTwo.alt (2*n-1)).length) →
      drv altCol R (2*s+1+i) 0 = (Rule30PeriodTwo.alt (2*n-1))[i] := by
    intro i hi
    simp only [Rule30PeriodTwo.alt,List.getElem_map,List.getElem_range]
    rw [drv_col0]
    unfold altCol
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · have h1 : (2*s+1+i)%2=1 := by omega
      simp [h,h1]
    · have h1 : (2*s+1+i)%2=0 := by omega
      simp [h,h1]
  have hw := col1_drvRow_exact R (Rule30PeriodTwo.alt (2*n-1)) (2*s+1) hc
  rw [Rule30PeriodTwo.alt_length] at hw
  unfold sample
  rw [hw]
  apply List.map_congr_left
  intro i hi
  have hi' : i<n := List.mem_range.mp hi
  have hh : 2*i<2*n-1 := by omega
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,hh,
    ↓reduceDIte,Option.map_some,Option.getD_some]
  unfold u
  congr 2
  omega

theorem forbidden_of_check {w : List Bool} (hn : 0<w.length) (hc : check w=true)
    (R : Nat → Bool) (s : Nat) : (List.range w.length).map (fun i => !u R (s+i)) ≠ w := by
  have hmem : Rule30Submission.drvRow altCol R (2*s+1) 0 (2*w.length-1) ∈ allLists (2*w.length-1) := by
    have h := mem_allLists (Rule30Submission.drvRow altCol R (2*s+1) 0 (2*w.length-1))
    rwa [Rule30Submission.length_drvRow] at h
  have hck := List.all_eq_true.1 hc _ hmem
  rw [sample_col1 R s w.length hn] at hck
  intro he
  rw [he] at hck
  simpa using hck

end Rule30CoupledWordCertificateResearch
