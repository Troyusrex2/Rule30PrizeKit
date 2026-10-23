module

public import Ruliology.CellularAutomata.Rule30RestrictedBackwardTubeResearch
public import Ruliology.CellularAutomata.Rule30Certificates.Rule30Tube10101Research

/-! Kernel-checked finite certificate support for the five-bit white-padding theorem. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30WhitePadding10101Research
open Rule30Jen Rule30Realization Rule30StripCertificates
open Rule30RestrictedBackwardTubeResearch

/-- The first five-bit exceptional tail, proved with an endpoint-conditioned tube. -/
theorem no_padding_10101_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i
      (List.replicate r false ++ [true,false,true,false,true]) := by
  apply no_padding_of_endpoint_tube hlo hzero i Rule30Tube10101Research.tail
    16 24 Rule30Tube10101Research.Z Rule30Tube10101Research.Q
    Rule30Tube10101Research.P Rule30Tube10101Research.S
    (fun d => decide (d ≤ 8)) (fun _ => false) (by decide)
    Rule30Tube10101Research.Zzero Rule30Tube10101Research.Zfixed
    Rule30Tube10101Research.Szero Rule30Tube10101Research.Pend
    Rule30Tube10101Research.Qstart Rule30Tube10101Research.Qend
  · intro d hd
    exact Rule30Tube10101Research.Qstep d hd
  · intro j hj
    exact Rule30Tube10101Research.Pstep j hj
  · intro j hj
    exact Rule30Tube10101Research.Sstep j hj
  · exact Rule30Tube10101Research.Qforce
  · exact Rule30Tube10101Research.Pforce
  · simpa only [Rule30Tube10101Research.tail, List.length_cons, List.length_nil] using
      (show 10*5+11 ≤ r by omega)
  · simpa only [Rule30Tube10101Research.tail, List.length_cons, List.length_nil] using
      (show 16-1+9*(5+1) ≤ r by omega)
  · omega

theorem no_padding_10101 (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord
      (List.replicate r false ++ [true,false,true,false,true]) := by
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed, show p ≠ 0 by omega]
  have h := no_padding_10101_leftFinite (x := seed) (lo := 0) (by decide) hzero 0 r hr
  simpa only [Rule30FiniteStripsResearch.EventuallyWord,
    Rule30StripCertificates.EventuallyWord, evol_seed] using h

theorem no_padding_10101_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i
      (List.replicate r false ++ [true,false,true,false,true]) := by
  obtain ⟨lo,hlo,hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_padding_10101_leftFinite hlo hzero i r hr

end Ruliology.CellularAutomata.Rule30WhitePadding10101Research
