module
public import Ruliology.CellularAutomata.Rule30SixTailReductionResearch
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100001Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100011Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100101Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward100111Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101001Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101011Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101101Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward101111Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110001Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110011Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110101Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward110111Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111001Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111011Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111101Research
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward111111Research

@[expose] public section
/-! Every Boolean tail of length at most six is excluded after 77 white phases.
The six-bit core proofs use finite backward-vacuum obstructions; shorter cores
use the prior five-tail theorem. This is a partial result, not Problem 1. -/
namespace Ruliology.CellularAutomata.Rule30SixTailResearch
open Rule30Jen Rule30Realization Rule30SixTailReductionResearch

theorem no_six_core {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (hv : v ∈ sixCores) (r : Nat) (hr : 77 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ v) := by
  simp only [sixCores, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Rule30SixTailCertificatesResearch.C100001.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C100011.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C100101.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C100111.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C101001.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C101011.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C101101.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C101111.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C110001.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C110011.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C110101.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C110111.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C111001.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C111011.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C111101.no_padding hlo hzero i r (by omega)
  · exact Rule30SixTailCertificatesResearch.C111111.no_padding hlo hzero i r (by omega)

/-- Every column of every leftmost-black start, with unrestricted transient. -/
theorem no_six_tail_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (hu : u.length ≤ 6) (r : Nat) (hr : 77 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ u) :=
  no_six_tail_of_cores hlo hzero i (no_six_core hlo hzero i) u hu r hr

theorem no_six_tail_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (u : List Bool) (hu : u.length ≤ 6) (r : Nat) (hr : 77 ≤ r) :
    ¬ Rule30FiniteStripsResearch.EventuallyWord x i (List.replicate r false ++ u) := by
  obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_six_tail_leftFinite hlo hzero i u hu r hr

theorem no_six_tail_seed (u : List Bool) (hu : u.length ≤ 6) (r : Nat) (hr : 77 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate r false ++ u) := by
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed, show p ≠ 0 by omega]
  have h := no_six_tail_leftFinite (x := seed) (lo := 0) (by decide) hzero 0 u hu r hr
  simpa only [Rule30FiniteStripsResearch.EventuallyWord,
    Rule30StripCertificates.EventuallyWord, evol_seed] using h
end Ruliology.CellularAutomata.Rule30SixTailResearch
