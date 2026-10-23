module

public import Ruliology.CellularAutomata.Rule30Certificates.TraceSepH15M2
public import Ruliology.CellularAutomata.Rule30Certificates.TraceSepH15M3

/-! A larger base case, with an unrestricted (possibly infinite) right half.
This bounded theorem does not prove the open global edge-recovery statement. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30TraceSeparationThreeResearch

open Rule30Realization Rule30TraceEdgeResearch Rule30TraceSeparationResearch

theorem certificate_two_three : Nat.land (edgeSignatures 15 2) (edgeSignatures 15 3) = 0 := by
  rw [Rule30TraceSeparationData.m2_full_mask,Rule30TraceSeparationData.m3_full_mask]
  decide

theorem separate_minus_two_minus_three {x y : Int → Bool}
    (hx : HasLeftEdge x (-2)) (hy : HasLeftEdge y (-3)) :
    ¬ (∀ t, t<15 → evol x t 0 = evol y t 0) :=
  no_common_trace_prefix (H:=15) (m:=2) (n:=3) (by decide) certificate_two_three hx hy

end Ruliology.CellularAutomata.Rule30TraceSeparationThreeResearch
