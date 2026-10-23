module

public import Ruliology.CellularAutomata.Rule30StripCertificates

@[expose] public section

/-! Small vacuum-free suffix certificates, starting from every strip state.
Both values of the unknown right boundary are included at every step.
These finite facts are replayed by Lean's kernel, without native evaluation. -/
namespace Ruliology.CellularAutomata.Rule30ForbiddenSuffixCertificatesResearch
open Rule30StripCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def suffix011 : List Bool := [false, true, true]
def suffix001001 : List Bool := [false, false, true, false, false, true]
def suffix111001 : List Bool := [true, true, true, false, false, true]

theorem safe011 : (applyWord 5 suffix011 (fullSet 5)).testBit 0 = false := by
  decide +kernel

theorem safe001001 : (applyWord 6 suffix001001 (fullSet 6)).testBit 0 = false := by
  decide +kernel

theorem safe111001 : (applyWord 6 suffix111001 (fullSet 6)).testBit 0 = false := by
  decide +kernel

end Ruliology.CellularAutomata.Rule30ForbiddenSuffixCertificatesResearch
