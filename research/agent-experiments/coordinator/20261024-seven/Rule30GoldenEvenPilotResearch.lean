import Rule30GoldenEvenSupportResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenEvenPilotResearch
open Rule30GoldenEvenSupportResearch

theorem check12 : check 12 0 64 = true := by decide +kernel

theorem noGoldenEvenWidth12 : NoGoldenEvenWidth 12 := by
  apply no_golden_even_width_of_checks 12 12 64 (by omega)
  intro c hc
  have : c = 0 := by simpa using hc
  subst c
  exact check12

end Rule30GoldenEvenPilotResearch
