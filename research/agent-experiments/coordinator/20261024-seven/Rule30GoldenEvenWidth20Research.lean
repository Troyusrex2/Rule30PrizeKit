import Rule30GoldenEvenSupportResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenEvenWidth20Research
open Rule30GoldenEvenSupportResearch

theorem check20 : check 20 0 48 = true := by decide +kernel

theorem noGoldenEvenWidth20 : NoGoldenEvenWidth 20 := by
  apply no_golden_even_width_of_checks 20 20 48 (by omega)
  intro c hc
  have : c = 0 := by simpa using hc
  subst c
  exact check20

end Rule30GoldenEvenWidth20Research
