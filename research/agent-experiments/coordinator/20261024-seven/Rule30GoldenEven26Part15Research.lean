import Rule30GoldenEvenSupportResearch

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Rule30GoldenEven26Part15Research
open Rule30GoldenEvenSupportResearch

theorem check_60 : check 20 60 61 = true := by decide +kernel

theorem check_61 : check 20 61 61 = true := by decide +kernel

theorem check_62 : check 20 62 61 = true := by decide +kernel

theorem check_63 : check 20 63 61 = true := by decide +kernel

end Rule30GoldenEven26Part15Research
