module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicOrbitCheck09
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem checked : (orbits.drop 288 |>.take 2).all checkOrbit=true := by decide +kernel
end Rule30CubicOrbitCheck09
