module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicOrbitCheck03
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem checked : (orbits.drop 96 |>.take 32).all checkOrbit=true := by decide +kernel
end Rule30CubicOrbitCheck03
