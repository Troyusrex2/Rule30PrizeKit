module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck00
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row0 : (List.range 64).all (fun j => !(moment 0 (0+j)))=true := by decide +kernel
theorem row1 : (List.range 63).all (fun j => !(moment 1 (1+j)))=true := by decide +kernel
theorem row2 : (List.range 62).all (fun j => !(moment 2 (2+j)))=true := by decide +kernel
theorem row3 : (List.range 61).all (fun j => !(moment 3 (3+j)))=true := by decide +kernel
end Rule30CubicMomentCheck00
