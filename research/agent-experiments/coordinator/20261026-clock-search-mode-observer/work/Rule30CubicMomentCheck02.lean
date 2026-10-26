module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck02
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row8 : (List.range 56).all (fun j => !(moment 8 (8+j)))=true := by decide +kernel
theorem row9 : (List.range 55).all (fun j => !(moment 9 (9+j)))=true := by decide +kernel
theorem row10 : (List.range 54).all (fun j => !(moment 10 (10+j)))=true := by decide +kernel
theorem row11 : (List.range 53).all (fun j => !(moment 11 (11+j)))=true := by decide +kernel
end Rule30CubicMomentCheck02
