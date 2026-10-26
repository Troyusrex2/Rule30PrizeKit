module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck04
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row16 : (List.range 48).all (fun j => !(moment 16 (16+j)))=true := by decide +kernel
theorem row17 : (List.range 47).all (fun j => !(moment 17 (17+j)))=true := by decide +kernel
theorem row18 : (List.range 46).all (fun j => !(moment 18 (18+j)))=true := by decide +kernel
theorem row19 : (List.range 45).all (fun j => !(moment 19 (19+j)))=true := by decide +kernel
end Rule30CubicMomentCheck04
