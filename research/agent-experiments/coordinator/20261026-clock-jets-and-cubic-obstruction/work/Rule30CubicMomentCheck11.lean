module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck11
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row44 : (List.range 20).all (fun j => !(moment 44 (44+j)))=true := by decide +kernel
theorem row45 : (List.range 19).all (fun j => !(moment 45 (45+j)))=true := by decide +kernel
theorem row46 : (List.range 18).all (fun j => !(moment 46 (46+j)))=true := by decide +kernel
theorem row47 : (List.range 17).all (fun j => !(moment 47 (47+j)))=true := by decide +kernel
end Rule30CubicMomentCheck11
