module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck13
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row52 : (List.range 12).all (fun j => !(moment 52 (52+j)))=true := by decide +kernel
theorem row53 : (List.range 11).all (fun j => !(moment 53 (53+j)))=true := by decide +kernel
theorem row54 : (List.range 10).all (fun j => !(moment 54 (54+j)))=true := by decide +kernel
theorem row55 : (List.range 9).all (fun j => !(moment 55 (55+j)))=true := by decide +kernel
end Rule30CubicMomentCheck13
