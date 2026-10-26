module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck08
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row32 : (List.range 32).all (fun j => !(moment 32 (32+j)))=true := by decide +kernel
theorem row33 : (List.range 31).all (fun j => !(moment 33 (33+j)))=true := by decide +kernel
theorem row34 : (List.range 30).all (fun j => !(moment 34 (34+j)))=true := by decide +kernel
theorem row35 : (List.range 29).all (fun j => !(moment 35 (35+j)))=true := by decide +kernel
end Rule30CubicMomentCheck08
