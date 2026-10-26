module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck12
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row48 : (List.range 16).all (fun j => !(moment 48 (48+j)))=true := by decide +kernel
theorem row49 : (List.range 15).all (fun j => !(moment 49 (49+j)))=true := by decide +kernel
theorem row50 : (List.range 14).all (fun j => !(moment 50 (50+j)))=true := by decide +kernel
theorem row51 : (List.range 13).all (fun j => !(moment 51 (51+j)))=true := by decide +kernel
end Rule30CubicMomentCheck12
