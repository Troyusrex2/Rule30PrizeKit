module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck03
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row12 : (List.range 52).all (fun j => !(moment 12 (12+j)))=true := by decide +kernel
theorem row13 : (List.range 51).all (fun j => !(moment 13 (13+j)))=true := by decide +kernel
theorem row14 : (List.range 50).all (fun j => !(moment 14 (14+j)))=true := by decide +kernel
theorem row15 : (List.range 49).all (fun j => !(moment 15 (15+j)))=true := by decide +kernel
end Rule30CubicMomentCheck03
