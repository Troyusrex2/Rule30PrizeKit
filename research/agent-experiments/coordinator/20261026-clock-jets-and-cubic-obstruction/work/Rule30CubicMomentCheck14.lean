module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck14
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row56 : (List.range 8).all (fun j => !(moment 56 (56+j)))=true := by decide +kernel
theorem row57 : (List.range 7).all (fun j => !(moment 57 (57+j)))=true := by decide +kernel
theorem row58 : (List.range 6).all (fun j => !(moment 58 (58+j)))=true := by decide +kernel
theorem row59 : (List.range 5).all (fun j => !(moment 59 (59+j)))=true := by decide +kernel
end Rule30CubicMomentCheck14
