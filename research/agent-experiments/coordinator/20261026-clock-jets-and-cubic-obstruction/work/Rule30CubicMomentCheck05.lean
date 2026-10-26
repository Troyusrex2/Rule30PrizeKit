module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck05
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row20 : (List.range 44).all (fun j => !(moment 20 (20+j)))=true := by decide +kernel
theorem row21 : (List.range 43).all (fun j => !(moment 21 (21+j)))=true := by decide +kernel
theorem row22 : (List.range 42).all (fun j => !(moment 22 (22+j)))=true := by decide +kernel
theorem row23 : (List.range 41).all (fun j => !(moment 23 (23+j)))=true := by decide +kernel
end Rule30CubicMomentCheck05
