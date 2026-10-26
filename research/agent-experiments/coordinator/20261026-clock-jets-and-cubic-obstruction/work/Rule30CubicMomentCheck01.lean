module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck01
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row4 : (List.range 60).all (fun j => !(moment 4 (4+j)))=true := by decide +kernel
theorem row5 : (List.range 59).all (fun j => !(moment 5 (5+j)))=true := by decide +kernel
theorem row6 : (List.range 58).all (fun j => !(moment 6 (6+j)))=true := by decide +kernel
theorem row7 : (List.range 57).all (fun j => !(moment 7 (7+j)))=true := by decide +kernel
end Rule30CubicMomentCheck01
