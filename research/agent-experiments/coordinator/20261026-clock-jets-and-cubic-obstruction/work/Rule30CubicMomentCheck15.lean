module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck15
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row60 : (List.range 4).all (fun j => !(moment 60 (60+j)))=true := by decide +kernel
theorem row61 : (List.range 3).all (fun j => !(moment 61 (61+j)))=true := by decide +kernel
theorem row62 : (List.range 2).all (fun j => !(moment 62 (62+j)))=true := by decide +kernel
theorem row63 : (List.range 1).all (fun j => !(moment 63 (63+j)))=true := by decide +kernel
end Rule30CubicMomentCheck15
