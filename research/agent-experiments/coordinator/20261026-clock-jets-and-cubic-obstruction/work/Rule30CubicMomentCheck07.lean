module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck07
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row28 : (List.range 36).all (fun j => !(moment 28 (28+j)))=true := by decide +kernel
theorem row29 : (List.range 35).all (fun j => !(moment 29 (29+j)))=true := by decide +kernel
theorem row30 : (List.range 34).all (fun j => !(moment 30 (30+j)))=true := by decide +kernel
theorem row31 : (List.range 33).all (fun j => !(moment 31 (31+j)))=true := by decide +kernel
end Rule30CubicMomentCheck07
