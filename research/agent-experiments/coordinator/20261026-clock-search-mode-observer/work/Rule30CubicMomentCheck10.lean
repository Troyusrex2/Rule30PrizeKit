module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck10
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row40 : (List.range 24).all (fun j => !(moment 40 (40+j)))=true := by decide +kernel
theorem row41 : (List.range 23).all (fun j => !(moment 41 (41+j)))=true := by decide +kernel
theorem row42 : (List.range 22).all (fun j => !(moment 42 (42+j)))=true := by decide +kernel
theorem row43 : (List.range 21).all (fun j => !(moment 43 (43+j)))=true := by decide +kernel
end Rule30CubicMomentCheck10
