module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck09
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row36 : (List.range 28).all (fun j => !(moment 36 (36+j)))=true := by decide +kernel
theorem row37 : (List.range 27).all (fun j => !(moment 37 (37+j)))=true := by decide +kernel
theorem row38 : (List.range 26).all (fun j => !(moment 38 (38+j)))=true := by decide +kernel
theorem row39 : (List.range 25).all (fun j => !(moment 39 (39+j)))=true := by decide +kernel
end Rule30CubicMomentCheck09
