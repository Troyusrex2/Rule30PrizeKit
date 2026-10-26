module
public import Rule30CubicCertificateData
@[expose] public section
namespace Rule30CubicMomentCheck06
open Rule30CubicCertificateData
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
theorem row24 : (List.range 40).all (fun j => !(moment 24 (24+j)))=true := by decide +kernel
theorem row25 : (List.range 39).all (fun j => !(moment 25 (25+j)))=true := by decide +kernel
theorem row26 : (List.range 38).all (fun j => !(moment 26 (26+j)))=true := by decide +kernel
theorem row27 : (List.range 37).all (fun j => !(moment 27 (27+j)))=true := by decide +kernel
end Rule30CubicMomentCheck06
