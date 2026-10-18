import SSPLean.K3AllStagesFaceNonposEndpointBase
set_option autoImplicit false
namespace SSP.K3AllStages
open SSP.K3S4Renewal SSP.K3S4KKT
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
noncomputable def EndpointFactoredPositive0 (m z : ℝ) : ℝ :=
  1*z^2*(m + 6)*(m*(m*(m*(m*(m*(m*(m + 33) + 458) + 3462) + 15381) + 40149) + 57024) + z^4*(m*(m*(m + 13) + 56) + 80) + z^3*(m*(m*(m*(4*m + 72) + 476) + 1368) + 1440) + z^2*(m*(m*(m*(m*(6*m + 138) + 1242) + 5466) + 11772) + 9936) + z*(m*(m*(m*(m*(m*(4*m + 112) + 1280) + 7640) + 25116) + 43128) + 30240) + 34020)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem EndpointFactoredPositive0_eq (m z : ℝ) :
    EndpointReducedC0 (m+4) (m+3+z) (uniformFaceALargeM m z) (uniformFaceALargeK m z) =
      EndpointFactoredPositive0 m z := by
  simp only [EndpointReducedC0, EndpointReducedX0, EndpointFactoredPositive0]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem EndpointFactoredPositive0_nonneg (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 ≤ EndpointFactoredPositive0 m z := by
  unfold EndpointFactoredPositive0
  positivity

end SSP.K3AllStages
