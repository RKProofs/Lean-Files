import SSPLean.K3AllStagesFaceNonposEndpointBase
set_option autoImplicit false
namespace SSP.K3AllStages
open SSP.K3S4Renewal SSP.K3S4KKT
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
noncomputable def EndpointFactoredPositive1 (m z : ℝ) : ℝ :=
  (m + 6)*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(2*m + 105) + 2528) + 36960) + 366128) + 2595246) + 13543812) + 52693524) + 152852670) + 326544129) + 499437900) + 517942836) + 326475360) + z^7*(m*(m*(m*(m*(m*(3*m + 93) + 1161) + 7503) + 26556) + 48912) + 36672) + z^6*(m*(m*(m*(m*(m*(m*(15*m + 533) + 7897) + 63399) + 298348) + 823888) + 1237264) + 780096) + z^5*(m*(m*(m*(m*(m*(m*(m*(32*m + 1254) + 21105) + 199381) + 1156839) + 4222317) + 9468972) + 11932164) + 6470928) + z^4*(m*(m*(m*(m*(m*(m*(m*(m*(40*m + 1651) + 30060) + 316714) + 2126792) + 9433831) + 27624876) + 51469236) + 55343520) + 26161056) + z^3*(m*(m*(m*(m*(m*(m*(m*(m*(m*(35*m + 1469) + 27633) + 307003) + 2232257) + 11104467) + 38281895) + 90308613) + 139484268) + 127316016) + 52121880) + z^2*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(23*m + 999) + 19515) + 226371) + 1733213) + 9202205) + 34596057) + 92180385) + 170765928) + 209714184) + 153852048) + 51146640) + z*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(10*m + 472) + 10101) + 129557) + 1108829) + 6668601) + 28884051) + 90734283) + 205019181) + 324679347) + 341676468) + 214194780) + 60361200) + 94478400)/3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem EndpointFactoredPositive1_eq (m z : ℝ) :
    EndpointReducedC1 (m+4) (m+3+z) (uniformFaceALargeM m z) (uniformFaceALargeK m z) =
      EndpointFactoredPositive1 m z := by
  simp only [EndpointReducedC1, EndpointReducedX0, EndpointReducedX1, uniformFaceALargeM, uniformFaceALargeK, uniformReturnM, uniformReturnK, EndpointFactoredPositive1]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem EndpointFactoredPositive1_nonneg (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 ≤ EndpointFactoredPositive1 m z := by
  unfold EndpointFactoredPositive1
  positivity

end SSP.K3AllStages
