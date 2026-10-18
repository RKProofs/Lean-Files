import SSPLean.K3AllStagesFaceNonposEndpointBase
set_option autoImplicit false
namespace SSP.K3AllStages
open SSP.K3S4Renewal SSP.K3S4KKT
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
noncomputable def EndpointFactoredPositive2 (m z : ℝ) : ℝ :=
  (m + 6)*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(9*m + 671) + 23389) + 506243) + 7620730) + 84673766) + 719097514) + 4768093926) + 24991766061) + 104147253963) + 345087281961) + 904064990823) + 1849887884592) + 2894653352016) + 3345354067824) + 2691019554192) + 1345385013120) + z^8*(m*(m*(m*(m*(m*(m*(m*(m*(3*m + 147) + 3131) + 38039) + 290551) + 1447591) + 4707312) + 9641280) + 11294976) + 5771520) + z^7*(m*(m*(m*(m*(m*(m*(m*(m*(m*(18*m + 968) + 22934) + 315390) + 2789598) + 16592306) + 67255322) + 183572624) + 323135720) + 331479840) + 150589440) + z^6*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(54*m + 3092) + 79084) + 1193224) + 11805839) + 80463647) + 385657351) + 1300472981) + 3025007268) + 4624793812) + 4184561904) + 1698387840) + z^5*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(114*m + 6756) + 181240) + 2910854) + 31178950) + 234690624) + 1273205916) + 5016932222) + 14253656580) + 28481868072) + 38004075072) + 30410756640) + 11039089536) + z^4*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(180*m + 10990) + 306604) + 5176190) + 59010517) + 479829215) + 2863544462) + 12701782588) + 41884859921) + 101431598181) + 175374042588) + 205046978148) + 145335402144) + 47172396384) + z^3*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(198*m + 12592) + 368342) + 6569898) + 79838496) + 699379834) + 4555198472) + 22414165638) + 83746672090) + 236496173246) + 496996282386) + 753863790600) + 780408123120) + 493647081696) + 143985120480) + z^2*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(138*m + 9228) + 285488) + 5420832) + 70656507) + 669715433) + 4769279367) + 25987408905) + 109254769343) + 354446095239) + 880243486677) + 1643627907819) + 2234120043168) + 2087333227296) + 1198861856784) + 319159757520) + z*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(54*m + 3812) + 125180) + 2538386) + 35577100) + 365466888) + 2846558568) + 17149410980) + 80772151422) + 298429870356) + 862166484108) + 1927375380666) + 3268805926320) + 4066419655152) + 3499789755168) + 1862119925280) + 461495491200) + 314802028800)/3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem EndpointFactoredPositive2_eq (m z : ℝ) :
    EndpointReducedC2 (m+4) (m+3+z) (uniformFaceALargeM m z) (uniformFaceALargeK m z) =
      EndpointFactoredPositive2 m z := by
  simp only [EndpointReducedC2, EndpointReducedX0, EndpointReducedX1, EndpointReducedX2, uniformFaceALargeM, uniformFaceALargeK, uniformReturnM, uniformReturnK, EndpointFactoredPositive2]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem EndpointFactoredPositive2_nonneg (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 ≤ EndpointFactoredPositive2 m z := by
  unfold EndpointFactoredPositive2
  positivity

end SSP.K3AllStages
