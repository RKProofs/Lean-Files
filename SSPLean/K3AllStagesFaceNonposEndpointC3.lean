import SSPLean.K3AllStagesFaceNonposEndpointBase
set_option autoImplicit false
namespace SSP.K3AllStages
open SSP.K3S4Renewal SSP.K3S4KKT
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
noncomputable def EndpointFactoredPositive3 (m z : ℝ) : ℝ :=
  1*(m + z + 4)*(m + 3)*(m + 6)*(m + 7)*(m*(m*(m*(m*(m*(m*(m + 34) + 485) + 3767) + 17220) + 46359) + 68094) + z^3*(m*(m*(m*(m + 21) + 157) + 495) + 556) + z^2*(m*(m*(m*(m*(3*m + 76) + 742) + 3493) + 7938) + 6984) + z*(m*(m*(m*(m*(m*(3*m + 89) + 1070) + 6680) + 22857) + 40671) + 29430) + 42120)*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(7*m + 345) + 7642) + 100412) + 869547) + 5211089) + 22054812) + 65929770) + 136451304) + 186257232) + 150959376) + z^5*(m*(m*(m*(m*(m*(m + 36) + 522) + 3882) + 15596) + 32184) + 26784) + z^4*(m*(m*(m*(m*(m*(m*(3*m + 129) + 2266) + 21194) + 114508) + 359024) + 607776) + 430272) + z^3*(m*(m*(m*(m*(m*(m*(m*(10*m + 428) + 7824) + 79894) + 499024) + 1954640) + 4694756) + 6330504) + 3674016) + z^2*(m*(m*(m*(m*(m*(m*(m*(m*(22*m + 958) + 18252) + 199746) + 1384262) + 6302396) + 18860052) + 35789256) + 39098592) + 18745344) + z*(m*(m*(m*(m*(m*(m*(m*(m*(m*(21*m + 968) + 19814) + 237160) + 1838339) + 9644162) + 34685730) + 84472830) + 133364448) + 123304032) + 50718960) + 55054080)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem EndpointFactoredPositive3_eq (m z : ℝ) :
    EndpointReducedC3 (m+4) (m+3+z) (uniformFaceALargeM m z) (uniformFaceALargeK m z) =
      EndpointFactoredPositive3 m z := by
  simp only [EndpointReducedC3, EndpointReducedX0, EndpointReducedX1, EndpointReducedX2, EndpointReducedX3, uniformFaceALargeM, uniformFaceALargeK, uniformReturnM, uniformReturnK, EndpointFactoredPositive3]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem EndpointFactoredPositive3_nonneg (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 ≤ EndpointFactoredPositive3 m z := by
  unfold EndpointFactoredPositive3
  positivity

end SSP.K3AllStages
