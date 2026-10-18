import SSPLean.K3AllStagesMiddleLowBase
set_option autoImplicit false
namespace SSP.K3AllStages
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def MiddleLowB2Positive1 (m s : ℝ) : ℝ :=
  (m + 3)*(m + 7)^2*(m + 8)^2*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(24*m + 1140) + 26034) + 391338) + 4411782) + 39461742) + 286044186) + 1695073098) + 8213318634) + 32050343430) + 97324559100) + 218268511380) + 335657326896) + 313054306704) + s^4*(m*(m*(m*(m*(m*(m*(m*(8*m + 314) + 5477) + 55565) + 358754) + 1507340) + 4012776) + 6163776) + 4164480) + s^3*(m*(m*(m*(m*(m*(m*(m*(m*(m*(40*m + 2116) + 50102) + 699458) + 6376400) + 39654002) + 170295418) + 498368872) + 950401320) + 1065516192) + 532776960) + s^2*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(70*m + 4546) + 135586) + 2435878) + 29214122) + 245754338) + 1485158866) + 6495816274) + 20420166028) + 45044962780) + 66287258040) + 58537939104) + 23509744128) + s*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(44*m + 3284) + 115932) + 2530404) + 37748952) + 404370524) + 3195202980) + 18888518996) + 83947134500) + 279493878328) + 687831612656) + 1217279980064) + 1470308938920) + 1089761580864) + 375573727296) + 132726335616)/9

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem MiddleLowB2Positive1_eq (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformCubicSampleB1 (fun v => uniformFaceANonposMiddleLowB2 m s v) =
      MiddleLowB2Positive1 m s := by
  unfold uniformCubicSampleB1 uniformFaceANonposMiddleLowB2 uniformFaceANonposMiddleLow
  simp only [uniformCubicSampleB2, NonposCompactPolynomial_eq m s _ _ hm hs]
  unfold NonposCompactPolynomial MiddleLowB2Positive1
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem MiddleLowB2Positive1_nonneg (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ MiddleLowB2Positive1 m s := by
  unfold MiddleLowB2Positive1
  positivity
end SSP.K3AllStages
