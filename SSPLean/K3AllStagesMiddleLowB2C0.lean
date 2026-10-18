import SSPLean.K3AllStagesMiddleLowBase
set_option autoImplicit false
namespace SSP.K3AllStages
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def MiddleLowB2Positive0 (m _s : ℝ) : ℝ :=
  2*(m + 3)^3*(m + 6)*(m + 7)^3*(m + 8)^3*(m*(m*(m*(m*(m*(m*(m*(m*(4*m + 82) + 1001) + 9550) + 67964) + 370822) + 1603105) + 4981278) + 9198486) + 7315164)/3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem MiddleLowB2Positive0_eq (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformCubicSampleB0 (fun v => uniformFaceANonposMiddleLowB2 m s v) =
      MiddleLowB2Positive0 m s := by
  unfold uniformCubicSampleB0 uniformFaceANonposMiddleLowB2 uniformFaceANonposMiddleLow
  simp only [uniformCubicSampleB2, NonposCompactPolynomial_eq m s _ _ hm hs]
  unfold NonposCompactPolynomial MiddleLowB2Positive0
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem MiddleLowB2Positive0_nonneg (m s : ℝ) (hm : 0 ≤ m) (_hs : 0 ≤ s) :
    0 ≤ MiddleLowB2Positive0 m s := by
  unfold MiddleLowB2Positive0
  positivity
end SSP.K3AllStages
