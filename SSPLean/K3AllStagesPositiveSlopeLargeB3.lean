import SSPLean.K3AllStagesPositiveSlopeLargeB2Complete

/-!
# Right endpoint coefficient of the large-ratio positive-slope chart

At `w = 1` the final cubic Bernstein coefficient is again nonnegative after
translating the large-ratio interval by `t = (1+r)/2`.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem uniformFaceAPositiveHighVWLargeB3_nonneg
    (m s t : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) (ht : 1/2 ≤ t) :
    0 ≤ uniformFaceAPositiveHighVWLargeB3 m s t := by
  let r := 2*t-1
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have htId : t = (1+r)/2 := by dsimp [r]; ring
  rw [htId]
  simp only [uniformFaceAPositiveHighVWLargeB3, uniformCubicSampleB3]
  unfold uniformFaceAPositiveHighVWLargeEndpoint
  unfold uniformFaceAPositiveQ uniformFaceAPositiveQ0
  unfold uniformFaceAPositiveD uniformFaceANonposT
  unfold uniformFaceANonposZ uniformFaceANonposP
  unfold uniformFaceACurrentM uniformFaceACurrentK
  unfold uniformFaceACoreXC0 uniformFaceACoreXC1
  unfold uniformFaceACoreXC2 uniformFaceACoreXC3
  unfold uniformReturnM uniformReturnK uniformFaceACore
  field_simp
  ring_nf
  positivity

end SSP.K3AllStages
