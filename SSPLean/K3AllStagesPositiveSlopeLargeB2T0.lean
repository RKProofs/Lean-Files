import SSPLean.K3AllStagesPositiveSlopeLargeB2

set_option autoImplicit false
namespace SSP.K3AllStages

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem uniformFaceAPositiveHighVWLargeB2T0_nonneg
    (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ uniformFaceAPositiveHighVWLargeB2T0 m s := by
  unfold uniformFaceAPositiveHighVWLargeB2T0 uniformCubicSampleB0
  unfold uniformFaceAPositiveHighVWLargeB2R
  unfold uniformFaceAPositiveHighVWLargeB2 uniformCubicSampleB2
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
