import SSPLean.K3AllStagesMiddleCubic

/-! # Shared definitions for the lower-middle return-face chart -/

set_option autoImplicit false

namespace SSP.K3AllStages

noncomputable def uniformFaceANonposMiddleLow
    (m s v w : ℝ) : ℝ :=
  uniformFaceANonposScaled m s v (1 + w * (m^2 + 38))

noncomputable def uniformFaceANonposMiddleLowB0 (m s v : ℝ) : ℝ :=
  uniformCubicSampleB0 (fun w => uniformFaceANonposMiddleLow m s v w)

noncomputable def uniformFaceANonposMiddleLowB1 (m s v : ℝ) : ℝ :=
  uniformCubicSampleB1 (fun w => uniformFaceANonposMiddleLow m s v w)

noncomputable def uniformFaceANonposMiddleLowB2 (m s v : ℝ) : ℝ :=
  uniformCubicSampleB2 (fun w => uniformFaceANonposMiddleLow m s v w)

noncomputable def uniformFaceANonposMiddleLowB3 (m s v : ℝ) : ℝ :=
  uniformCubicSampleB3 (fun w => uniformFaceANonposMiddleLow m s v w)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem uniformFaceANonposMiddleLow_bernstein_w (m s v w : ℝ) :
    uniformFaceANonposMiddleLow m s v w =
      cornerBern3 (uniformFaceANonposMiddleLowB0 m s v)
        (uniformFaceANonposMiddleLowB1 m s v)
        (uniformFaceANonposMiddleLowB2 m s v)
        (uniformFaceANonposMiddleLowB3 m s v) w := by
  unfold uniformFaceANonposMiddleLowB0 uniformFaceANonposMiddleLowB1
  unfold uniformFaceANonposMiddleLowB2 uniformFaceANonposMiddleLowB3
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposMiddleLow cornerBern3
  simp_rw [uniformFaceANonposScaled_power]
  ring

end SSP.K3AllStages
