import SSPLean.K3AllStagesMiddleCubic

/-! # Shared definitions for the upper-middle return-face chart -/

set_option autoImplicit false
namespace SSP.K3AllStages

noncomputable def uniformFaceANonposMiddleHigh (m s v w : ℝ) : ℝ :=
  uniformFaceANonposScaled m s v
    ((m^2 + 39) + w * (uniformFaceANonposP m / 8 - (m^2 + 39)))

noncomputable def uniformFaceANonposMiddleHighB0 (m s v : ℝ) : ℝ :=
  uniformCubicSampleB0 (fun w => uniformFaceANonposMiddleHigh m s v w)

noncomputable def uniformFaceANonposMiddleHighB1 (m s v : ℝ) : ℝ :=
  uniformCubicSampleB1 (fun w => uniformFaceANonposMiddleHigh m s v w)

noncomputable def uniformFaceANonposMiddleHighB2 (m s v : ℝ) : ℝ :=
  uniformCubicSampleB2 (fun w => uniformFaceANonposMiddleHigh m s v w)

noncomputable def uniformFaceANonposMiddleHighB3 (m s v : ℝ) : ℝ :=
  uniformCubicSampleB3 (fun w => uniformFaceANonposMiddleHigh m s v w)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem uniformFaceANonposMiddleHigh_bernstein_w (m s v w : ℝ) :
    uniformFaceANonposMiddleHigh m s v w =
      cornerBern3 (uniformFaceANonposMiddleHighB0 m s v)
        (uniformFaceANonposMiddleHighB1 m s v)
        (uniformFaceANonposMiddleHighB2 m s v)
        (uniformFaceANonposMiddleHighB3 m s v) w := by
  unfold uniformFaceANonposMiddleHighB0 uniformFaceANonposMiddleHighB1
  unfold uniformFaceANonposMiddleHighB2 uniformFaceANonposMiddleHighB3
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposMiddleHigh cornerBern3
  simp_rw [uniformFaceANonposScaled_power]
  ring

end SSP.K3AllStages
