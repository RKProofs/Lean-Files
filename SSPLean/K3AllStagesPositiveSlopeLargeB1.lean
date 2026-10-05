import SSPLean.K3AllStagesPositiveSlopeLargeBase

/-!
# First middle coefficient of the large-ratio positive-slope chart

The coefficient is cubic after translating `t = (1+r)/2`.  Its four
Bernstein coefficients are kept as separate declarations so Lean can release
each expanded normal form before checking the next one.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

noncomputable def uniformFaceAPositiveHighVWLargeB1R
    (m s r : ℝ) : ℝ :=
  uniformFaceAPositiveHighVWLargeB1 m s ((1+r)/2)

noncomputable def uniformFaceAPositiveHighVWLargeB1T0 (m s : ℝ) : ℝ :=
  uniformCubicSampleB0 (uniformFaceAPositiveHighVWLargeB1R m s)

noncomputable def uniformFaceAPositiveHighVWLargeB1T1 (m s : ℝ) : ℝ :=
  uniformCubicSampleB1 (uniformFaceAPositiveHighVWLargeB1R m s)

noncomputable def uniformFaceAPositiveHighVWLargeB1T2 (m s : ℝ) : ℝ :=
  uniformCubicSampleB2 (uniformFaceAPositiveHighVWLargeB1R m s)

noncomputable def uniformFaceAPositiveHighVWLargeB1T3 (m s : ℝ) : ℝ :=
  uniformCubicSampleB3 (uniformFaceAPositiveHighVWLargeB1R m s)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem uniformFaceAPositiveHighVWLargeB1_bernstein_r (m s r : ℝ) :
    uniformFaceAPositiveHighVWLargeB1R m s r =
      cornerBern3 (uniformFaceAPositiveHighVWLargeB1T0 m s)
        (uniformFaceAPositiveHighVWLargeB1T1 m s)
        (uniformFaceAPositiveHighVWLargeB1T2 m s)
        (uniformFaceAPositiveHighVWLargeB1T3 m s) r := by
  unfold uniformFaceAPositiveHighVWLargeB1T0
  unfold uniformFaceAPositiveHighVWLargeB1T1
  unfold uniformFaceAPositiveHighVWLargeB1T2
  unfold uniformFaceAPositiveHighVWLargeB1T3
  unfold uniformFaceAPositiveHighVWLargeB1R
  unfold uniformFaceAPositiveHighVWLargeB1
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceAPositiveHighVWLargeEndpoint
  unfold uniformFaceAPositiveQ cornerBern3
  unfold uniformFaceACurrentK uniformReturnK
  ring

end SSP.K3AllStages
