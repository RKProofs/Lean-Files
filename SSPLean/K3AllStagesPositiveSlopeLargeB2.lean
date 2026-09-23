import SSPLean.K3AllStagesPositiveSlopeLarge

/-!
# Second middle coefficient of the large-ratio positive-slope chart

The coefficient is cubic after translating `t = (1+r)/2`.  Its four
Bernstein coefficients are kept as separate declarations so Lean can release
each expanded normal form before checking the next one.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

noncomputable def uniformFaceAPositiveHighVWLargeB2R
    (m s r : ℝ) : ℝ :=
  uniformFaceAPositiveHighVWLargeB2 m s ((1+r)/2)

noncomputable def uniformFaceAPositiveHighVWLargeB2T0 (m s : ℝ) : ℝ :=
  uniformCubicSampleB0 (uniformFaceAPositiveHighVWLargeB2R m s)

noncomputable def uniformFaceAPositiveHighVWLargeB2T1 (m s : ℝ) : ℝ :=
  uniformCubicSampleB1 (uniformFaceAPositiveHighVWLargeB2R m s)

noncomputable def uniformFaceAPositiveHighVWLargeB2T2 (m s : ℝ) : ℝ :=
  uniformCubicSampleB2 (uniformFaceAPositiveHighVWLargeB2R m s)

noncomputable def uniformFaceAPositiveHighVWLargeB2T3 (m s : ℝ) : ℝ :=
  uniformCubicSampleB3 (uniformFaceAPositiveHighVWLargeB2R m s)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem uniformFaceAPositiveHighVWLargeB2_bernstein_r (m s r : ℝ) :
    uniformFaceAPositiveHighVWLargeB2R m s r =
      cornerBern3 (uniformFaceAPositiveHighVWLargeB2T0 m s)
        (uniformFaceAPositiveHighVWLargeB2T1 m s)
        (uniformFaceAPositiveHighVWLargeB2T2 m s)
        (uniformFaceAPositiveHighVWLargeB2T3 m s) r := by
  unfold uniformFaceAPositiveHighVWLargeB2T0
  unfold uniformFaceAPositiveHighVWLargeB2T1
  unfold uniformFaceAPositiveHighVWLargeB2T2
  unfold uniformFaceAPositiveHighVWLargeB2T3
  unfold uniformFaceAPositiveHighVWLargeB2R
  unfold uniformFaceAPositiveHighVWLargeB2
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceAPositiveHighVWLargeEndpoint
  unfold uniformFaceAPositiveQ cornerBern3
  unfold uniformFaceACurrentK uniformReturnK
  ring

end SSP.K3AllStages
