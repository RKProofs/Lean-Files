import SSPLean.K3AllStagesPositiveSlopeLargeCubic

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
  have hc := (uniformFaceAPositiveHighVWLargeB1_isCubic m s).comp_affine (1/2) (1/2)
  have hid : (fun r => uniformFaceAPositiveHighVWLargeB1 m s (1/2+1/2*r)) =
      uniformFaceAPositiveHighVWLargeB1R m s := by
    funext r
    congr 1
    ring
  rw [hid] at hc
  simpa only [uniformFaceAPositiveHighVWLargeB1T0,
    uniformFaceAPositiveHighVWLargeB1T1,uniformFaceAPositiveHighVWLargeB1T2,
    uniformFaceAPositiveHighVWLargeB1T3,uniformCubicSampleB0,uniformCubicSampleB1,
    uniformCubicSampleB2,uniformCubicSampleB3,cornerBern3] using hc.interpolate r

end SSP.K3AllStages
