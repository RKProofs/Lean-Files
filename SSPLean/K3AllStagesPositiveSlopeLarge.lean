import SSPLean.K3AllStagesPositiveSlope

/-!
# The large-ratio positive-slope chart for the uniform `k = 3` induction

This file handles the high-`z` chart `v = w*t`, `1/2 ≤ t ≤ 1` separately
so that its moderately large coefficient certificate is serialized after the
main positive-slope reductions.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

/-- The denominator-free `q = 1` endpoint at the projective point
`X = K(q)/(t*n*M(1))`. -/
noncomputable def uniformFaceAPositiveHighVWLargeEndpoint
    (m s w t : ℝ) : ℝ :=
  let n := m + 4
  let T := uniformFaceANonposT m s
  let L := uniformFaceACurrentM n T 1
  let q := uniformFaceAPositiveQ m s (w*t)
  let K := uniformFaceACurrentK n T q
  t^3*n^3*L^3*uniformFaceACoreXC0 n T 1
    + t^2*n^2*L^2*K*uniformFaceACoreXC1 n T 1
    + t*n*L*K^2*uniformFaceACoreXC2 n T 1
    + K^3*uniformFaceACoreXC3 n T 1

noncomputable def uniformFaceAPositiveHighVWLargeB0 (m s t : ℝ) : ℝ :=
  uniformCubicSampleB0
    (fun w => uniformFaceAPositiveHighVWLargeEndpoint m s w t)

noncomputable def uniformFaceAPositiveHighVWLargeB1 (m s t : ℝ) : ℝ :=
  uniformCubicSampleB1
    (fun w => uniformFaceAPositiveHighVWLargeEndpoint m s w t)

noncomputable def uniformFaceAPositiveHighVWLargeB2 (m s t : ℝ) : ℝ :=
  uniformCubicSampleB2
    (fun w => uniformFaceAPositiveHighVWLargeEndpoint m s w t)

noncomputable def uniformFaceAPositiveHighVWLargeB3 (m s t : ℝ) : ℝ :=
  uniformCubicSampleB3
    (fun w => uniformFaceAPositiveHighVWLargeEndpoint m s w t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- Cubic Bernstein expansion in the original face coordinate `w`. -/
theorem uniformFaceAPositiveHighVWLarge_bernstein_w (m s w t : ℝ) :
    uniformFaceAPositiveHighVWLargeEndpoint m s w t =
      cornerBern3 (uniformFaceAPositiveHighVWLargeB0 m s t)
        (uniformFaceAPositiveHighVWLargeB1 m s t)
        (uniformFaceAPositiveHighVWLargeB2 m s t)
        (uniformFaceAPositiveHighVWLargeB3 m s t) w := by
  unfold uniformFaceAPositiveHighVWLargeB0
  unfold uniformFaceAPositiveHighVWLargeB1
  unfold uniformFaceAPositiveHighVWLargeB2
  unfold uniformFaceAPositiveHighVWLargeB3
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceAPositiveHighVWLargeEndpoint
  unfold uniformFaceAPositiveQ cornerBern3
  unfold uniformFaceACurrentK uniformReturnK
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
/-- The left `w`-Bernstein coefficient is nonnegative.  The three remaining
coefficients use the same translated variables but need pre-expanded
certificates to avoid excessive elaborator memory. -/
theorem uniformFaceAPositiveHighVWLargeB0_nonneg
    (m s t : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) (ht : 1/2 ≤ t) :
    0 ≤ uniformFaceAPositiveHighVWLargeB0 m s t := by
  let r := 2*t-1
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have htId : t = (1+r)/2 := by dsimp [r]; ring
  rw [htId]
  simp only [uniformFaceAPositiveHighVWLargeB0, uniformCubicSampleB0]
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
