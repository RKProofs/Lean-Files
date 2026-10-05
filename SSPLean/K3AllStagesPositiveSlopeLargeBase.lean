import SSPLean.K3AllStagesPositiveSlope

/-! # Shared definitions for the large-ratio positive-slope chart

This base is separate from the expensive `B0` certificate so the independent coefficient
chains do not need to load its large proof term. -/

set_option autoImplicit false

namespace SSP.K3AllStages

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
  uniformCubicSampleB0 (fun w => uniformFaceAPositiveHighVWLargeEndpoint m s w t)

noncomputable def uniformFaceAPositiveHighVWLargeB1 (m s t : ℝ) : ℝ :=
  uniformCubicSampleB1 (fun w => uniformFaceAPositiveHighVWLargeEndpoint m s w t)

noncomputable def uniformFaceAPositiveHighVWLargeB2 (m s t : ℝ) : ℝ :=
  uniformCubicSampleB2 (fun w => uniformFaceAPositiveHighVWLargeEndpoint m s w t)

noncomputable def uniformFaceAPositiveHighVWLargeB3 (m s t : ℝ) : ℝ :=
  uniformCubicSampleB3 (fun w => uniformFaceAPositiveHighVWLargeEndpoint m s w t)

private theorem affine_cubic_bernstein
    (A0 A1 A2 A3 K0 K1 w : ℝ) :
    let f := fun z : ℝ =>
      A0 + A1 * (K0 + K1*z) + A2 * (K0 + K1*z)^2 + A3 * (K0 + K1*z)^3
    f w = cornerBern3 (uniformCubicSampleB0 f) (uniformCubicSampleB1 f)
      (uniformCubicSampleB2 f) (uniformCubicSampleB3 f) w := by
  dsimp
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3 cornerBern3
  ring

theorem uniformFaceAPositiveHighVWLarge_bernstein_w (m s w t : ℝ) :
    uniformFaceAPositiveHighVWLargeEndpoint m s w t =
      cornerBern3 (uniformFaceAPositiveHighVWLargeB0 m s t)
        (uniformFaceAPositiveHighVWLargeB1 m s t)
        (uniformFaceAPositiveHighVWLargeB2 m s t)
        (uniformFaceAPositiveHighVWLargeB3 m s t) w := by
  let n := m + 4
  let T := uniformFaceANonposT m s
  let L := uniformFaceACurrentM n T 1
  let K := fun z : ℝ => uniformFaceACurrentK n T (uniformFaceAPositiveQ m s (z*t))
  let K0 := K 0
  let K1 := K 1 - K0
  let A0 := t^3*n^3*L^3*uniformFaceACoreXC0 n T 1
  let A1 := t^2*n^2*L^2*uniformFaceACoreXC1 n T 1
  let A2 := t*n*L*uniformFaceACoreXC2 n T 1
  let A3 := uniformFaceACoreXC3 n T 1
  let f := fun z : ℝ => uniformFaceAPositiveHighVWLargeEndpoint m s z t
  let g := fun z : ℝ =>
    A0 + A1 * (K0 + K1*z) + A2 * (K0 + K1*z)^2 + A3 * (K0 + K1*z)^3
  have hK (z : ℝ) : K z = K0 + K1*z := by
    dsimp [K, K0, K1, n, T]
    unfold uniformFaceAPositiveQ uniformFaceACurrentK uniformReturnK
    ring
  have hfg : f = g := by
    funext z
    dsimp [f]
    unfold uniformFaceAPositiveHighVWLargeEndpoint
    dsimp only
    change A0 + t^2*n^2*L^2*(K z)*uniformFaceACoreXC1 n T 1
        + t*n*L*(K z)^2*uniformFaceACoreXC2 n T 1
        + (K z)^3*uniformFaceACoreXC3 n T 1 = g z
    rw [hK z]
    dsimp [g, A1, A2, A3]
    ring
  change f w = cornerBern3 (uniformCubicSampleB0 f) (uniformCubicSampleB1 f)
    (uniformCubicSampleB2 f) (uniformCubicSampleB3 f) w
  rw [hfg]
  exact affine_cubic_bernstein A0 A1 A2 A3 K0 K1 w

end SSP.K3AllStages
