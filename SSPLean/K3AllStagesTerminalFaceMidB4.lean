import SSPLean.K3AllStagesTerminalFaceMidB3
set_option autoImplicit false
namespace SSP.K3AllStages
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeMidB4_nonneg_of_threshold
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t)
    (hthreshold : uniformLargeGradSlopeThreshold m t ≤
      uniformLargeGradSlopeCoeff m*x) :
    0 ≤ uniformLargeMidB4 m t x := by
  let u := uniformLargeGradSlopeCoeff m*x
    - uniformLargeGradSlopeThreshold m t
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hP := uniformLargeGradSlopeCoeff_pos m hm
  have hxid : x =
      (uniformLargeGradSlopeThreshold m t + u) /
        uniformLargeGradSlopeCoeff m := by
    dsimp [u]
    field_simp [hP.ne']
    ring
  rw [hxid]
  let A := 3*m^4 + 57*m^3 + 401*m^2 + 1239*m + 1420
  let B := -6*m^5 - 94*m^4 - 430*m^3 + 6*m^2 + 4212*m + 7160
  let C := 24*m^6 + 582*m^5 + 5731*m^4 + 29493*m^3
    + 84265*m^2 + 127749*m + 80908
  have hA : 0 < A := by dsimp [A]; positivity
  have hdisc : 0 ≤ 4*A*C-B^2 := by
    have hid : 4*A*C-B^2 =
        4*(m+3)^2*(m+5)*
          (63*m^7 + 2139*m^6 + 30506*m^5 + 236250*m^4
            + 1069159*m^3 + 2813659*m^2 + 3957920*m + 2268288) := by
      dsimp [A, B, C]
      ring
    rw [hid]
    positivity
  have hquad : 0 ≤ A*t^2+B*t+C := by
    have hid : 4*A*(A*t^2+B*t+C) =
        (2*A*t+B)^2+(4*A*C-B^2) := by ring
    have hscaled : 0 ≤ 4*A*(A*t^2+B*t+C) := by
      rw [hid]
      positivity
    exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*A)).mp hscaled
  let S := A*t^2+B*t+C
  let remainder :=
    (uniformLargeGradSlopeCoeff m)^4 *
        uniformLargeMidB4 m t
          ((uniformLargeGradSlopeThreshold m t + u) /
            uniformLargeGradSlopeCoeff m)
      - u^3*(m+4)^2*(m+6)*S/2
  have hrem : 0 ≤ remainder := by
    dsimp [remainder, S, A, B, C]
    unfold uniformLargeMidB4
    unfold uniformLargeGradSlopeCoeff uniformLargeGradSlopeThreshold
    simp only [TerminalMidSample_eq _ 1 _ _ (by norm_num)]
    unfold TerminalMidPolynomial TerminalMidX0 TerminalMidX1 TerminalMidX2
    field_simp [hP.ne']
    ring_nf
    positivity
  have hscaled : 0 ≤
      (uniformLargeGradSlopeCoeff m)^4 *
        uniformLargeMidB4 m t
          ((uniformLargeGradSlopeThreshold m t + u) /
            uniformLargeGradSlopeCoeff m) := by
    have hblock : 0 ≤ u^3*(m+4)^2*(m+6)*S/2 := by
      dsimp [S]
      positivity
    dsimp [remainder] at hrem
    linarith
  exact (mul_nonneg_iff_of_pos_left (pow_pos hP 4)).mp hscaled

end SSP.K3AllStages
