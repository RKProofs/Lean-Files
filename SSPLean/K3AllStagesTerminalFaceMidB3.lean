import SSPLean.K3AllStagesTerminalFaceMidB2
set_option autoImplicit false
namespace SSP.K3AllStages
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeMidB3_nonneg_of_threshold
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t)
    (hthreshold : uniformLargeGradSlopeThreshold m t ≤
      uniformLargeGradSlopeCoeff m*x) :
    0 ≤ uniformLargeMidB3 m t x := by
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
  have hscaled : 0 ≤
      (uniformLargeGradSlopeCoeff m)^4 *
        uniformLargeMidB3 m t
          ((uniformLargeGradSlopeThreshold m t + u) /
            uniformLargeGradSlopeCoeff m) := by
    unfold uniformLargeMidB3
    unfold uniformLargeGradSlopeCoeff uniformLargeGradSlopeThreshold
    simp only [TerminalMidSample_eq _ 1 _ _ (by norm_num),
      TerminalMidSample_eq _ 2 _ _ (by norm_num),
      TerminalMidSample_eq _ 3 _ _ (by norm_num)]
    unfold TerminalMidPolynomial TerminalMidX0 TerminalMidX1 TerminalMidX2
    field_simp [hP.ne']
    ring_nf
    positivity
  exact (mul_nonneg_iff_of_pos_left (pow_pos hP 4)).mp hscaled

end SSP.K3AllStages
