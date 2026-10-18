import SSPLean.K3AllStagesTerminalFaceEnd
set_option autoImplicit false
namespace SSP.K3AllStages
/-! ### Completion of the final large-time middle certificate -/

noncomputable def uniformLargeGradMaxTime
    (m a x : ℝ) : ℝ :=
  uniformLargeGrad0Poly m a 8 x /
    (a * uniformLargeGrad0TimeCoeff m x)

noncomputable def uniformLargeMidTimeC0
    (m a x : ℝ) : ℝ :=
  uniformLargeMidSample m a 8 x

noncomputable def uniformLargeMidTimeC1
    (m a x : ℝ) : ℝ :=
  uniformLargeMidSample m a 8 x
    + uniformLargeGradMaxTime m a x / 4 *
      (uniformLargeMidSample m a 9 x - uniformLargeMidSample m a 7 x)

noncomputable def uniformLargeMidTimeC2
    (m a x : ℝ) : ℝ :=
  uniformLargeMidSample m a (8 + uniformLargeGradMaxTime m a x) x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem uniformLargeMidTime_endpoint_identity
    (m a x : ℝ) (ha : a ≠ 0)
    (hC : uniformLargeGrad0TimeCoeff m x ≠ 0) :
    2*a^2*uniformLargeGrad0TimeCoeff m x ^ 2 *
        uniformLargeMidTimeC2 m a x =
      uniformRemainingEndpointP m a x := by
  unfold uniformLargeMidTimeC2 uniformLargeGradMaxTime
  unfold uniformLargeGrad0Poly
  unfold uniformRemainingEndpointP
  unfold uniformLargeMidSample uniformFaceBCoreB1
  unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1
  field_simp [ha, hC]
  unfold uniformLargeGrad0TimeCoeff
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem uniformLargeMidTime_middle_identity
    (m a x : ℝ) (ha : a ≠ 0)
    (hC : uniformLargeGrad0TimeCoeff m x ≠ 0) :
    2*a*uniformLargeGrad0TimeCoeff m x *
        uniformLargeMidTimeC1 m a x =
      uniformRemainingTimeMidN m a x := by
  unfold uniformLargeMidTimeC1 uniformLargeGradMaxTime
  unfold uniformLargeGrad0Poly
  unfold uniformRemainingTimeMidN
  unfold uniformLargeMidSample uniformFaceBCoreB1
  unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1
  field_simp [ha, hC]
  unfold uniformLargeGrad0TimeCoeff
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem uniformLargeMidTime_det_identity
    (m a x : ℝ) (ha : a ≠ 0)
    (hC : uniformLargeGrad0TimeCoeff m x ≠ 0) :
    4*a^2*uniformLargeGrad0TimeCoeff m x ^ 2 *
        (uniformLargeMidTimeC0 m a x * uniformLargeMidTimeC2 m a x
          - uniformLargeMidTimeC1 m a x ^ 2) =
      uniformLargeGrad0Poly m a 8 x ^ 2 * (m+6) *
        uniformRemainingTimeDetJ m a x := by
  unfold uniformLargeMidTimeC0 uniformLargeMidTimeC1
  unfold uniformLargeMidTimeC2 uniformLargeGradMaxTime
  unfold uniformLargeGrad0Poly
  unfold uniformRemainingTimeDetJ
  unfold uniformLargeMidSample uniformFaceBCoreB1
  unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1
  field_simp [ha, hC]
  unfold uniformLargeGrad0TimeCoeff
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeMid_time_bernstein
    (m a x w : ℝ) (ha : a ≠ 0)
    (hC : uniformLargeGrad0TimeCoeff m x ≠ 0) :
    uniformLargeMidSample m a
        (8 + w * uniformLargeGradMaxTime m a x) x =
      cornerBern2 (uniformLargeMidTimeC0 m a x)
        (uniformLargeMidTimeC1 m a x) (uniformLargeMidTimeC2 m a x) w := by
  unfold uniformLargeMidTimeC0 uniformLargeMidTimeC1
  unfold uniformLargeMidTimeC2 uniformLargeGradMaxTime
  unfold uniformLargeMidSample uniformFaceBCoreB1
  unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1 cornerBern2
  field_simp [ha, hC]
  unfold uniformLargeGrad0TimeCoeff uniformLargeGrad0Poly
  ring

theorem uniformLargeMidTimeC2_nonneg
    (m a x : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (ha1 : a ≤ 1)
    (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidTimeC2 m a x := by
  have hP := uniformRemainingEndpointP_nonneg m a x hm ha.le ha1 hx
  have hid := uniformLargeMidTime_endpoint_identity m a x ha.ne'
    (ne_of_gt (uniformLargeGrad0TimeCoeff_pos m x hm hx))
  have hscale : 0 < 2*a^2*uniformLargeGrad0TimeCoeff m x ^ 2 := by
    have hC := uniformLargeGrad0TimeCoeff_pos m x hm hx
    positivity
  exact (mul_nonneg_iff_of_pos_left hscale).mp (by rw [hid]; exact hP)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeMidSample_nonneg_of_t_ge_eight_grad
    (m a t x : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (ha1 : a ≤ 1)
    (ht : 8 ≤ t) (hx : 0 ≤ x)
    (hgrad : 0 ≤ uniformLargeGrad0Poly m a t x) :
    0 ≤ uniformLargeMidSample m a t x := by
  let C := uniformLargeGrad0TimeCoeff m x
  let h := uniformLargeGrad0Poly m a 8 x
  have hC : 0 < C := by
    dsimp [C]
    exact uniformLargeGrad0TimeCoeff_pos m x hm hx
  have hbudget : a*C*(t-8) ≤ h := by
    dsimp [C, h]
    exact uniformLargeGrad0_time_budget_eight m a t x ht hgrad
  have hh : 0 ≤ h := by
    have hleft : 0 ≤ a*C*(t-8) := by positivity
    exact le_trans hleft hbudget
  by_cases hh0 : h = 0
  · have ht8 : t = 8 := by
      have : a*C*(t-8) ≤ 0 := by simpa [hh0] using hbudget
      nlinarith [mul_pos ha hC]
    subst t
    exact uniformLargeMidTimeB2_nonneg m a x hm ha hx
  · have hhpos : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
    let u := uniformLargeGradMaxTime m a x
    have hu : 0 < u := by
      dsimp [u, uniformLargeGradMaxTime, h]
      positivity
    have huid : a*C*u = h := by
      change a*C*(h/(a*C)) = h
      field_simp [mul_ne_zero ha.ne' hC.ne']
    let w := (t-8)/u
    have hw : 0 ≤ w := by dsimp [w]; positivity
    have htu : t-8 ≤ u := by nlinarith [mul_pos ha hC]
    have hw1 : w ≤ 1 := by
      dsimp [w]
      exact (div_le_one hu).mpr htu
    have htid : t = 8+w*u := by
      dsimp [w]
      field_simp [hu.ne']
      ring
    have hc0 : 0 ≤ uniformLargeMidTimeC0 m a x := by
      unfold uniformLargeMidTimeC0
      exact uniformLargeMidTimeB2_nonneg m a x hm ha hx
    have hc2 := uniformLargeMidTimeC2_nonneg m a x hm ha ha1 hx
    have hbern : 0 ≤ cornerBern2 (uniformLargeMidTimeC0 m a x)
        (uniformLargeMidTimeC1 m a x) (uniformLargeMidTimeC2 m a x) w := by
      by_cases hc1 : 0 ≤ uniformLargeMidTimeC1 m a x
      · exact cornerBern2_nonneg _ _ _ w hc0 hc1 hc2 hw (by linarith)
      · have hc1neg : uniformLargeMidTimeC1 m a x < 0 := lt_of_not_ge hc1
        have hmidN : uniformRemainingTimeMidN m a x ≤ 0 := by
          have hid := uniformLargeMidTime_middle_identity m a x ha.ne' hC.ne'
          nlinarith [mul_pos ha hC]
        have hJ := uniformRemainingTimeDetJ_nonneg_of_mid_nonpos
          m a x hm ha.le ha1 hx hmidN
        have hdetScaled : 0 ≤
            4*a^2*C^2 *
              (uniformLargeMidTimeC0 m a x * uniformLargeMidTimeC2 m a x
                - uniformLargeMidTimeC1 m a x ^ 2) := by
          dsimp [C]
          rw [uniformLargeMidTime_det_identity m a x ha.ne' hC.ne']
          positivity
        have hscale : 0 < 4*a^2*C^2 := by positivity
        have hdet : 0 ≤ uniformLargeMidTimeC0 m a x *
            uniformLargeMidTimeC2 m a x - uniformLargeMidTimeC1 m a x ^ 2 :=
          (mul_nonneg_iff_of_pos_left hscale).mp hdetScaled
        exact cornerBern2_nonneg_of_det _ _ _ w hc0 hc2 hdet
    rw [htid, uniformLargeMid_time_bernstein m a x w ha.ne' hC.ne']
    exact hbern

/-- The last large-time middle coefficient follows from the left-gradient
time budget. -/
theorem uniformFaceBCoreB1_nonneg_of_T_ge_nine_grad0
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT9 : 9 ≤ T) (hY : 0 ≤ Y)
    (hgrad : 0 ≤ uniformGradB0 n a T Y) :
    0 ≤ uniformFaceBCoreB1 n a T Y := by
  let m := n-4
  let t := T-1
  let x := a*Y
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have ht : 8 ≤ t := by dsimp [t]; linarith
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : t+1 = T := by dsimp [t]; ring
  have hgradPoly : 0 ≤ uniformLargeGrad0Poly m a t x := by
    rw [← uniformGradB0_large_coordinates m a t Y]
    rw [hnid, hTid]
    positivity
  have hsample := uniformLargeMidSample_nonneg_of_t_ge_eight_grad
    m a t x hm ha ha1 ht hx hgradPoly
  unfold uniformLargeMidSample at hsample
  rw [show x/a = Y by dsimp [x]; field_simp [ha.ne']] at hsample
  rw [hnid, hTid] at hsample
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos ha)).mp hsample

/-- Unconditional terminal-face nonnegativity in the uniform `k = 3`
induction step. -/
theorem uniformSharpFaceB_nonneg
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1) :
    0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformSharpFaceB n a T Y q := by
  apply uniformSharpFaceB_nonneg_of_large_mid0_above_nine
    n a T Y q hn ha ha1 hT hY hq hq1
  intro hT9 hgrad0
  exact uniformFaceBCoreB1_nonneg_of_T_ge_nine_grad0
    n a T Y hn ha ha1 hT9 hY.le hgrad0


end SSP.K3AllStages
