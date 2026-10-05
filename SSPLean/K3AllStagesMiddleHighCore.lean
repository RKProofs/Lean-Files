import SSPLean.K3AllStagesMiddleHighB0
import SSPLean.K3AllStagesMiddleHighB1
import SSPLean.K3AllStagesMiddleHighB2
import SSPLean.K3AllStagesMiddleHighB3

/-! # Assembly of the upper-middle return-face certificate -/

set_option autoImplicit false
namespace SSP.K3AllStages

theorem uniformFaceANonposMiddleHigh_nonneg
    (m s v w : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    0 ≤ uniformFaceANonposMiddleHigh m s v w := by
  rw [uniformFaceANonposMiddleHigh_bernstein_w]
  exact cornerBern3_nonneg _ _ _ _ _
    (uniformFaceANonposMiddleHighB0_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposMiddleHighB1_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposMiddleHighB2_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposMiddleHighB3_nonneg m s v hm hs hv hv1)
    hw hw1

theorem uniformFaceANonposScaled_nonneg_of_middle_high
    (m s v X : ℝ) (hm : 0 < m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hXlower : m^2 + 39 ≤ X)
    (hXupper : X ≤ uniformFaceANonposP m / 8) :
    0 ≤ uniformFaceANonposScaled m s v X := by
  let L := m^2 + 39
  let R := uniformFaceANonposP m / 8
  let w := (X - L) / (R - L)
  have hwidth : 0 < R - L := by
    dsimp [R, L]
    unfold uniformFaceANonposP
    have hm0 : 0 ≤ m := hm.le
    have hpoly : 0 < 2*m^2 + 27*m + 191 := by positivity
    nlinarith [mul_pos hm hpoly]
  have hw : 0 ≤ w := by
    dsimp [w]
    exact div_nonneg (sub_nonneg.mpr hXlower) hwidth.le
  have hw1 : w ≤ 1 := by
    dsimp [w]
    rw [div_le_one hwidth]
    dsimp [R, L] at hXupper ⊢
    linarith
  have hXid : L + w * (R - L) = X := by
    dsimp [w]
    field_simp [hwidth.ne']
    ring
  have hcert := uniformFaceANonposMiddleHigh_nonneg
    m s v w hm.le hs hv hv1 hw hw1
  unfold uniformFaceANonposMiddleHigh at hcert
  change 0 ≤ uniformFaceANonposScaled m s v (L + w * (R - L)) at hcert
  rwa [hXid] at hcert

end SSP.K3AllStages
