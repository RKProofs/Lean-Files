import SSPLean.K3AllStagesMiddleLowB0
import SSPLean.K3AllStagesMiddleLowB1
import SSPLean.K3AllStagesMiddleLowB2
import SSPLean.K3AllStagesMiddleLowB3

/-! # Assembly of the lower-middle return-face certificate -/

set_option autoImplicit false
namespace SSP.K3AllStages

theorem uniformFaceANonposMiddleLow_nonneg
    (m s v w : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    0 ≤ uniformFaceANonposMiddleLow m s v w := by
  rw [uniformFaceANonposMiddleLow_bernstein_w]
  exact cornerBern3_nonneg _ _ _ _ _
    (uniformFaceANonposMiddleLowB0_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposMiddleLowB1_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposMiddleLowB2_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposMiddleLowB3_nonneg m s v hm hs hv hv1)
    hw hw1

theorem uniformFaceANonposScaled_nonneg_of_middle_low
    (m s v X : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hX1 : 1 ≤ X) (hXupper : X ≤ m^2 + 39) :
    0 ≤ uniformFaceANonposScaled m s v X := by
  let w := (X - 1) / (m^2 + 38)
  have hden : 0 < m^2 + 38 := by positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : w ≤ 1 := by
    dsimp [w]
    rw [div_le_one hden]
    linarith
  have hXid : 1 + w * (m^2 + 38) = X := by
    dsimp [w]
    field_simp [hden.ne']
    ring
  have hcert := uniformFaceANonposMiddleLow_nonneg
    m s v w hm hs hv hv1 hw hw1
  unfold uniformFaceANonposMiddleLow at hcert
  rwa [hXid] at hcert

end SSP.K3AllStages
