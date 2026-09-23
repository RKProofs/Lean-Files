import SSPLean.K3AllStagesPositiveSlopeLow

/-!
# Completion of the positive-current-slope return face
-/

set_option autoImplicit false

namespace SSP.K3AllStages

/-- The positive-current-slope polynomial certificate, with every chart
discharged. -/
theorem uniformFaceAPositive_poly_nonneg
    (m z q w : ℝ)
    (hm : 0 ≤ m) (hz : 0 ≤ z) (hq : 0 < q) (hq1 : q ≤ 1)
    (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hM : 0 < uniformFaceACurrentM (m + 4) (m + 3 + z) q)
    (hgrad : uniformFaceACurrentGradPoly (m + 4) (m + 3 + z) q w < 0) :
    0 ≤ uniformFaceACurrentPoly (m + 4) (m + 3 + z) q w := by
  apply uniformFaceAPositive_poly_nonneg_of_chart_certificates
    m z q w hm hz hq hq1 hw hw1 hM hgrad
  · intro m u q w hm hu hu1 hq hq1 hw hw1 _hgrad
    exact uniformFaceAPositiveLow_nonneg
      m u q w hm hu hu1 hq hq1 hw hw1
  · intro m s v t w hm hs hv hv1 ht _htHalf hw hw1 hvt _hgrad
    exact uniformFaceAPositiveHighVW_nonneg
      m s v t w hm hs hv hv1 ht hw hw1 hvt
  · intro m s v t w hm hs hv hv1 ht _ht1 hw hw1 hvt
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
    exact uniformFaceAPositiveHighVW_nonneg
      m s v t w hm hs hv hv1 htpos hw hw1 hvt

end SSP.K3AllStages
