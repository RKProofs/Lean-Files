import SSPLean.K3AllStagesMiddleLow
import SSPLean.K3AllStagesMiddleHighCore

/-! # Assembly of the nonpositive-current-slope return-face certificates -/

set_option autoImplicit false

namespace SSP.K3AllStages

theorem uniformFaceANonposScaled_nonneg
    (m s v X : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) (hX : 0 ≤ X) :
    0 ≤ uniformFaceANonposScaled m s v X := by
  by_cases hX1 : X ≤ 1
  · exact uniformFaceANonposScaled_nonneg_of_X_le_one
      m s v X hm hs hv hv1 hX hX1
  by_cases hXmid : X ≤ m^2 + 39
  · exact uniformFaceANonposScaled_nonneg_of_middle_low
      m s v X hm hs hv hv1 (by linarith) hXmid
  by_cases hXtail : uniformFaceANonposP m / 8 ≤ X
  · exact uniformFaceANonposScaled_nonneg_of_large_X
      m s v X hm hs hv hv1 hXtail
  have hmpos : 0 < m := by
    by_contra hmnot
    have hmzero : m = 0 := le_antisymm (le_of_not_gt hmnot) hm
    subst m
    unfold uniformFaceANonposP at hXtail
    norm_num at hXmid hXtail
    linarith
  exact uniformFaceANonposScaled_nonneg_of_middle_high
    m s v X hmpos hs hv hv1 (by linarith) (le_of_not_ge hXtail)

theorem uniformFaceACore_nonneg_of_currentM_nonpos_complete
    (n X T q : ℝ) (hn : 4 ≤ n) (hX : 0 ≤ X)
    (hT1 : n - 1 ≤ T) (hq : 0 < q)
    (hM : uniformFaceACurrentM n T q ≤ 0) :
    0 ≤ uniformFaceACore n X T q := by
  apply uniformFaceACore_nonneg_of_currentM_nonpos n X T q hn hX hT1 hq hM
  intro m s v R hm hs hv hv1 hR
  exact uniformFaceANonposScaled_nonneg m s v R hm hs hv hv1 hR

theorem uniformSharpFaceA_nonneg_of_currentM_nonpos_complete
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hT1 : n - 1 ≤ T) (hY : 0 < Y)
    (hq : 0 < q) (hM : uniformFaceACurrentM n T q ≤ 0) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  apply uniformSharpFaceA_nonneg_of_currentM_nonpos
    n a T Y q hn ha hT hT1 hY hq hM
  intro m s v X hm hs hv hv1 hX
  exact uniformFaceANonposScaled_nonneg m s v X hm hs hv hv1 hX

end SSP.K3AllStages
