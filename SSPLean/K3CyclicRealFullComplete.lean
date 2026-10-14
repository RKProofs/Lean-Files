import SSPLean.K3CyclicRealFullCoeff3
import SSPLean.K3CyclicRealFullCoeff4
import SSPLean.K3CyclicRealFullCoeff5
import SSPLean.K3CyclicRealFullCoeff6
import SSPLean.K3CyclicRealFullCoeff7
import SSPLean.K3CyclicRealFullCoeff8

/-! Assembly of all full first-start curvature coefficients. -/

set_option autoImplicit false

namespace SSP.K3CyclicRealTail

theorem fullCurvatureCoefficient_chart_nonneg
    {s d : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (M : ℕ) :
    0 ≤ fullCurvatureCoefficient
      (realRootChartU s d) (realRootChartV s d) M := by
  by_cases htail : 9 ≤ M
  · exact fullCurvatureCoefficient_tail_nonneg hs0 hs1 hd0 hd1 htail
  · have hM : M < 9 := by omega
    rcases realRootChart_admissible hs0 hs1 hd0 hd1 with
      ⟨hu, huv, hv1, hroot⟩
    have hv : 0 ≤ realRootChartV s d := hu.trans huv
    interval_cases M
    · exact fullCurvatureCoefficient_zero_nonneg hu hv
    · exact fullCurvatureCoefficient_one_nonneg_of_root hu hv hroot
    · exact fullCurvatureCoefficient_two_nonneg_of_root hu hv hroot
    · exact fullCurvatureCoefficient_chart_3_nonneg hs0 hs1 hd0 hd1
    · exact fullCurvatureCoefficient_chart_4_nonneg hs0 hs1 hd0 hd1
    · exact fullCurvatureCoefficient_chart_5_nonneg hs0 hs1 hd0 hd1
    · exact fullCurvatureCoefficient_chart_6_nonneg hs0 hs1 hd0 hd1
    · exact fullCurvatureCoefficient_chart_7_nonneg hs0 hs1 hd0 hd1
    · exact fullCurvatureCoefficient_chart_8_nonneg hs0 hs1 hd0 hd1

theorem fullCurvatureCoefficient_nonneg_of_root
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) (M : ℕ) :
    0 ≤ fullCurvatureCoefficient u v M := by
  rcases le_total u v with huv | hvu
  · rcases exists_realRootChart hu huv hroot with
      ⟨s, d, hs0, hs1, hd0, hd1, hU, hV⟩
    rw [← hU, ← hV]
    exact fullCurvatureCoefficient_chart_nonneg hs0 hs1 hd0 hd1 M
  · rw [fullCurvatureCoefficient_comm]
    rcases exists_realRootChart hv hvu (by simpa [add_comm] using hroot) with
      ⟨s, d, hs0, hs1, hd0, hd1, hV, hU⟩
    rw [← hV, ← hU]
    exact fullCurvatureCoefficient_chart_nonneg hs0 hs1 hd0 hd1 M

end SSP.K3CyclicRealTail
