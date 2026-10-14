import SSPLean.K3CyclicRealFullCoefficient

/-! Generated Bernstein certificate for `M = 3` (total degree `N = 9`). -/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace SSP.K3CyclicRealTail

noncomputable def fullCoeff3Q : ℕ → ℕ → ℚ
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 0, 6 => 0
  | 0, 7 => 0
  | 0, 8 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 0
  | 1, 5 => 0
  | 1, 6 => 0
  | 1, 7 => 0
  | 1, 8 => 0
  | 2, 0 => (19 / 112 : ℚ)
  | 2, 1 => (57 / 448 : ℚ)
  | 2, 2 => (285 / 3136 : ℚ)
  | 2, 3 => (95 / 1568 : ℚ)
  | 2, 4 => (57 / 1568 : ℚ)
  | 2, 5 => (57 / 3136 : ℚ)
  | 2, 6 => (19 / 3136 : ℚ)
  | 2, 7 => 0
  | 2, 8 => 0
  | 3, 0 => (247 / 448 : ℚ)
  | 3, 1 => (1501 / 3584 : ℚ)
  | 3, 2 => (475 / 1568 : ℚ)
  | 3, 3 => (2565 / 12544 : ℚ)
  | 3, 4 => (779 / 6272 : ℚ)
  | 3, 5 => (1577 / 25088 : ℚ)
  | 3, 6 => (19 / 896 : ℚ)
  | 3, 7 => 0
  | 3, 8 => 0
  | 4, 0 => (1067 / 896 : ℚ)
  | 4, 1 => (8261 / 8960 : ℚ)
  | 4, 2 => (8521 / 12544 : ℚ)
  | 4, 3 => (5855 / 12544 : ℚ)
  | 4, 4 => (18091 / 62720 : ℚ)
  | 4, 5 => (19 / 128 : ℚ)
  | 4, 6 => (57 / 1120 : ℚ)
  | 4, 7 => 0
  | 4, 8 => 0
  | 5, 0 => (1085 / 512 : ℚ)
  | 5, 1 => (48403 / 28672 : ℚ)
  | 5, 2 => (128367 / 100352 : ℚ)
  | 5, 3 => (181273 / 200704 : ℚ)
  | 5, 4 => (71861 / 125440 : ℚ)
  | 5, 5 => (1083 / 3584 : ℚ)
  | 5, 6 => (95 / 896 : ℚ)
  | 5, 7 => 0
  | 5, 8 => 0
  | 6, 0 => (95065 / 28672 : ℚ)
  | 6, 1 => (316201 / 114688 : ℚ)
  | 6, 2 => (1751881 / 802816 : ℚ)
  | 6, 3 => (20177 / 12544 : ℚ)
  | 6, 4 => (133387 / 125440 : ℚ)
  | 6, 5 => (1045 / 1792 : ℚ)
  | 6, 6 => (95 / 448 : ℚ)
  | 6, 7 => 0
  | 6, 8 => 0
  | 7, 0 => (76075 / 16384 : ℚ)
  | 7, 1 => (541565 / 131072 : ℚ)
  | 7, 2 => (114959 / 32768 : ℚ)
  | 7, 3 => (39769 / 14336 : ℚ)
  | 7, 4 => (7039 / 3584 : ℚ)
  | 7, 5 => (589 / 512 : ℚ)
  | 7, 6 => (57 / 128 : ℚ)
  | 7, 7 => 0
  | 7, 8 => 0
  | 8, 0 => (94285 / 16384 : ℚ)
  | 8, 1 => (94669 / 16384 : ℚ)
  | 8, 2 => (79589 / 14336 : ℚ)
  | 8, 3 => (17825 / 3584 : ℚ)
  | 8, 4 => (3583 / 896 : ℚ)
  | 8, 5 => (171 / 64 : ℚ)
  | 8, 6 => (19 / 16 : ℚ)
  | 8, 7 => 0
  | 8, 8 => 0
  | _, _ => 0

noncomputable def fullCoeff3 (i j : ℕ) : ℝ := fullCoeff3Q i j

set_option maxHeartbeats 0 in
theorem fullCoeff3_nonneg (i : ℕ) (hi : i ∈ Finset.range 9)
    (j : ℕ) (hj : j ∈ Finset.range 9) : 0 ≤ fullCoeff3 i j := by
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  interval_cases i <;> interval_cases j <;> norm_num [fullCoeff3, fullCoeff3Q]

set_option maxHeartbeats 0 in
theorem fullCurvatureCoefficient_chart_3_certificate (s d : ℝ) :
    fullCurvatureCoefficient (realRootChartU s d) (realRootChartV s d) 3 =
      tensorBernstein2 8 fullCoeff3 (s ^ 2) (d ^ 2) := by
  norm_num (config := { maxSteps := 2000000 })
    [fullCurvatureCoefficient, varianceCoefficient, symmetricProduct,
      normalizedComplete, splitWeight, splitKappa, complete3, diagonal,
      realRootChartU, realRootChartV, tensorBernstein2, fullCoeff3, fullCoeff3Q,
      bernsteinBasis, Finset.sum_range_succ, Nat.choose]
  ring

theorem fullCurvatureCoefficient_chart_3_nonneg
    {s d : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    0 ≤ fullCurvatureCoefficient
      (realRootChartU s d) (realRootChartV s d) 3 := by
  apply fullCurvatureCoefficient_chart_nonneg_of_bernstein
    hs0 hs1 hd0 hd1 fullCoeff3_nonneg
  exact fullCurvatureCoefficient_chart_3_certificate s d

end SSP.K3CyclicRealTail
