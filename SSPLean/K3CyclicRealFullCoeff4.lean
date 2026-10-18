import SSPLean.K3CyclicRealFullCoefficient

/-! Generated Bernstein certificate for `M = 4` (total degree `N = 10`). -/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace SSP.K3CyclicRealTail

set_option maxHeartbeats 0 in
noncomputable def fullCoeff4Q : ℕ → ℕ → ℚ
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 0, 6 => 0
  | 0, 7 => 0
  | 0, 8 => 0
  | 0, 9 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 0
  | 1, 5 => 0
  | 1, 6 => 0
  | 1, 7 => 0
  | 1, 8 => 0
  | 1, 9 => 0
  | 2, 0 => (47 / 288 : ℚ)
  | 2, 1 => (329 / 2592 : ℚ)
  | 2, 2 => (329 / 3456 : ℚ)
  | 2, 3 => (235 / 3456 : ℚ)
  | 2, 4 => (235 / 5184 : ℚ)
  | 2, 5 => (47 / 1728 : ℚ)
  | 2, 6 => (47 / 3456 : ℚ)
  | 2, 7 => (47 / 10368 : ℚ)
  | 2, 8 => 0
  | 2, 9 => 0
  | 3, 0 => (235 / 448 : ℚ)
  | 3, 1 => (2491 / 6048 : ℚ)
  | 3, 2 => (5029 / 16128 : ℚ)
  | 3, 3 => (705 / 3136 : ℚ)
  | 3, 4 => (25615 / 169344 : ℚ)
  | 3, 5 => (2585 / 28224 : ℚ)
  | 3, 6 => (1739 / 37632 : ℚ)
  | 3, 7 => (47 / 3024 : ℚ)
  | 3, 8 => 0
  | 3, 9 => 0
  | 4, 0 => (6067 / 5376 : ℚ)
  | 4, 1 => (18587 / 20736 : ℚ)
  | 4, 2 => (66431 / 96768 : ℚ)
  | 4, 3 => (37685 / 75264 : ℚ)
  | 4, 4 => (692605 / 2032128 : ℚ)
  | 4, 5 => (141427 / 677376 : ℚ)
  | 4, 6 => (47 / 441 : ℚ)
  | 4, 7 => (47 / 1296 : ℚ)
  | 4, 8 => 0
  | 4, 9 => 0
  | 5, 0 => (2707 / 1344 : ℚ)
  | 5, 1 => (78625 / 48384 : ℚ)
  | 5, 2 => (26231 / 20736 : ℚ)
  | 5, 3 => (211819 / 225792 : ℚ)
  | 5, 4 => (82471 / 127008 : ℚ)
  | 5, 5 => (821843 / 2032128 : ℚ)
  | 5, 6 => (47 / 224 : ℚ)
  | 5, 7 => (47 / 648 : ℚ)
  | 5, 8 => 0
  | 5, 9 => 0
  | 6, 0 => (26061 / 8192 : ℚ)
  | 6, 1 => (451499 / 172032 : ℚ)
  | 6, 2 => (12967763 / 6193152 : ℚ)
  | 6, 3 => (7675739 / 4816896 : ℚ)
  | 6, 4 => (109567 / 96768 : ℚ)
  | 6, 5 => (980243 / 1354752 : ℚ)
  | 6, 6 => (517 / 1344 : ℚ)
  | 6, 7 => (235 / 1728 : ℚ)
  | 6, 8 => 0
  | 6, 9 => 0
  | 7, 0 => (222415 / 49152 : ℚ)
  | 7, 1 => (853373 / 221184 : ℚ)
  | 7, 2 => (1887277 / 589824 : ℚ)
  | 7, 3 => (2621135 / 1032192 : ℚ)
  | 7, 4 => (546737 / 290304 : ℚ)
  | 7, 5 => (26983 / 21504 : ℚ)
  | 7, 6 => (799 / 1152 : ℚ)
  | 7, 7 => (329 / 1296 : ℚ)
  | 7, 8 => 0
  | 7, 9 => 0
  | 8, 0 => (562157 / 98304 : ℚ)
  | 8, 1 => (4552925 / 884736 : ℚ)
  | 8, 2 => (63023 / 13824 : ℚ)
  | 8, 3 => (6016595 / 1548288 : ℚ)
  | 8, 4 => (112391 / 36288 : ℚ)
  | 8, 5 => (321109 / 145152 : ℚ)
  | 8, 6 => (47 / 36 : ℚ)
  | 8, 7 => (329 / 648 : ℚ)
  | 8, 8 => 0
  | 8, 9 => 0
  | 9, 0 => (197325 / 32768 : ℚ)
  | 9, 1 => (595009 / 98304 : ℚ)
  | 9, 2 => (300337 / 49152 : ℚ)
  | 9, 3 => (10663 / 1792 : ℚ)
  | 9, 4 => (43541 / 8064 : ℚ)
  | 9, 5 => (70627 / 16128 : ℚ)
  | 9, 6 => (47 / 16 : ℚ)
  | 9, 7 => (47 / 36 : ℚ)
  | 9, 8 => 0
  | 9, 9 => 0
  | _, _ => 0

set_option maxHeartbeats 0 in
noncomputable def fullCoeff4 (i j : ℕ) : ℝ := fullCoeff4Q i j

set_option maxHeartbeats 0 in
theorem fullCoeff4_nonneg (i : ℕ) (hi : i ∈ Finset.range 10)
    (j : ℕ) (hj : j ∈ Finset.range 10) : 0 ≤ fullCoeff4 i j := by
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  interval_cases i <;> interval_cases j <;> norm_num [fullCoeff4, fullCoeff4Q]

set_option maxHeartbeats 0 in
theorem fullCurvatureCoefficient_chart_4_certificate (s d : ℝ) :
    fullCurvatureCoefficient (realRootChartU s d) (realRootChartV s d) 4 =
      tensorBernstein2 9 fullCoeff4 (s ^ 2) (d ^ 2) := by
  norm_num (config := { maxSteps := 2000000 })
    [fullCurvatureCoefficient, varianceCoefficient, symmetricProduct,
      normalizedComplete, splitWeight, splitKappa, complete3, diagonal,
      realRootChartU, realRootChartV, tensorBernstein2, fullCoeff4, fullCoeff4Q,
      bernsteinBasis, Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 0 in
theorem fullCurvatureCoefficient_chart_4_nonneg
    {s d : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    0 ≤ fullCurvatureCoefficient
      (realRootChartU s d) (realRootChartV s d) 4 := by
  apply fullCurvatureCoefficient_chart_nonneg_of_bernstein
    hs0 hs1 hd0 hd1 fullCoeff4_nonneg
  exact fullCurvatureCoefficient_chart_4_certificate s d

end SSP.K3CyclicRealTail
