import SSPLean.K3CyclicRealFullCoefficient

/-! Generated Bernstein certificate for `M = 5` (total degree `N = 11`). -/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace SSP.K3CyclicRealTail

set_option maxHeartbeats 0 in
noncomputable def fullCoeff5Q : ℕ → ℕ → ℚ
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
  | 0, 10 => 0
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
  | 1, 10 => 0
  | 2, 0 => (19 / 120 : ℚ)
  | 2, 1 => (19 / 150 : ℚ)
  | 2, 2 => (133 / 1350 : ℚ)
  | 2, 3 => (133 / 1800 : ℚ)
  | 2, 4 => (19 / 360 : ℚ)
  | 2, 5 => (19 / 540 : ℚ)
  | 2, 6 => (19 / 900 : ℚ)
  | 2, 7 => (19 / 1800 : ℚ)
  | 2, 8 => (19 / 5400 : ℚ)
  | 2, 9 => 0
  | 2, 10 => 0
  | 3, 0 => (323 / 640 : ℚ)
  | 3, 1 => (2603 / 6400 : ℚ)
  | 3, 2 => (3059 / 9600 : ℚ)
  | 3, 3 => (18487 / 76800 : ℚ)
  | 3, 4 => (133 / 768 : ℚ)
  | 3, 5 => (893 / 7680 : ℚ)
  | 3, 6 => (1349 / 19200 : ℚ)
  | 3, 7 => (2717 / 76800 : ℚ)
  | 3, 8 => (19 / 1600 : ℚ)
  | 3, 9 => 0
  | 3, 10 => 0
  | 4, 0 => (611 / 560 : ℚ)
  | 4, 1 => (9897 / 11200 : ℚ)
  | 4, 2 => (731 / 1050 : ℚ)
  | 4, 3 => (71123 / 134400 : ℚ)
  | 4, 4 => (601 / 1568 : ℚ)
  | 4, 5 => (24389 / 94080 : ℚ)
  | 4, 6 => (9283 / 58800 : ℚ)
  | 4, 7 => (513 / 6400 : ℚ)
  | 4, 8 => (19 / 700 : ℚ)
  | 4, 9 => 0
  | 4, 10 => 0
  | 5, 0 => (42661 / 21504 : ℚ)
  | 5, 1 => (23133 / 14336 : ℚ)
  | 5, 2 => (103111 / 80640 : ℚ)
  | 5, 3 => (1262971 / 1290240 : ℚ)
  | 5, 4 => (215219 / 301056 : ℚ)
  | 5, 5 => (41977 / 86016 : ℚ)
  | 5, 6 => (135577 / 451584 : ℚ)
  | 5, 7 => (2071 / 13440 : ℚ)
  | 5, 8 => (19 / 360 : ℚ)
  | 5, 9 => 0
  | 5, 10 => 0
  | 6, 0 => (46449 / 14336 : ℚ)
  | 6, 1 => (29663 / 11200 : ℚ)
  | 6, 2 => (379139 / 179200 : ℚ)
  | 6, 3 => (3520543 / 2150400 : ℚ)
  | 6, 4 => (3646033 / 3010560 : ℚ)
  | 6, 5 => (252493 / 301056 : ℚ)
  | 6, 6 => (985769 / 1881600 : ℚ)
  | 6, 7 => (437 / 1600 : ℚ)
  | 6, 8 => (19 / 200 : ℚ)
  | 6, 9 => 0
  | 6, 10 => 0
  | 7, 0 => (795389 / 163840 : ℚ)
  | 7, 1 => (6543601 / 1638400 : ℚ)
  | 7, 2 => (23825909 / 7372800 : ℚ)
  | 7, 3 => (3337557 / 1310720 : ℚ)
  | 7, 4 => (33127781 / 17203200 : ℚ)
  | 7, 5 => (3526283 / 2580480 : ℚ)
  | 7, 6 => (941183 / 1075200 : ℚ)
  | 7, 7 => (1197 / 2560 : ℚ)
  | 7, 8 => (133 / 800 : ℚ)
  | 7, 9 => 0
  | 7, 10 => 0
  | 8, 0 => (204577 / 30720 : ℚ)
  | 8, 1 => (3393671 / 614400 : ℚ)
  | 8, 2 => (3155303 / 691200 : ℚ)
  | 8, 3 => (27379387 / 7372800 : ℚ)
  | 8, 4 => (1345811 / 460800 : ℚ)
  | 8, 5 => (418609 / 193536 : ℚ)
  | 8, 6 => (582997 / 403200 : ℚ)
  | 8, 7 => (3857 / 4800 : ℚ)
  | 8, 8 => (133 / 450 : ℚ)
  | 8, 9 => 0
  | 8, 10 => 0
  | 9, 0 => (1066941 / 131072 : ℚ)
  | 9, 1 => (44733363 / 6553600 : ℚ)
  | 9, 2 => (5767831 / 983040 : ℚ)
  | 9, 3 => (8309943 / 1638400 : ℚ)
  | 9, 4 => (6147431 / 1433600 : ℚ)
  | 9, 5 => (736201 / 215040 : ℚ)
  | 9, 6 => (31487 / 12800 : ℚ)
  | 9, 7 => (2337 / 1600 : ℚ)
  | 9, 8 => (57 / 100 : ℚ)
  | 9, 9 => 0
  | 9, 10 => 0
  | 10, 0 => (4262409 / 524288 : ℚ)
  | 10, 1 => (912483 / 131072 : ℚ)
  | 10, 2 => (3235141 / 491520 : ℚ)
  | 10, 3 => (213647 / 32768 : ℚ)
  | 10, 4 => (912913 / 143360 : ℚ)
  | 10, 5 => (125381 / 21504 : ℚ)
  | 10, 6 => (21341 / 4480 : ℚ)
  | 10, 7 => (513 / 160 : ℚ)
  | 10, 8 => (57 / 40 : ℚ)
  | 10, 9 => 0
  | 10, 10 => 0
  | _, _ => 0

set_option maxHeartbeats 0 in
noncomputable def fullCoeff5 (i j : ℕ) : ℝ := fullCoeff5Q i j

set_option maxHeartbeats 0 in
theorem fullCoeff5_nonneg (i : ℕ) (hi : i ∈ Finset.range 11)
    (j : ℕ) (hj : j ∈ Finset.range 11) : 0 ≤ fullCoeff5 i j := by
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  interval_cases i <;> interval_cases j <;> norm_num [fullCoeff5, fullCoeff5Q]

set_option maxHeartbeats 0 in
theorem fullCurvatureCoefficient_chart_5_certificate (s d : ℝ) :
    fullCurvatureCoefficient (realRootChartU s d) (realRootChartV s d) 5 =
      tensorBernstein2 10 fullCoeff5 (s ^ 2) (d ^ 2) := by
  norm_num (config := { maxSteps := 2000000 })
    [fullCurvatureCoefficient, varianceCoefficient, symmetricProduct,
      normalizedComplete, splitWeight, splitKappa, complete3, diagonal,
      realRootChartU, realRootChartV, tensorBernstein2, fullCoeff5, fullCoeff5Q,
      bernsteinBasis, Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 0 in
theorem fullCurvatureCoefficient_chart_5_nonneg
    {s d : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    0 ≤ fullCurvatureCoefficient
      (realRootChartU s d) (realRootChartV s d) 5 := by
  apply fullCurvatureCoefficient_chart_nonneg_of_bernstein
    hs0 hs1 hd0 hd1 fullCoeff5_nonneg
  exact fullCurvatureCoefficient_chart_5_certificate s d

end SSP.K3CyclicRealTail

