import SSPLean.K3CyclicRealTailLowCertificate

/-! Generated low-memory bridge from the analytic definitions to the certificate. -/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace SSP.K3CyclicRealTail

open scoped BigOperators

noncomputable def lowPowerCoefficient (u v : ℝ) (r : ℕ) : ℝ :=
  if r ≤ 10 then
    varianceCoefficient u v (10 - r) /
      ((10 : ℝ) ^ r * (Nat.factorial (16 - r) : ℝ))
  else 0

theorem varianceLowBlock_eq_power (u v y : ℝ) :
    varianceLowBlock u v y =
      ∑ r ∈ Finset.range 11, lowPowerCoefficient u v r * y ^ r := by
  norm_num [varianceLowBlock, lowPowerCoefficient, Finset.sum_range_succ]
  ring

noncomputable def bernsteinYCoefficient (p : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (k + 1),
    p r * (Nat.choose k r : ℝ) / (Nat.choose 10 r : ℝ)

theorem power_eq_bernstein10 (p : ℕ → ℝ) (y : ℝ) :
    (∑ r ∈ Finset.range 11, p r * y ^ r) =
      ∑ k ∈ Finset.range 11,
        bernsteinYCoefficient p k * bernsteinBasis 10 k y := by
  norm_num [bernsteinYCoefficient, bernsteinBasis, Finset.sum_range_succ,
    Nat.choose]
  ring

noncomputable def varianceLowBernsteinSlice (k : ℕ) (S D : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11,
    varianceLowBernsteinCoeff i j k * bernsteinBasis 10 i S *
      bernsteinBasis 10 j D

set_option maxHeartbeats 0 in
theorem normalizedComplete_chart_0 (s d : ℝ) :
    normalizedComplete (realRootChartU s d) (realRootChartV s d) 0 =
      normalizedChart0 (s ^ 2) (d ^ 2) := by
  norm_num [normalizedComplete, normalizedChart0, realRootChartU,
    realRootChartV, complete3, diagonal, Finset.sum_range_succ] <;>
    ring

set_option maxHeartbeats 0 in
theorem normalizedComplete_chart_1 (s d : ℝ) :
    normalizedComplete (realRootChartU s d) (realRootChartV s d) 1 =
      normalizedChart1 (s ^ 2) (d ^ 2) := by
  norm_num [normalizedComplete, normalizedChart1, realRootChartU,
    realRootChartV, complete3, diagonal, Finset.sum_range_succ] <;>
    ring

set_option maxHeartbeats 0 in
theorem normalizedComplete_chart_2 (s d : ℝ) :
    normalizedComplete (realRootChartU s d) (realRootChartV s d) 2 =
      normalizedChart2 (s ^ 2) (d ^ 2) := by
  norm_num [normalizedComplete, normalizedChart2, realRootChartU,
    realRootChartV, complete3, diagonal, Finset.sum_range_succ] <;>
    ring

set_option maxHeartbeats 0 in
theorem normalizedComplete_chart_3 (s d : ℝ) :
    normalizedComplete (realRootChartU s d) (realRootChartV s d) 3 =
      normalizedChart3 (s ^ 2) (d ^ 2) := by
  norm_num [normalizedComplete, normalizedChart3, realRootChartU,
    realRootChartV, complete3, diagonal, Finset.sum_range_succ] <;>
    ring

set_option maxHeartbeats 0 in
theorem normalizedComplete_chart_4 (s d : ℝ) :
    normalizedComplete (realRootChartU s d) (realRootChartV s d) 4 =
      normalizedChart4 (s ^ 2) (d ^ 2) := by
  norm_num [normalizedComplete, normalizedChart4, realRootChartU,
    realRootChartV, complete3, diagonal, Finset.sum_range_succ] <;>
    ring

set_option maxHeartbeats 0 in
theorem normalizedComplete_chart_5 (s d : ℝ) :
    normalizedComplete (realRootChartU s d) (realRootChartV s d) 5 =
      normalizedChart5 (s ^ 2) (d ^ 2) := by
  norm_num [normalizedComplete, normalizedChart5, realRootChartU,
    realRootChartV, complete3, diagonal, Finset.sum_range_succ] <;>
    ring

set_option maxHeartbeats 0 in
theorem normalizedComplete_chart_6 (s d : ℝ) :
    normalizedComplete (realRootChartU s d) (realRootChartV s d) 6 =
      normalizedChart6 (s ^ 2) (d ^ 2) := by
  norm_num [normalizedComplete, normalizedChart6, realRootChartU,
    realRootChartV, complete3, diagonal, Finset.sum_range_succ] <;>
    ring

set_option maxHeartbeats 0 in
theorem normalizedComplete_chart_7 (s d : ℝ) :
    normalizedComplete (realRootChartU s d) (realRootChartV s d) 7 =
      normalizedChart7 (s ^ 2) (d ^ 2) := by
  norm_num [normalizedComplete, normalizedChart7, realRootChartU,
    realRootChartV, complete3, diagonal, Finset.sum_range_succ] <;>
    ring

set_option maxHeartbeats 0 in
theorem normalizedComplete_chart_8 (s d : ℝ) :
    normalizedComplete (realRootChartU s d) (realRootChartV s d) 8 =
      normalizedChart8 (s ^ 2) (d ^ 2) := by
  norm_num [normalizedComplete, normalizedChart8, realRootChartU,
    realRootChartV, complete3, diagonal, Finset.sum_range_succ] <;>
    ring

set_option maxHeartbeats 0 in
theorem normalizedComplete_chart_9 (s d : ℝ) :
    normalizedComplete (realRootChartU s d) (realRootChartV s d) 9 =
      normalizedChart9 (s ^ 2) (d ^ 2) := by
  norm_num [normalizedComplete, normalizedChart9, realRootChartU,
    realRootChartV, complete3, diagonal, Finset.sum_range_succ] <;>
    ring

set_option maxHeartbeats 0 in
theorem normalizedComplete_chart_10 (s d : ℝ) :
    normalizedComplete (realRootChartU s d) (realRootChartV s d) 10 =
      normalizedChart10 (s ^ 2) (d ^ 2) := by
  norm_num [normalizedComplete, normalizedChart10, realRootChartU,
    realRootChartV, complete3, diagonal, Finset.sum_range_succ] <;>
    ring

set_option maxHeartbeats 0 in
theorem lowPowerCoefficient_chart_0 (s d : ℝ) :
    lowPowerCoefficient (realRootChartU s d) (realRootChartV s d) 0 =
      varianceLowPower0 (s ^ 2) (d ^ 2) := by
  norm_num [lowPowerCoefficient, varianceCoefficient, symmetricProduct,
    splitWeight, splitKappa, Finset.sum_range_succ, Nat.choose]
  try simp only [normalizedComplete_chart_0,
      normalizedComplete_chart_1,
      normalizedComplete_chart_2,
      normalizedComplete_chart_3,
      normalizedComplete_chart_4,
      normalizedComplete_chart_5,
      normalizedComplete_chart_6,
      normalizedComplete_chart_7,
      normalizedComplete_chart_8,
      normalizedComplete_chart_9,
      normalizedComplete_chart_10]
  norm_num [varianceLowPower0, realRootChartU, realRootChartV,
      normalizedChart0,
      normalizedChart1,
      normalizedChart2,
      normalizedChart3,
      normalizedChart4,
      normalizedChart5,
      normalizedChart6,
      normalizedChart7,
      normalizedChart8,
      normalizedChart9,
      normalizedChart10] <;>
    ring

set_option maxHeartbeats 0 in
theorem lowPowerCoefficient_chart_1 (s d : ℝ) :
    lowPowerCoefficient (realRootChartU s d) (realRootChartV s d) 1 =
      varianceLowPower1 (s ^ 2) (d ^ 2) := by
  norm_num [lowPowerCoefficient, varianceCoefficient, symmetricProduct,
    splitWeight, splitKappa, Finset.sum_range_succ, Nat.choose]
  try simp only [normalizedComplete_chart_0,
      normalizedComplete_chart_1,
      normalizedComplete_chart_2,
      normalizedComplete_chart_3,
      normalizedComplete_chart_4,
      normalizedComplete_chart_5,
      normalizedComplete_chart_6,
      normalizedComplete_chart_7,
      normalizedComplete_chart_8,
      normalizedComplete_chart_9]
  norm_num [varianceLowPower1, realRootChartU, realRootChartV,
      normalizedChart0,
      normalizedChart1,
      normalizedChart2,
      normalizedChart3,
      normalizedChart4,
      normalizedChart5,
      normalizedChart6,
      normalizedChart7,
      normalizedChart8,
      normalizedChart9] <;>
    ring

set_option maxHeartbeats 0 in
theorem lowPowerCoefficient_chart_2 (s d : ℝ) :
    lowPowerCoefficient (realRootChartU s d) (realRootChartV s d) 2 =
      varianceLowPower2 (s ^ 2) (d ^ 2) := by
  norm_num [lowPowerCoefficient, varianceCoefficient, symmetricProduct,
    splitWeight, splitKappa, Finset.sum_range_succ, Nat.choose]
  try simp only [normalizedComplete_chart_0,
      normalizedComplete_chart_1,
      normalizedComplete_chart_2,
      normalizedComplete_chart_3,
      normalizedComplete_chart_4,
      normalizedComplete_chart_5,
      normalizedComplete_chart_6,
      normalizedComplete_chart_7,
      normalizedComplete_chart_8]
  norm_num [varianceLowPower2, realRootChartU, realRootChartV,
      normalizedChart0,
      normalizedChart1,
      normalizedChart2,
      normalizedChart3,
      normalizedChart4,
      normalizedChart5,
      normalizedChart6,
      normalizedChart7,
      normalizedChart8] <;>
    ring

set_option maxHeartbeats 0 in
theorem lowPowerCoefficient_chart_3 (s d : ℝ) :
    lowPowerCoefficient (realRootChartU s d) (realRootChartV s d) 3 =
      varianceLowPower3 (s ^ 2) (d ^ 2) := by
  norm_num [lowPowerCoefficient, varianceCoefficient, symmetricProduct,
    splitWeight, splitKappa, Finset.sum_range_succ, Nat.choose]
  try simp only [normalizedComplete_chart_0,
      normalizedComplete_chart_1,
      normalizedComplete_chart_2,
      normalizedComplete_chart_3,
      normalizedComplete_chart_4,
      normalizedComplete_chart_5,
      normalizedComplete_chart_6,
      normalizedComplete_chart_7]
  norm_num [varianceLowPower3, realRootChartU, realRootChartV,
      normalizedChart0,
      normalizedChart1,
      normalizedChart2,
      normalizedChart3,
      normalizedChart4,
      normalizedChart5,
      normalizedChart6,
      normalizedChart7] <;>
    ring

set_option maxHeartbeats 0 in
theorem lowPowerCoefficient_chart_4 (s d : ℝ) :
    lowPowerCoefficient (realRootChartU s d) (realRootChartV s d) 4 =
      varianceLowPower4 (s ^ 2) (d ^ 2) := by
  norm_num [lowPowerCoefficient, varianceCoefficient, symmetricProduct,
    splitWeight, splitKappa, Finset.sum_range_succ, Nat.choose]
  try simp only [normalizedComplete_chart_0,
      normalizedComplete_chart_1,
      normalizedComplete_chart_2,
      normalizedComplete_chart_3,
      normalizedComplete_chart_4,
      normalizedComplete_chart_5,
      normalizedComplete_chart_6]
  norm_num [varianceLowPower4, realRootChartU, realRootChartV,
      normalizedChart0,
      normalizedChart1,
      normalizedChart2,
      normalizedChart3,
      normalizedChart4,
      normalizedChart5,
      normalizedChart6] <;>
    ring

set_option maxHeartbeats 0 in
theorem lowPowerCoefficient_chart_5 (s d : ℝ) :
    lowPowerCoefficient (realRootChartU s d) (realRootChartV s d) 5 =
      varianceLowPower5 (s ^ 2) (d ^ 2) := by
  norm_num [lowPowerCoefficient, varianceCoefficient, symmetricProduct,
    splitWeight, splitKappa, Finset.sum_range_succ, Nat.choose]
  try simp only [normalizedComplete_chart_0,
      normalizedComplete_chart_1,
      normalizedComplete_chart_2,
      normalizedComplete_chart_3,
      normalizedComplete_chart_4,
      normalizedComplete_chart_5]
  norm_num [varianceLowPower5, realRootChartU, realRootChartV,
      normalizedChart0,
      normalizedChart1,
      normalizedChart2,
      normalizedChart3,
      normalizedChart4,
      normalizedChart5] <;>
    ring

set_option maxHeartbeats 0 in
theorem lowPowerCoefficient_chart_6 (s d : ℝ) :
    lowPowerCoefficient (realRootChartU s d) (realRootChartV s d) 6 =
      varianceLowPower6 (s ^ 2) (d ^ 2) := by
  norm_num [lowPowerCoefficient, varianceCoefficient, symmetricProduct,
    splitWeight, splitKappa, Finset.sum_range_succ, Nat.choose]
  try simp only [normalizedComplete_chart_0,
      normalizedComplete_chart_1,
      normalizedComplete_chart_2,
      normalizedComplete_chart_3,
      normalizedComplete_chart_4]
  norm_num [varianceLowPower6, realRootChartU, realRootChartV,
      normalizedChart0,
      normalizedChart1,
      normalizedChart2,
      normalizedChart3,
      normalizedChart4] <;>
    ring

set_option maxHeartbeats 0 in
theorem lowPowerCoefficient_chart_7 (s d : ℝ) :
    lowPowerCoefficient (realRootChartU s d) (realRootChartV s d) 7 =
      varianceLowPower7 (s ^ 2) (d ^ 2) := by
  norm_num [lowPowerCoefficient, varianceCoefficient, symmetricProduct,
    splitWeight, splitKappa, Finset.sum_range_succ, Nat.choose]
  try simp only [normalizedComplete_chart_0,
      normalizedComplete_chart_1,
      normalizedComplete_chart_2,
      normalizedComplete_chart_3]
  norm_num [varianceLowPower7, realRootChartU, realRootChartV,
      normalizedChart0,
      normalizedChart1,
      normalizedChart2,
      normalizedChart3] <;>
    ring

set_option maxHeartbeats 0 in
theorem lowPowerCoefficient_chart_8 (s d : ℝ) :
    lowPowerCoefficient (realRootChartU s d) (realRootChartV s d) 8 =
      varianceLowPower8 (s ^ 2) (d ^ 2) := by
  norm_num [lowPowerCoefficient, varianceCoefficient, symmetricProduct,
    splitWeight, splitKappa, Finset.sum_range_succ, Nat.choose]
  try simp only [normalizedComplete_chart_0,
      normalizedComplete_chart_1,
      normalizedComplete_chart_2]
  norm_num [varianceLowPower8, realRootChartU, realRootChartV,
      normalizedChart0,
      normalizedChart1,
      normalizedChart2] <;>
    ring

set_option maxHeartbeats 0 in
theorem lowPowerCoefficient_chart_9 (s d : ℝ) :
    lowPowerCoefficient (realRootChartU s d) (realRootChartV s d) 9 =
      varianceLowPower9 (s ^ 2) (d ^ 2) := by
  norm_num [lowPowerCoefficient, varianceCoefficient, symmetricProduct,
    splitWeight, splitKappa, Finset.sum_range_succ, Nat.choose]
  try simp only [normalizedComplete_chart_0,
      normalizedComplete_chart_1]
  norm_num [varianceLowPower9, realRootChartU, realRootChartV,
      normalizedChart0,
      normalizedChart1] <;>
    ring

set_option maxHeartbeats 0 in
theorem lowPowerCoefficient_chart_10 (s d : ℝ) :
    lowPowerCoefficient (realRootChartU s d) (realRootChartV s d) 10 =
      varianceLowPower10 (s ^ 2) (d ^ 2) := by
  norm_num [lowPowerCoefficient, varianceCoefficient, symmetricProduct,
    splitWeight, splitKappa, Finset.sum_range_succ, Nat.choose]
  try simp only [normalizedComplete_chart_0]
  norm_num [varianceLowPower10, realRootChartU, realRootChartV,
      normalizedChart0] <;>
    ring

end SSP.K3CyclicRealTail
