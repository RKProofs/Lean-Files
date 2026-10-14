import SSPLean.K3CyclicRealTailLowBridge

/-! Generated tensor-Bernstein slice `k = 3`. -/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace SSP.K3CyclicRealTail

open scoped BigOperators

set_option maxHeartbeats 0 in
theorem bernsteinYCoefficient_chart_3 (s d : ℝ) :
    bernsteinYCoefficient
        (lowPowerCoefficient (realRootChartU s d) (realRootChartV s d)) 3 =
      varianceLowBernsteinSlice 3 (s ^ 2) (d ^ 2) := by
  norm_num [bernsteinYCoefficient, Finset.sum_range_succ, Nat.choose]
  rw [lowPowerCoefficient_chart_0, lowPowerCoefficient_chart_1, lowPowerCoefficient_chart_2, lowPowerCoefficient_chart_3]
  norm_num (config := { maxSteps := 1000000 })
    [varianceLowBernsteinSlice, varianceLowBernsteinCoeff,
      varianceLowBernsteinCoeffQ, varianceLowBernsteinPair,
      varianceLowBernsteinData3, bernsteinBasis, Finset.sum_range_succ,
      Nat.choose, varianceLowPower0,
      varianceLowPower1,
      varianceLowPower2,
      varianceLowPower3]
  ring

end SSP.K3CyclicRealTail
