import SSPLean.K3CyclicRealTailLowBridge

/-! Generated tensor-Bernstein slice `k = 10`. -/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace SSP.K3CyclicRealTail

open scoped BigOperators

set_option maxHeartbeats 0 in
theorem bernsteinYCoefficient_chart_10 (s d : ℝ) :
    bernsteinYCoefficient
        (lowPowerCoefficient (realRootChartU s d) (realRootChartV s d)) 10 =
      varianceLowBernsteinSlice 10 (s ^ 2) (d ^ 2) := by
  norm_num [bernsteinYCoefficient, Finset.sum_range_succ, Nat.choose]
  rw [lowPowerCoefficient_chart_0, lowPowerCoefficient_chart_1, lowPowerCoefficient_chart_2, lowPowerCoefficient_chart_3, lowPowerCoefficient_chart_4, lowPowerCoefficient_chart_5, lowPowerCoefficient_chart_6, lowPowerCoefficient_chart_7, lowPowerCoefficient_chart_8, lowPowerCoefficient_chart_9, lowPowerCoefficient_chart_10]
  norm_num (config := { maxSteps := 1000000 })
    [varianceLowBernsteinSlice, varianceLowBernsteinCoeff,
      varianceLowBernsteinCoeffQ, varianceLowBernsteinPair,
      varianceLowBernsteinData10, bernsteinBasis, Finset.sum_range_succ,
      Nat.choose, varianceLowPower0,
      varianceLowPower1,
      varianceLowPower2,
      varianceLowPower3,
      varianceLowPower4,
      varianceLowPower5,
      varianceLowPower6,
      varianceLowPower7,
      varianceLowPower8,
      varianceLowPower9,
      varianceLowPower10]
  ring

end SSP.K3CyclicRealTail
