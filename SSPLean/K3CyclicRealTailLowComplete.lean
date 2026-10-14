import SSPLean.K3CyclicRealTailLowSlice0
import SSPLean.K3CyclicRealTailLowSlice1
import SSPLean.K3CyclicRealTailLowSlice2
import SSPLean.K3CyclicRealTailLowSlice3
import SSPLean.K3CyclicRealTailLowSlice4
import SSPLean.K3CyclicRealTailLowSlice5
import SSPLean.K3CyclicRealTailLowSlice6
import SSPLean.K3CyclicRealTailLowSlice7
import SSPLean.K3CyclicRealTailLowSlice8
import SSPLean.K3CyclicRealTailLowSlice9
import SSPLean.K3CyclicRealTailLowSlice10

/-! Assembly of the finite real-spectrum variance-tail certificate. -/

set_option autoImplicit false

namespace SSP.K3CyclicRealTail

open scoped BigOperators

theorem varianceLowBernsteinSlices_eq_tensor (S D y : ℝ) :
    (∑ k ∈ Finset.range 11,
      varianceLowBernsteinSlice k S D * bernsteinBasis 10 k y) =
      tensorBernstein10 varianceLowBernsteinCoeff S D y := by
  unfold varianceLowBernsteinSlice tensorBernstein10
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

/-- Exact tensor-Bernstein representation of the degrees `6,…,16` block. -/
theorem varianceLowBlock_certificate (s d y : ℝ) :
    varianceLowBlock (realRootChartU s d) (realRootChartV s d) y =
      tensorBernstein10 varianceLowBernsteinCoeff (s ^ 2) (d ^ 2) y := by
  rw [varianceLowBlock_eq_power, power_eq_bernstein10]
  rw [show (∑ k ∈ Finset.range 11,
      bernsteinYCoefficient
          (lowPowerCoefficient (realRootChartU s d) (realRootChartV s d)) k *
        bernsteinBasis 10 k y) =
      ∑ k ∈ Finset.range 11,
        varianceLowBernsteinSlice k (s ^ 2) (d ^ 2) *
          bernsteinBasis 10 k y by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    interval_cases k <;>
      simp only [bernsteinYCoefficient_chart_0, bernsteinYCoefficient_chart_1,
        bernsteinYCoefficient_chart_2, bernsteinYCoefficient_chart_3,
        bernsteinYCoefficient_chart_4, bernsteinYCoefficient_chart_5,
        bernsteinYCoefficient_chart_6, bernsteinYCoefficient_chart_7,
        bernsteinYCoefficient_chart_8, bernsteinYCoefficient_chart_9,
        bernsteinYCoefficient_chart_10]]
  exact varianceLowBernsteinSlices_eq_tensor (s ^ 2) (d ^ 2) y

/-- The exact low-degree block required for the real-spectrum first-start
tail is nonnegative throughout the normalized cube. -/
theorem varianceLowBlock_nonneg
    {s d y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ varianceLowBlock (realRootChartU s d) (realRootChartV s d) y := by
  rw [varianceLowBlock_certificate]
  apply tensorBernstein10_nonneg
    (fun i hi j hj k hk => varianceLowBernsteinCoeff_nonneg i j k)
  · positivity
  · nlinarith [sq_nonneg s, mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  · positivity
  · nlinarith [sq_nonneg d, mul_nonneg hd0 (sub_nonneg.mpr hd1)]
  · exact hy0
  · exact hy1

/-- Tail-time form of `varianceLowBlock_nonneg`, with `y = 10/t`. -/
theorem varianceLowBlock_nonneg_of_t_ge_ten
    {s d t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (ht : 10 ≤ t) :
    0 ≤ varianceLowBlock (realRootChartU s d) (realRootChartV s d)
      (10 / t) := by
  apply varianceLowBlock_nonneg hs0 hs1 hd0 hd1
  · positivity
  · apply (div_le_one (by linarith : 0 < t)).2
    exact ht

end SSP.K3CyclicRealTail
