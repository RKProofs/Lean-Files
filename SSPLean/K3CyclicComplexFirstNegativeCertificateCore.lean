import SSPLean.K3CyclicComplexFirstBernsteinConversion
import SSPLean.K3CyclicComplexFirstNegativeDegreeBounds

/-! # Semantic core of the negative-m compact certificate -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.NegativeCoeff

open Dense

theorem bernCoeff_nonneg_of_certificate {N i j : ℕ}
    (h : certificateOK N = true) (hi : i ≤ N) (hj : j ≤ N / 2) :
    0 ≤ ComplexCoeff.bernCoeffOf (curvatureCoefficient N) N i j := by
  simp only [certificateOK] at h
  have hi' := List.all_eq_true.mp h i
    (List.mem_range.mpr (Nat.lt_succ_iff.mpr hi))
  have hj' := List.all_eq_true.mp hi' j
    (List.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  exact of_decide_eq_true hj'

theorem curvatureCoefficient_nonneg_of_certificate {N : ℕ}
    (hcert : certificateOK N = true)
    {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ beval (curvatureCoefficient N) r t := by
  rw [beval_eq_tensorBernstein (curvatureCoefficient N) N
    curvatureCoefficient_outer_degree
    (fun b _hb => curvatureCoefficient_inner_degree)]
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hjN : j ≤ N / 2 := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hc : 0 ≤
      (ComplexCoeff.bernCoeffOf (curvatureCoefficient N) N i j : ℝ) := by
    exact_mod_cast bernCoeff_nonneg_of_certificate hcert hiN hjN
  have hr : 0 ≤ (Nat.choose N i : ℝ) * r ^ i * (1 - r) ^ (N - i) := by
    positivity
  have ht : 0 ≤ (Nat.choose (N / 2) j : ℝ) * t ^ j *
      (1 - t) ^ (N / 2 - j) := by
    positivity
  positivity

end SSP.K3CyclicComplex.NegativeCoeff
