import SSPLean.K3CyclicComplexFirstBernsteinConversion
import SSPLean.K3CyclicComplexFirstCertificateBridge
import SSPLean.K3CyclicComplexFirstDegreeBounds

/-! # Compact nonnegativity for the complex first start

The executable sign and degree certificates are combined here with the exact
tensor-Bernstein reconstruction theorem.  Thus the checked Bernstein signs
apply to the original dense curvature coefficient, not merely to a separately
constructed polynomial.
-/

set_option autoImplicit false

namespace SSP.K3CyclicComplex

open Dense

namespace ComplexCoeff

theorem curvatureCoefficient_nonneg_through_seventy {N : ℕ} (hN : N ≤ 70)
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
  have hc : 0 ≤ (bernCoeffOf (curvatureCoefficient N) N i j : ℝ) := by
    exact_mod_cast bernCoeffOf_nonneg_of_certificate
      (certificate_through_seventy hN) hiN hjN
  have hr : 0 ≤ (Nat.choose N i : ℝ) * r ^ i * (1 - r) ^ (N - i) := by
    positivity
  have ht : 0 ≤ (Nat.choose (N / 2) j : ℝ) * t ^ j *
      (1 - t) ^ (N / 2 - j) := by
    positivity
  positivity

end ComplexCoeff

end SSP.K3CyclicComplex
