import SSPLean.K3CyclicComplexFirstPositiveTimeConversion

/-! # Semantic core of the positive-m three-variable certificate -/

set_option autoImplicit false

open Polynomial
open scoped BigOperators Polynomial

namespace SSP.K3CyclicComplex.PositiveCoeff

open Dense ComplexCoeff

theorem spatialBernCoeff_gt_one_of_certificate {powers : List Bi}
    {k i j : ℕ} (h : certificateAtFrom powers k = true)
    (hi : i ≤ order) (hj : j ≤ order / 2) :
    1 < bcoeff (spatialBernTableFrom powers k) i j := by
  simp only [certificateAtFrom] at h
  have hi' := List.all_eq_true.mp h i
    (List.mem_range.mpr (Nat.lt_succ_iff.mpr hi))
  have hj' := List.all_eq_true.mp hi' j
    (List.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  exact of_decide_eq_true hj'

theorem sum_real_bernsteinBasis (n : ℕ) (x : ℝ) :
    (∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℝ) * x ^ i * (1 - x) ^ (n - i)) = 1 := by
  have h := congrArg (fun p : ℝ[X] => p.eval x)
    (bernsteinPolynomial.sum (R := ℝ) n)
  simpa [Polynomial.eval_finsetSum, bernsteinPolynomial] using h

theorem beval_timeBernPoly_ge_one {k : ℕ} (hk : k ≤ order)
    (hcert : certificateAt k = true)
    {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 ≤ beval
      (timeBernPolyFrom (powerTableUpTo (k + 1)) k) r t := by
  let q := timeBernPolyFrom (powerTableUpTo (k + 1)) k
  have hq := timeBernPoly_bounded hk
  have hexp := SSP.K3CyclicComplex.beval_eq_tensorBernstein q order
    hq.1 (fun b _hb => by
      by_cases hmem : b < q.length
      · apply hq.2
        rw [List.getD_eq_getElem _ _ hmem]
        exact List.getElem_mem hmem
      · rw [List.getD_eq_default _ _ (by omega)]
        simp) r t
  have hsumR := sum_real_bernsteinBasis order r
  have hsumT := sum_real_bernsteinBasis (order / 2) t
  rw [hexp]
  calc
    1 = ∑ i ∈ Finset.range (order + 1),
        ∑ j ∈ Finset.range (order / 2 + 1),
          ((Nat.choose order i : ℝ) * r ^ i * (1 - r) ^ (order - i)) *
          ((Nat.choose (order / 2) j : ℝ) * t ^ j *
            (1 - t) ^ (order / 2 - j)) := by
      calc
        _ = (∑ i ∈ Finset.range (order + 1),
              (Nat.choose order i : ℝ) * r ^ i *
                (1 - r) ^ (order - i)) *
            (∑ j ∈ Finset.range (order / 2 + 1),
              (Nat.choose (order / 2) j : ℝ) * t ^ j *
                (1 - t) ^ (order / 2 - j)) := by
              rw [hsumR, hsumT]
              ring
        _ = _ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (order + 1),
        ∑ j ∈ Finset.range (order / 2 + 1),
          (bcoeff (spatialBernTableFrom
              (powerTableUpTo (k + 1)) k) i j : ℝ) *
            ((Nat.choose order i : ℝ) * r ^ i *
              (1 - r) ^ (order - i)) *
            ((Nat.choose (order / 2) j : ℝ) * t ^ j *
              (1 - t) ^ (order / 2 - j)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hiN : i ≤ order :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hjN : j ≤ order / 2 :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hcQ := spatialBernCoeff_gt_one_of_certificate
        (powers := powerTableUpTo (k + 1))
        (by simpa [certificateAt] using hcert) hiN hjN
      have hc : (1 : ℝ) ≤
          (bcoeff (spatialBernTableFrom
            (powerTableUpTo (k + 1)) k) i j : ℝ) := by
        exact_mod_cast hcQ.le
      have hR : 0 ≤ (Nat.choose order i : ℝ) * r ^ i *
          (1 - r) ^ (order - i) := by positivity
      have hT : 0 ≤ (Nat.choose (order / 2) j : ℝ) * t ^ j *
          (1 - t) ^ (order / 2 - j) := by positivity
      nlinarith [mul_nonneg hR hT,
        mul_le_mul_of_nonneg_right hc (mul_nonneg hR hT)]

end SSP.K3CyclicComplex.PositiveCoeff
