import SSPLean.K3CyclicRealTailCoefficient

/-!
# The finite low-degree block in the three-state real-spectrum tail

This file isolates the final finite certificate from the analytic and
far-tail arguments.  The variable `M` below corresponds to total Taylor
degree `N = M + 6`; hence the low block consists of `0 ≤ M ≤ 10`.
-/

set_option autoImplicit false

namespace SSP.K3CyclicRealTail

open scoped BigOperators

/-- The coefficient `D̂_(M+6)` after removal of the common `(uv)^2` factor. -/
noncomputable def varianceCoefficient (u v : ℝ) (M : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (M + 1), splitWeight M i *
    symmetricProduct (normalizedComplete u v) M i *
      splitKappa (M + 6) (i + 3)

/-- After `y = 10/t`, this is `t^(-16)` times the Taylor block of degrees
`6,…,16`, up to the common positive factor `(uv)^2`. -/
noncomputable def varianceLowBlock (u v y : ℝ) : ℝ :=
  ∑ M ∈ Finset.range 11,
    varianceCoefficient u v M /
      ((10 : ℝ) ^ (10 - M) * (Nat.factorial (M + 6) : ℝ)) *
        y ^ (10 - M)

/-- Perron-normalized real-root chart. -/
noncomputable def realRootChartU (s d : ℝ) : ℝ :=
  s ^ 2 * (1 - d) ^ 2 / 4

noncomputable def realRootChartV (s d : ℝ) : ℝ :=
  s ^ 2 * (1 + d) ^ 2 / 4

theorem realRootChartU_nonneg (s d : ℝ) : 0 ≤ realRootChartU s d := by
  unfold realRootChartU
  positivity

theorem realRootChartV_nonneg (s d : ℝ) : 0 ≤ realRootChartV s d := by
  unfold realRootChartV
  positivity

/-- A degree-`n` Bernstein basis function. -/
noncomputable def bernsteinBasis (n i : ℕ) (x : ℝ) : ℝ :=
  (Nat.choose n i : ℝ) * x ^ i * (1 - x) ^ (n - i)

theorem bernsteinBasis_nonneg {n i : ℕ} {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ bernsteinBasis n i x := by
  unfold bernsteinBasis
  positivity

/-- Tensor Bernstein form used by the exact low-block certificate.  Degree
ten in each of `S=s²`, `D=d²`, and `y` is sufficient. -/
noncomputable def tensorBernstein10
    (c : ℕ → ℕ → ℕ → ℝ) (S D y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 11, ∑ j ∈ Finset.range 11, ∑ k ∈ Finset.range 11,
    c i j k * bernsteinBasis 10 i S * bernsteinBasis 10 j D *
      bernsteinBasis 10 k y

theorem tensorBernstein10_nonneg
    {c : ℕ → ℕ → ℕ → ℝ} {S D y : ℝ}
    (hc : ∀ i ∈ Finset.range 11, ∀ j ∈ Finset.range 11,
      ∀ k ∈ Finset.range 11, 0 ≤ c i j k)
    (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hD0 : 0 ≤ D) (hD1 : D ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ tensorBernstein10 c S D y := by
  unfold tensorBernstein10
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (hc i hi j hj k hk) (bernsteinBasis_nonneg hS0 hS1))
      (bernsteinBasis_nonneg hD0 hD1))
    (bernsteinBasis_nonneg hy0 hy1)

/-- A nonnegative tensor-Bernstein representation immediately proves the low
block.  The generated certificate supplies this representation downstream. -/
theorem varianceLowBlock_nonneg_of_tensorBernstein
    {c : ℕ → ℕ → ℕ → ℝ} {s d y : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hc : ∀ i ∈ Finset.range 11, ∀ j ∈ Finset.range 11,
      ∀ k ∈ Finset.range 11, 0 ≤ c i j k)
    (hcertificate :
      varianceLowBlock (realRootChartU s d) (realRootChartV s d) y =
        tensorBernstein10 c (s ^ 2) (d ^ 2) y) :
    0 ≤ varianceLowBlock (realRootChartU s d) (realRootChartV s d) y := by
  rw [hcertificate]
  apply tensorBernstein10_nonneg hc
  · positivity
  · nlinarith [sq_nonneg s, mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  · positivity
  · nlinarith [sq_nonneg d, mul_nonneg hd0 (sub_nonneg.mpr hd1)]
  · exact hy0
  · exact hy1

end SSP.K3CyclicRealTail
