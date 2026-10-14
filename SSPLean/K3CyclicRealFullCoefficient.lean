import SSPLean.K3CyclicRealTailAnalytic

/-!
# Full first-start coefficients in the three-state real-root chart

Restoring the constant term `h₁ = 1 + w` adds a manifestly positive linear
term to the remainder curvature.  Since the remainder coefficients are
already nonnegative from total Taylor degree `15` onward, only degrees
`6, ..., 14` remain for a compact certificate.
-/

set_option autoImplicit false

namespace SSP.K3CyclicRealTail

open scoped BigOperators

/-- Two-variable tensor Bernstein form of a common degree `n`. -/
noncomputable def tensorBernstein2
    (n : ℕ) (c : ℕ → ℕ → ℝ) (S D : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    c i j * bernsteinBasis n i S * bernsteinBasis n j D

theorem tensorBernstein2_nonneg
    {n : ℕ} {c : ℕ → ℕ → ℝ} {S D : ℝ}
    (hc : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
      0 ≤ c i j)
    (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    0 ≤ tensorBernstein2 n c S D := by
  unfold tensorBernstein2
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg
    (mul_nonneg (hc i hi j hj) (bernsteinBasis_nonneg hS0 hS1))
    (bernsteinBasis_nonneg hD0 hD1)

/-- `N!` times the degree-`N` coefficient of the full corrected curvature,
with `N = M + 6`. -/
noncomputable def fullCurvatureCoefficient (u v : ℝ) (M : ℕ) : ℝ :=
  (u * v) ^ 2 * varianceCoefficient u v M +
    (((M + 6) * (M + 5) + 4 : ℕ) : ℝ) *
      (u * v) * complete3 u v (M + 3)

theorem fullCurvatureCoefficient_comm (u v : ℝ) (M : ℕ) :
    fullCurvatureCoefficient u v M =
      fullCurvatureCoefficient v u M := by
  unfold fullCurvatureCoefficient
  rw [varianceCoefficient_comm, complete3_comm]
  ring

/-- The previously proved coefficient tail immediately controls every full
coefficient of total degree at least `15`. -/
theorem fullCurvatureCoefficient_tail_nonneg_of_ordered
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv1 : v ≤ 1)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1)
    {M : ℕ} (hM : 9 ≤ M) :
    0 ≤ fullCurvatureCoefficient u v M := by
  unfold fullCurvatureCoefficient
  apply add_nonneg
  · exact mul_nonneg (sq_nonneg _)
      (normalizedComplete_splitCoefficient_nonneg_of_baseline_formula
        hu huv hv1 hroot hM)
  · exact mul_nonneg
      (mul_nonneg (by positivity) (mul_nonneg hu (hu.trans huv)))
      (complete3_nonneg hu (hu.trans huv) (M + 3))

theorem fullCurvatureCoefficient_tail_nonneg_of_root
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1)
    {M : ℕ} (hM : 9 ≤ M) :
    0 ≤ fullCurvatureCoefficient u v M := by
  have hsu : Real.sqrt u ≤ 1 := by
    nlinarith [Real.sqrt_nonneg v]
  have hsv : Real.sqrt v ≤ 1 := by
    nlinarith [Real.sqrt_nonneg u]
  have hu1 : u ≤ 1 := by
    nlinarith [Real.sq_sqrt hu, Real.sqrt_nonneg u]
  have hv1 : v ≤ 1 := by
    nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v]
  rcases le_total u v with huv | hvu
  · exact fullCurvatureCoefficient_tail_nonneg_of_ordered
      hu huv hv1 hroot hM
  · rw [fullCurvatureCoefficient_comm]
    apply fullCurvatureCoefficient_tail_nonneg_of_ordered hv hvu hu1
    · simpa [add_comm] using hroot
    · exact hM

/-- Chart form used by the forthcoming nine-degree certificate. -/
theorem fullCurvatureCoefficient_tail_nonneg
    {s d : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) {M : ℕ} (hM : 9 ≤ M) :
    0 ≤ fullCurvatureCoefficient
      (realRootChartU s d) (realRootChartV s d) M := by
  rcases realRootChart_admissible hs0 hs1 hd0 hd1 with
    ⟨hu, huv, hv1, hroot⟩
  exact fullCurvatureCoefficient_tail_nonneg_of_ordered
    hu huv hv1 hroot hM

/-- Once the nine coefficients `M = 0, ..., 8` are certified, every full
first-start coefficient follows.  This is the compact finite remainder of
the coefficientwise proof. -/
theorem fullCurvatureCoefficient_nonneg_of_first_nine
    {s d : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hlow : ∀ M, M < 9 →
      0 ≤ fullCurvatureCoefficient
        (realRootChartU s d) (realRootChartV s d) M) (M : ℕ) :
    0 ≤ fullCurvatureCoefficient
      (realRootChartU s d) (realRootChartV s d) M := by
  by_cases hM : 9 ≤ M
  · exact fullCurvatureCoefficient_tail_nonneg hs0 hs1 hd0 hd1 hM
  · exact hlow M (by omega)

theorem fullCurvatureCoefficient_zero_nonneg
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ fullCurvatureCoefficient u v 0 := by
  have huv : 0 ≤ u * v := mul_nonneg hu hv
  have hc : u * v ≤ complete3 u v 3 := by
    norm_num [complete3, diagonal, Finset.sum_range_succ]
    nlinarith [sq_nonneg u, sq_nonneg v,
      mul_nonneg hu (sq_nonneg v), mul_nonneg (sq_nonneg u) hv,
      pow_nonneg hu 3, pow_nonneg hv 3]
  norm_num [fullCurvatureCoefficient, varianceCoefficient,
    symmetricProduct, normalizedComplete, splitWeight, splitKappa,
    Finset.sum_range_succ, Nat.choose]
  nlinarith [mul_nonneg huv (sub_nonneg.mpr hc)]

theorem fullCurvatureCoefficient_one_nonneg_of_root
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) :
    0 ≤ fullCurvatureCoefficient u v 1 := by
  have huv : 0 ≤ u * v := mul_nonneg hu hv
  have huvsum : u + v ≤ 1 := by
    nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv,
      Real.sqrt_nonneg u, Real.sqrt_nonneg v,
      sq_nonneg (Real.sqrt u + Real.sqrt v)]
  have huv4 : 4 * (u * v) ≤ 1 := by
    nlinarith [sq_nonneg (u - v)]
  have hbad : 0 ≤ 23 - 12 * (u * v) * (1 + u + v) := by
    have hfac : 1 + u + v ≤ 2 := by linarith
    have hprod : (u * v) * (1 + u + v) ≤ (u * v) * 2 :=
      mul_le_mul_of_nonneg_left hfac huv
    nlinarith
  have hid : fullCurvatureCoefficient u v 1 =
      2 * u * v *
        (23 * u ^ 4 + 23 * u ^ 3 * v + 23 * u ^ 3 +
          23 * u ^ 2 * v ^ 2 + 23 * u ^ 2 + 23 * u * v ^ 3 +
          23 * u + 23 * v ^ 4 + 23 * v ^ 3 + 23 * v ^ 2 +
          23 * v + (23 - 12 * (u * v) * (1 + u + v))) := by
    norm_num [fullCurvatureCoefficient, varianceCoefficient,
      symmetricProduct, normalizedComplete, splitWeight, splitKappa,
      complete3, diagonal, Finset.sum_range_succ, Nat.choose]
    ring
  rw [hid]
  positivity

theorem fullCurvatureCoefficient_two_nonneg_of_root
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) :
    0 ≤ fullCurvatureCoefficient u v 2 := by
  have huvsum : u + v ≤ 1 := by
    nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv,
      Real.sqrt_nonneg u, Real.sqrt_nonneg v,
      sq_nonneg (Real.sqrt u + Real.sqrt v)]
  have hquad : 0 ≤ u ^ 2 - u * v + v ^ 2 := by
    nlinarith [sq_nonneg (u - v), sq_nonneg u, sq_nonneg v]
  have hfac : 0 ≤ u ^ 2 - u * v - u + v ^ 2 - v + 1 := by
    linarith
  have hid : fullCurvatureCoefficient u v 2 =
      20 * u * v * (u ^ 2 - u * v - u + v ^ 2 - v + 1) *
        (3 * u ^ 3 + 6 * u ^ 2 * v + 6 * u ^ 2 +
          6 * u * v ^ 2 + 11 * u * v + 6 * u + 3 * v ^ 3 +
          6 * v ^ 2 + 6 * v + 3) := by
    norm_num [fullCurvatureCoefficient, varianceCoefficient,
      symmetricProduct, normalizedComplete, splitWeight, splitKappa,
      complete3, diagonal, Finset.sum_range_succ, Nat.choose]
    ring
  rw [hid]
  positivity

theorem fullCurvatureCoefficient_first_three_nonneg_of_root
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1)
    {M : ℕ} (hM : M < 3) :
    0 ≤ fullCurvatureCoefficient u v M := by
  interval_cases M
  · exact fullCurvatureCoefficient_zero_nonneg hu hv
  · exact fullCurvatureCoefficient_one_nonneg_of_root hu hv hroot
  · exact fullCurvatureCoefficient_two_nonneg_of_root hu hv hroot

/-- A generated Bernstein identity supplies any of the remaining compact
coefficients without exposing its rational table to the assembly module. -/
theorem fullCurvatureCoefficient_chart_nonneg_of_bernstein
    {s d : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) {M n : ℕ} {c : ℕ → ℕ → ℝ}
    (hc : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
      0 ≤ c i j)
    (hcert : fullCurvatureCoefficient
        (realRootChartU s d) (realRootChartV s d) M =
      tensorBernstein2 n c (s ^ 2) (d ^ 2)) :
    0 ≤ fullCurvatureCoefficient
      (realRootChartU s d) (realRootChartV s d) M := by
  rw [hcert]
  apply tensorBernstein2_nonneg hc
  · positivity
  · nlinarith [sq_nonneg s, mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  · positivity
  · nlinarith [sq_nonneg d, mul_nonneg hd0 (sub_nonneg.mpr hd1)]

end SSP.K3CyclicRealTail
