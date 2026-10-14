import SSPLean.K3CyclicComplexMiddleTailCoefficient

/-! # Exponential generating functions for the complex-middle chart -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

open scoped BigOperators

noncomputable def middleEgfTerm
    (rhoValue etaValue : ℝ) (shift n : ℕ) (x : ℝ) : ℝ :=
  scalarDerivative rhoValue etaValue (n + shift) * x ^ n /
    (Nat.factorial n : ℝ)

noncomputable def middleEgf
    (rhoValue etaValue : ℝ) (shift : ℕ) (x : ℝ) : ℝ :=
  ∑' n, middleEgfTerm rhoValue etaValue shift n x

theorem middleEgfTerm_summable
    {rhoValue etaValue x : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) (shift : ℕ) :
    Summable (fun n => middleEgfTerm rhoValue etaValue shift n x) := by
  have hmajorant : Summable (fun n : ℕ =>
      3 * (|x| ^ n / (Nat.factorial n : ℝ))) :=
    (Real.summable_pow_div_factorial |x|).mul_left 3
  apply hmajorant.of_norm_bounded
  intro n
  have hd := abs_scalarDerivative_le_three
    hrho0 hrho1 heta0 heta1 (n + shift)
  unfold middleEgfTerm
  simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : 0 ≤ (Nat.factorial n : ℝ))]
  rw [show 3 * (|x| ^ n / (Nat.factorial n : ℝ)) =
      (3 * |x| ^ n) / (Nat.factorial n : ℝ) by ring]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right hd (pow_nonneg (abs_nonneg x) _)

noncomputable def middleEgfConvolution
    (rhoValue etaValue : ℝ) (a b : ℕ) (x : ℝ) (M : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (M + 1),
    middleEgfTerm rhoValue etaValue a i x *
      middleEgfTerm rhoValue etaValue b (M - i) x

theorem middleEgfConvolution_summable
    {rhoValue etaValue x : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) (a b : ℕ) :
    Summable (middleEgfConvolution rhoValue etaValue a b x) := by
  have ha := (middleEgfTerm_summable (x := x) hrho0 hrho1 heta0 heta1 a).norm
  have hb := (middleEgfTerm_summable (x := x) hrho0 hrho1 heta0 heta1 b).norm
  exact (summable_norm_sum_mul_range_of_summable_norm ha hb).of_norm

theorem middleEgf_mul_middleEgf
    {rhoValue etaValue x : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) (a b : ℕ) :
    middleEgf rhoValue etaValue a x * middleEgf rhoValue etaValue b x =
      ∑' M, middleEgfConvolution rhoValue etaValue a b x M := by
  have ha := (middleEgfTerm_summable (x := x) hrho0 hrho1 heta0 heta1 a).norm
  have hb := (middleEgfTerm_summable (x := x) hrho0 hrho1 heta0 heta1 b).norm
  simpa only [middleEgf, middleEgfConvolution] using
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm ha hb

noncomputable def middleRecurrenceCurvature
    (rhoValue etaValue x : ℝ) : ℝ :=
  x ^ 2 * (middleEgf rhoValue etaValue 0 x *
      middleEgf rhoValue etaValue 2 x -
    middleEgf rhoValue etaValue 1 x ^ 2) +
    middleEgf rhoValue etaValue 0 x ^ 2

noncomputable def middleRawCurvatureConvolution
    (rhoValue etaValue x : ℝ) (M : ℕ) : ℝ :=
  x ^ 2 * (middleEgfConvolution rhoValue etaValue 0 2 x M -
    middleEgfConvolution rhoValue etaValue 1 1 x M) +
      middleEgfConvolution rhoValue etaValue 0 0 x M

theorem middleRecurrenceCurvature_eq_rawSeries
    {rhoValue etaValue x : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) :
    middleRecurrenceCurvature rhoValue etaValue x =
      ∑' M, middleRawCurvatureConvolution rhoValue etaValue x M := by
  have h02 := middleEgf_mul_middleEgf
    (x := x) hrho0 hrho1 heta0 heta1 0 2
  have h11 := middleEgf_mul_middleEgf
    (x := x) hrho0 hrho1 heta0 heta1 1 1
  have h00 := middleEgf_mul_middleEgf
    (x := x) hrho0 hrho1 heta0 heta1 0 0
  have hs02 := middleEgfConvolution_summable
    (x := x) hrho0 hrho1 heta0 heta1 0 2
  have hs11 := middleEgfConvolution_summable
    (x := x) hrho0 hrho1 heta0 heta1 1 1
  have hs00 := middleEgfConvolution_summable
    (x := x) hrho0 hrho1 heta0 heta1 0 0
  have h11sq : middleEgf rhoValue etaValue 1 x ^ 2 =
      ∑' M, middleEgfConvolution rhoValue etaValue 1 1 x M := by
    rw [pow_two, h11]
  have h00sq : middleEgf rhoValue etaValue 0 x ^ 2 =
      ∑' M, middleEgfConvolution rhoValue etaValue 0 0 x M := by
    rw [pow_two, h00]
  unfold middleRecurrenceCurvature
  rw [h02, h11sq, h00sq]
  simpa only [middleRawCurvatureConvolution] using
    ((((hs02.hasSum.sub hs11.hasSum).mul_left (x ^ 2)).add
      hs00.hasSum).tsum_eq.symm)

end SSP.K3CyclicComplex.MiddleCoeff
