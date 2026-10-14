import SSPLean.K3CyclicComplexMiddleSemantics

/-! # Uniform bounds on the complex-middle chart -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

theorem scalar_parameter_bounds
    {rhoValue etaValue : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) :
    0 ≤ scalarZ rhoValue ∧ scalarZ rhoValue ≤ 1 / 3 ∧
    0 ≤ scalarA rhoValue etaValue ∧
    scalarA rhoValue etaValue ≤ 2 / 3 ∧
    scalarZ rhoValue ≤ scalarA rhoValue etaValue ∧
    0 ≤ scalarB rhoValue etaValue ∧
    scalarB rhoValue etaValue ≤ 1 := by
  have hz0 : 0 ≤ scalarZ rhoValue := by
    unfold scalarZ
    nlinarith [mul_self_le_mul_self hrho0 hrho1]
  have hz1 : scalarZ rhoValue ≤ 1 / 3 := by
    unfold scalarZ
    nlinarith [sq_nonneg rhoValue]
  have hA0 : 0 ≤ scalarA rhoValue etaValue := by
    unfold scalarA
    nlinarith [mul_nonneg hrho0 heta0]
  have hetaRho : rhoValue * etaValue ≤ rhoValue := by
    nlinarith [mul_le_mul heta1 hrho1 hrho0 (by norm_num : (0 : ℝ) ≤ 1)]
  have hA1 : scalarA rhoValue etaValue ≤ 2 / 3 := by
    unfold scalarA
    nlinarith
  have hzA : scalarZ rhoValue ≤ scalarA rhoValue etaValue := by
    unfold scalarZ scalarA
    nlinarith [sq_nonneg (1 - rhoValue), mul_nonneg hrho0 heta0]
  have hB0 : 0 ≤ scalarB rhoValue etaValue := by
    unfold scalarB
    linarith
  have hB1 : scalarB rhoValue etaValue ≤ 1 := by
    unfold scalarB
    linarith
  exact ⟨hz0, hz1, hA0, hA1, hzA, hB0, hB1⟩

theorem abs_cosineSign_le_one (n : ℕ) : |(cosineSign n : ℝ)| ≤ 1 := by
  have hmod : n % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases h : n % 4 <;> simp [cosineSign, h]

theorem abs_sineSign_le_one (n : ℕ) : |(sineSign n : ℝ)| ≤ 1 := by
  have hmod : n % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases h : n % 4 <;> simp [sineSign, h]

theorem abs_scalarDerivative_le_three
    {rhoValue etaValue : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) (n : ℕ) :
    |scalarDerivative rhoValue etaValue n| ≤ 3 := by
  obtain ⟨hz0, hz1, hA0, hA1, _hzA, hB0, hB1⟩ :=
    scalar_parameter_bounds hrho0 hrho1 heta0 heta1
  have hzpow (k : ℕ) : scalarZ rhoValue ^ k ≤ 1 := by
    exact pow_le_one₀ hz0 (by linarith)
  have hcos := abs_cosineSign_le_one n
  have hsin := abs_sineSign_le_one n
  unfold scalarDerivative
  calc
    |scalarA rhoValue etaValue *
          (1 - (cosineSign n : ℝ) * scalarZ rhoValue ^ (n / 2)) +
        scalarB rhoValue etaValue *
          ((sineSign n : ℝ) * scalarZ rhoValue ^ ((n - 1) / 2))| ≤
      |scalarA rhoValue etaValue *
          (1 - (cosineSign n : ℝ) * scalarZ rhoValue ^ (n / 2))| +
        |scalarB rhoValue etaValue *
          ((sineSign n : ℝ) * scalarZ rhoValue ^ ((n - 1) / 2))| :=
        abs_add_le _ _
    _ ≤ scalarA rhoValue etaValue * 2 + scalarB rhoValue etaValue := by
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg hA0, abs_of_nonneg hB0,
        abs_of_nonneg (pow_nonneg hz0 ((n - 1) / 2))]
      have hcosProd : |(cosineSign n : ℝ)| *
          scalarZ rhoValue ^ (n / 2) ≤ 1 := by
        nlinarith [mul_le_mul hcos (hzpow (n / 2))
          (pow_nonneg hz0 _) (by norm_num : (0 : ℝ) ≤ 1)]
      have hsinProd : |(sineSign n : ℝ)| *
          scalarZ rhoValue ^ ((n - 1) / 2) ≤ 1 := by
        nlinarith [mul_le_mul hsin (hzpow ((n - 1) / 2))
          (pow_nonneg hz0 _) (by norm_num : (0 : ℝ) ≤ 1)]
      have habsSub : |1 - (cosineSign n : ℝ) *
          scalarZ rhoValue ^ (n / 2)| ≤ 2 := by
        calc
          _ ≤ |(1 : ℝ)| + |(cosineSign n : ℝ) *
              scalarZ rhoValue ^ (n / 2)| := abs_sub _ _
          _ ≤ 2 := by
            rw [abs_mul, abs_one,
              abs_of_nonneg (pow_nonneg hz0 (n / 2))]
            linarith
      nlinarith
    _ ≤ 3 := by linarith

end SSP.K3CyclicComplex.MiddleCoeff
