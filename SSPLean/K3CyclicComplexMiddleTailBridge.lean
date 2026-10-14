import SSPLean.K3CyclicComplexMiddleJBound

/-! # Converting the numerical tail certificate to the analytic brace -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

lemma tail_subtractions_normalized
    {N : ℕ} (hN : 25 ≤ N) :
    (2 * tailM N * (2 / Real.sqrt 3) ^ N +
        (1 / 3 : ℝ) * tailQ N * (2 / Real.sqrt 3) ^ (N - 3) +
        2 ^ (N - 1) * 28 / Real.sqrt 3 ^ N) /
        2 ^ N = tailP N / Real.sqrt 3 ^ N := by
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hN1 : N - 1 + 1 = N := by omega
  have hN3 : N - 3 + 3 = N := by omega
  have htwo : (2 : ℝ) ^ N = 2 ^ (N - 1) * 2 := by
    rw [← pow_succ, hN1]
  have hN13 : N - 3 + 2 = N - 1 := by omega
  have htwo13 : (2 : ℝ) ^ (N - 1) = 2 ^ (N - 3) * 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, hN13]
  have hs3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    rw [show 3 = 2 + 1 by norm_num, pow_add, hs2]
    ring
  have hsN3 : Real.sqrt 3 ^ N =
      Real.sqrt 3 ^ (N - 3) * (3 * Real.sqrt 3) := by
    rw [← hs3, ← pow_add, hN3]
  rw [div_pow]
  rw [show (2 / Real.sqrt 3) ^ (N - 3) =
      2 ^ (N - 3) / Real.sqrt 3 ^ (N - 3) by rw [div_pow]]
  unfold tailP tailA tailQ tailM
  rw [htwo, htwo13, hsN3]
  field_simp
  norm_num
  ring

theorem tail_analytic_brace_pos {N : ℕ} (hN : 25 ≤ N) :
    0 < (2 : ℝ) ^ N -
      2 * tailM N * (2 / Real.sqrt 3) ^ N -
      (1 / 3 : ℝ) * tailQ N * (2 / Real.sqrt 3) ^ (N - 3) -
      2 ^ (N - 1) * 28 / Real.sqrt 3 ^ N := by
  have hnum := tailP_lt_sqrt_three_pow hN
  have hsN : 0 < Real.sqrt 3 ^ N := pow_pos (Real.sqrt_pos.2 (by norm_num)) _
  have htwoN : 0 < (2 : ℝ) ^ N := by positivity
  have hratio : tailP N / Real.sqrt 3 ^ N < 1 :=
    (div_lt_one hsN).2 hnum
  rw [← tail_subtractions_normalized hN] at hratio
  have this := (div_lt_one htwoN).mp hratio
  linarith

lemma norm_oppositeProduct
    {N : ℕ} (hN : 2 ≤ N) (omega : ℝ) :
    ‖oppositeProduct N omega‖ =
      Real.sqrt (1 + omega ^ 2) ^ N := by
  unfold oppositeProduct
  rw [norm_mul, norm_affinePower_negI_two, norm_affinePower_I]
  let r := Real.sqrt (1 + omega ^ 2)
  change (1 + omega ^ 2) * r ^ (N - 2) = r ^ N
  have hr2 : r ^ 2 = 1 + omega ^ 2 := by
    dsimp [r]
    rw [Real.sq_sqrt (by positivity)]
  rw [← hr2, ← pow_add]
  congr 1
  omega

lemma norm_middleR_le
    {N : ℕ} (hN : 2 ≤ N) (omega : ℝ) :
    ‖middleR N omega‖ ≤
      tailM N * Real.sqrt (1 + omega ^ 2) ^ N := by
  rw [middleR_eq_affine_products]
  calc
    ‖affinePower Complex.I N omega +
        (((N : ℝ) * ((N : ℝ) - 1) / 2 : ℝ) : ℂ) *
          oppositeProduct N omega‖ ≤
      ‖affinePower Complex.I N omega‖ +
        ‖(((N : ℝ) * ((N : ℝ) - 1) / 2 : ℝ) : ℂ) *
          oppositeProduct N omega‖ := norm_add_le _ _
    _ = tailM N * Real.sqrt (1 + omega ^ 2) ^ N := by
      rw [norm_affinePower_I, norm_mul, norm_oppositeProduct hN]
      have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hn0 : 0 ≤ (N : ℝ) := by positivity
      have hn1 : 0 ≤ (N : ℝ) - 1 := by linarith
      have hm : 0 ≤ (N : ℝ) * ((N : ℝ) - 1) / 2 :=
        div_nonneg (mul_nonneg hn0 hn1) (by norm_num)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm]
      unfold tailM
      ring

lemma middleR_re_le
    {N : ℕ} (hN : 2 ≤ N) (omega : ℝ) :
    (middleR N omega).re ≤
      tailM N * Real.sqrt (1 + omega ^ 2) ^ N := by
  exact (Complex.re_le_norm _).trans (norm_middleR_le hN omega)

end SSP.K3CyclicComplex.MiddleCoeff
