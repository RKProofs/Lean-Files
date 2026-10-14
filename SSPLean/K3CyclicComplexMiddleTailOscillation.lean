import SSPLean.K3CyclicComplexMiddleTailBridge

/-! # Norm bound for the complex-middle oscillatory pair -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

lemma sq_norm_middleAmplitude (A B omega : ℝ) :
    ‖middleAmplitude A B omega‖ ^ 2 =
      (A ^ 2 + (B / omega) ^ 2) / 4 := by
  rw [Complex.sq_norm, Complex.normSq_apply,
    middleAmplitude_re, middleAmplitude_im]
  ring

lemma norm_two_middleFrequency
    {omega : ℝ} (homega : 0 ≤ omega) :
    ‖2 * middleFrequency omega‖ = 2 * omega := by
  unfold middleFrequency
  rw [norm_mul, norm_mul]
  norm_num
  exact homega

lemma norm_oscillatory_term
    {N : ℕ} (hN : 2 ≤ N) {A B omega : ℝ} (homega : 0 < omega) :
    ‖middleAmplitude A B omega ^ 2 *
        (2 * middleFrequency omega) ^ N‖ =
      2 ^ (N - 2) * (A ^ 2 * omega ^ N + B ^ 2 * omega ^ (N - 2)) := by
  rw [norm_mul, norm_pow, norm_pow, sq_norm_middleAmplitude,
    norm_two_middleFrequency homega.le]
  have hN2 : N - 2 + 2 = N := by omega
  have hpowOmega : omega ^ N = omega ^ (N - 2) * omega ^ 2 := by
    rw [← pow_add, hN2]
  have hpowTwo : (2 : ℝ) ^ N = 2 ^ (N - 2) * 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, hN2]
  rw [mul_pow, hpowTwo]
  field_simp [homega.ne']
  rw [hpowOmega]
  ring

lemma omega_le_inv_sqrt_three
    {omega : ℝ} (homega : 0 ≤ omega) (hsq : omega ^ 2 ≤ 1 / 3) :
    omega ≤ 1 / Real.sqrt 3 := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hinv0 : 0 ≤ 1 / Real.sqrt 3 := by positivity
  have hinvSq : (1 / Real.sqrt 3) ^ 2 = (1 / 3 : ℝ) := by
    rw [div_pow, one_pow, hs2]
  nlinarith [sq_nonneg (omega + 1 / Real.sqrt 3)]

lemma inv_sqrt_three_pow_sub_six
    {N : ℕ} (hN : 6 ≤ N) :
    (1 / Real.sqrt 3) ^ (N - 6) =
      27 / Real.sqrt 3 ^ N := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hN6 : N - 6 + 6 = N := by omega
  have hs6 : Real.sqrt 3 ^ 6 = 27 := by
    rw [show 6 = 2 * 3 by norm_num, pow_mul, hs2]
    norm_num
  rw [div_pow, one_pow]
  rw [show Real.sqrt 3 ^ N = Real.sqrt 3 ^ (N - 6) * 27 by
    rw [← hs6, ← pow_add, hN6]]
  field_simp

theorem oscillatory_real_pair_lower
    {N : ℕ} (hN : 6 ≤ N) {A B omega : ℝ}
    (homega : 0 < omega) (hsq : omega ^ 2 ≤ 1 / 3)
    (hA0 : 0 ≤ A) (hzA : omega ^ 2 ≤ A)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    2 * (middleAmplitude A B omega ^ 2 *
        (2 * middleFrequency omega) ^ N).re ≥
      -(A ^ 2 * (2 ^ (N - 1) * 28 / Real.sqrt 3 ^ N)) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hw := omega_le_inv_sqrt_three homega.le hsq
  have hpowN : omega ^ N ≤ (1 / Real.sqrt 3) ^ N :=
    pow_le_pow_left₀ homega.le hw N
  rw [div_pow, one_pow] at hpowN
  have hpow6 : omega ^ (N - 6) ≤ (1 / Real.sqrt 3) ^ (N - 6) :=
    pow_le_pow_left₀ homega.le hw (N - 6)
  rw [inv_sqrt_three_pow_sub_six hN] at hpow6
  have hBsq : B ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - B)]
  have hw4 : omega ^ 4 ≤ A ^ 2 := by
    nlinarith [sq_nonneg (A - omega ^ 2)]
  have hsplit : omega ^ (N - 2) = omega ^ 4 * omega ^ (N - 6) := by
    rw [← pow_add]
    congr 1
    omega
  have hsecond : B ^ 2 * omega ^ (N - 2) ≤
      A ^ 2 * (27 / Real.sqrt 3 ^ N) := by
    rw [hsplit]
    have hp0 : 0 ≤ omega ^ (N - 6) := pow_nonneg homega.le _
    have hi0 : 0 ≤ 27 / Real.sqrt 3 ^ N := by positivity
    have hleft : B ^ 2 * omega ^ 4 ≤ A ^ 2 := by
      calc
        B ^ 2 * omega ^ 4 ≤ 1 * omega ^ 4 :=
          mul_le_mul_of_nonneg_right hBsq (pow_nonneg homega.le _)
        _ ≤ A ^ 2 := by simpa using hw4
    have hright := mul_le_mul hleft hpow6 hp0 (sq_nonneg A)
    simpa [mul_assoc] using hright
  have hfirst : A ^ 2 * omega ^ N ≤
      A ^ 2 * (1 / Real.sqrt 3 ^ N) := by
    exact mul_le_mul_of_nonneg_left hpowN (sq_nonneg A)
  have hnorm := norm_oscillatory_term (N := N) (by omega) (A := A) (B := B) homega
  have hre : |(middleAmplitude A B omega ^ 2 *
      (2 * middleFrequency omega) ^ N).re| ≤
      ‖middleAmplitude A B omega ^ 2 *
        (2 * middleFrequency omega) ^ N‖ := Complex.abs_re_le_norm _
  rw [hnorm] at hre
  have htwo : (2 : ℝ) ^ (N - 1) = 2 * 2 ^ (N - 2) := by
    rw [mul_comm, ← pow_succ]
    congr 1
    omega
  have hlower := (neg_le_of_abs_le hre)
  have hsum : A ^ 2 * omega ^ N + B ^ 2 * omega ^ (N - 2) ≤
      A ^ 2 * (28 / Real.sqrt 3 ^ N) := by
    have hadd := add_le_add hfirst hsecond
    calc
      _ ≤ A ^ 2 * (1 / Real.sqrt 3 ^ N) +
          A ^ 2 * (27 / Real.sqrt 3 ^ N) := hadd
      _ = _ := by ring
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (by positivity : (0 : ℝ) ≤ 2 ^ (N - 2))
  have hlower2 := mul_le_mul_of_nonneg_left hlower (by norm_num : (0 : ℝ) ≤ 2)
  rw [htwo]
  calc
    -(A ^ 2 * (2 * 2 ^ (N - 2) * 28 / Real.sqrt 3 ^ N)) =
        -(2 * (2 ^ (N - 2) * (A ^ 2 * (28 / Real.sqrt 3 ^ N)))) := by ring
    _ ≤ -(2 * (2 ^ (N - 2) *
        (A ^ 2 * omega ^ N + B ^ 2 * omega ^ (N - 2)))) := by
      exact neg_le_neg (mul_le_mul_of_nonneg_left hscaled (by norm_num))
    _ ≤ 2 * (middleAmplitude A B omega ^ 2 *
        (2 * middleFrequency omega) ^ N).re := by
      simpa [mul_assoc] using hlower2

end SSP.K3CyclicComplex.MiddleCoeff
