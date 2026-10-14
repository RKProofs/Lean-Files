import SSPLean.K3CyclicComplexMiddleTailOscillation

/-! # Nonnegativity of all complex-middle coefficients in the analytic tail -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

lemma sqrt_one_add_le_two_div_sqrt_three
    {omega : ℝ} (hsq : omega ^ 2 ≤ 1 / 3) :
    Real.sqrt (1 + omega ^ 2) ≤ 2 / Real.sqrt 3 := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 ≤ Real.sqrt (1 + omega ^ 2) := Real.sqrt_nonneg _
  have hright0 : 0 ≤ 2 / Real.sqrt 3 := by positivity
  have hleftsq : Real.sqrt (1 + omega ^ 2) ^ 2 = 1 + omega ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]
  have hrightsq : (2 / Real.sqrt 3) ^ 2 = 4 / 3 := by
    rw [div_pow, hs2]
    norm_num
  nlinarith [sq_nonneg (Real.sqrt (1 + omega ^ 2) + 2 / Real.sqrt 3)]

theorem scalarCurvatureCoefficient_nonneg_tail
    {N : ℕ} (hN : 25 ≤ N)
    {rhoValue etaValue omega : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1)
    (homega : 0 < omega) (hz : scalarZ rhoValue = omega ^ 2) :
    0 ≤ scalarCurvatureCoefficient rhoValue etaValue N := by
  obtain ⟨hz0, hz1, hA0, _hA1, hzA, hB0, hB1⟩ :=
    scalar_parameter_bounds hrho0 hrho1 heta0 heta1
  let AA := scalarA rhoValue etaValue
  let BB := scalarB rhoValue etaValue
  let rr := Real.sqrt (1 + omega ^ 2)
  have hsq : omega ^ 2 ≤ 1 / 3 := by linarith
  have hzAA : omega ^ 2 ≤ AA := by simpa [AA, hz] using hzA
  have hAA0 : 0 ≤ AA := by simpa [AA] using hA0
  have hBB0 : 0 ≤ BB := by simpa [BB] using hB0
  have hBB1 : BB ≤ 1 := by simpa [BB] using hB1
  have hosc := oscillatory_real_pair_lower (N := N) (by omega)
    (A := AA) (B := BB) homega hsq hAA0 hzAA hBB0 hBB1
  have hR := middleR_re_le (N := N) (by omega) omega
  change (middleR N omega).re ≤ tailM N * rr ^ N at hR
  have hJ := middleJ_taylor_lower (N := N) (by omega) homega
  have herrEq : omega ^ 2 / 6 *
      (1 + (N : ℝ) * ((N : ℝ) - 1) / 2) *
      ((N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2)) *
      Real.sqrt (1 + omega ^ 2) ^ (N - 3) =
      omega ^ 2 / 6 * tailQ N * rr ^ (N - 3) := by
    unfold tailQ tailM rr
    ring
  rw [herrEq] at hJ
  change middleJ N omega ≥
      (N : ℝ) + ((N : ℝ) * ((N : ℝ) - 1) / 2) * ((N : ℝ) - 4) -
        omega ^ 2 / 6 * tailQ N * rr ^ (N - 3) at hJ
  have hJ0 : 0 ≤ (N : ℝ) +
      ((N : ℝ) * ((N : ℝ) - 1) / 2) * ((N : ℝ) - 4) := by
    have hn : (25 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hn0 : 0 ≤ (N : ℝ) := by positivity
    have hn1 : 0 ≤ (N : ℝ) - 1 := by linarith
    have hn4 : 0 ≤ (N : ℝ) - 4 := by linarith
    exact add_nonneg hn0
      (mul_nonneg (div_nonneg (mul_nonneg hn0 hn1) (by norm_num)) hn4)
  have hE0 : 0 ≤ tailQ N * rr ^ (N - 3) := by
    exact mul_nonneg (tailQ_nonneg (by omega)) (pow_nonneg (Real.sqrt_nonneg _) _)
  have hBA : BB * omega ^ 2 ≤ AA := by
    nlinarith [mul_le_mul hBB1 hzAA (sq_nonneg omega) (by norm_num : (0 : ℝ) ≤ 1)]
  have herrcoef : 2 * AA * BB * omega ^ 2 / 6 ≤ AA ^ 2 / 3 := by
    nlinarith
  have herr := mul_le_mul_of_nonneg_right herrcoef hE0
  have hAB0 : 0 ≤ 2 * AA * BB := by positivity
  have hJscaled := mul_le_mul_of_nonneg_left hJ hAB0
  have hJterm : 2 * AA * BB * middleJ N omega ≥
      -(AA ^ 2 * ((1 / 3 : ℝ) * tailQ N * rr ^ (N - 3))) := by
    nlinarith
  have hRterm : -2 * AA ^ 2 * (middleR N omega).re ≥
      -(AA ^ 2 * (2 * tailM N * rr ^ N)) := by
    have hs := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 2 * AA ^ 2)
    nlinarith
  have hpair := scalarCurvatureCoefficient_pairing
    (rhoValue := rhoValue) (etaValue := etaValue) (omega := omega)
    (N := N) (by omega) homega.ne' hz
  change scalarCurvatureCoefficient rhoValue etaValue N =
      AA ^ 2 * 2 ^ N +
      2 * (middleAmplitude AA BB omega ^ 2 *
        (2 * middleFrequency omega) ^ N).re -
      2 * AA ^ 2 * (middleR N omega).re +
      2 * AA * BB * middleJ N omega at hpair
  have hlower : scalarCurvatureCoefficient rhoValue etaValue N ≥
      AA ^ 2 * ((2 : ℝ) ^ N -
        2 * tailM N * rr ^ N -
        (1 / 3 : ℝ) * tailQ N * rr ^ (N - 3) -
        2 ^ (N - 1) * 28 / Real.sqrt 3 ^ N) := by
    rw [hpair]
    nlinarith
  have hrr : rr ≤ 2 / Real.sqrt 3 := by
    exact sqrt_one_add_le_two_div_sqrt_three hsq
  have hr0 : 0 ≤ rr := Real.sqrt_nonneg _
  have hpN := pow_le_pow_left₀ hr0 hrr N
  have hpN3 := pow_le_pow_left₀ hr0 hrr (N - 3)
  have hM0 : 0 ≤ tailM N := by
    unfold tailM
    have hn : (25 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hn0 : 0 ≤ (N : ℝ) := by positivity
    have hn1 : 0 ≤ (N : ℝ) - 1 := by linarith
    exact add_nonneg (by norm_num)
      (div_nonneg (mul_nonneg hn0 hn1) (by norm_num))
  have hQ0 := tailQ_nonneg (by omega : 2 ≤ N)
  have hbrace := tail_analytic_brace_pos hN
  have hactual : 0 < (2 : ℝ) ^ N -
      2 * tailM N * rr ^ N -
      (1 / 3 : ℝ) * tailQ N * rr ^ (N - 3) -
      2 ^ (N - 1) * 28 / Real.sqrt 3 ^ N := by
    have hcM : 0 ≤ 2 * tailM N := mul_nonneg (by norm_num) hM0
    have hcQ : 0 ≤ (1 / 3 : ℝ) * tailQ N :=
      mul_nonneg (by norm_num) hQ0
    have hMN := mul_le_mul_of_nonneg_left hpN hcM
    have hQN := mul_le_mul_of_nonneg_left hpN3
      hcQ
    linarith
  exact (mul_nonneg (sq_nonneg AA) hactual.le).trans hlower

theorem scalarCurvatureCoefficient_nonneg_of_scalarZ_pos
    {N : ℕ} (hN : 4 ≤ N)
    {rhoValue etaValue : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1)
    (hzpos : 0 < scalarZ rhoValue) :
    0 ≤ scalarCurvatureCoefficient rhoValue etaValue N := by
  by_cases hN24 : N ≤ 24
  · exact scalarCurvatureCoefficient_nonneg_through_twenty_four
      hN hN24 hrho0 hrho1 heta0 heta1
  · have hN25 : 25 ≤ N := by omega
    let omega := Real.sqrt (scalarZ rhoValue)
    have homega : 0 < omega := Real.sqrt_pos.2 hzpos
    have hz : scalarZ rhoValue = omega ^ 2 := by
      dsimp [omega]
      rw [Real.sq_sqrt hzpos.le]
    exact scalarCurvatureCoefficient_nonneg_tail hN25
      hrho0 hrho1 heta0 heta1 homega hz

@[simp] lemma scalarZ_one : scalarZ 1 = 0 := by
  norm_num [scalarZ]

lemma scalarDerivative_one_zero (etaValue : ℝ) :
    scalarDerivative 1 etaValue 0 = 0 := by
  norm_num [scalarDerivative, cosineSign, sineSign]

lemma scalarDerivative_one_one (etaValue : ℝ) :
    scalarDerivative 1 etaValue 1 = 1 := by
  norm_num [scalarDerivative, cosineSign, sineSign, scalarB]

lemma scalarDerivative_one_ge_two
    (etaValue : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    scalarDerivative 1 etaValue n = scalarA 1 etaValue := by
  by_cases hn2 : n = 2
  · subst n
    norm_num [scalarDerivative, cosineSign, sineSign]
  · have hn3 : 3 ≤ n := by omega
    have hhalf : n / 2 ≠ 0 := by omega
    have hhalf' : (n - 1) / 2 ≠ 0 := by omega
    simp [scalarDerivative, hhalf, hhalf']

noncomputable def boundaryCorrection (A : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then -A else if n = 1 then 1 - A else 0

lemma scalarDerivative_one_eq_correction (etaValue : ℝ) (n : ℕ) :
    scalarDerivative 1 etaValue n =
      scalarA 1 etaValue + boundaryCorrection (scalarA 1 etaValue) n := by
  by_cases h0 : n = 0
  · subst n
    simp [boundaryCorrection, scalarDerivative_one_zero]
  by_cases h1 : n = 1
  · subst n
    simp [boundaryCorrection, scalarDerivative_one_one]
  · have hn : 2 ≤ n := by omega
    rw [scalarDerivative_one_ge_two etaValue hn]
    simp [boundaryCorrection, h0, h1]

lemma sum_kernel_real (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), (kernel N j : ℝ)) = (2 : ℝ) ^ N := by
  have h := kernel_geometric_pairing N (1 : ℂ) 1
  norm_num at h
  exact_mod_cast h

lemma sum_kernel_mul_boundaryCorrection
    {N : ℕ} (hN : 1 ≤ N) (A : ℝ) :
    (∑ j ∈ Finset.range (N + 1),
      (kernel N j : ℝ) * boundaryCorrection A j) =
      (kernel N 0 : ℝ) * (-A) + (kernel N 1 : ℝ) * (1 - A) := by
  have hc (j : ℕ) : boundaryCorrection A j =
      (if j = 0 then -A else 0) + (if j = 1 then 1 - A else 0) := by
    by_cases h0 : j = 0
    · subst j
      simp [boundaryCorrection]
    by_cases h1 : j = 1
    · subst j
      simp [boundaryCorrection]
    · simp [boundaryCorrection, h0, h1]
  simp_rw [hc, mul_add]
  rw [Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq']
  have h0mem : 0 ∈ Finset.range (N + 1) := by simp
  have h1mem : 1 ∈ Finset.range (N + 1) := by
    exact Finset.mem_range.mpr (by omega)
  rw [if_pos h0mem, if_pos h1mem]

lemma kernel_last_eq_first (N : ℕ) : kernel N N = kernel N 0 := by
  unfold kernel
  simp
  ring

lemma kernel_penultimate_eq_second
    {N : ℕ} (hN : 1 ≤ N) : kernel N (N - 1) = kernel N 1 := by
  unfold kernel
  rw [Nat.choose_symm hN]
  have hsub : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
  rw [hsub]
  ring

lemma sum_kernel_mul_boundaryCorrection_reverse
    {N : ℕ} (hN : 1 ≤ N) (A : ℝ) :
    (∑ j ∈ Finset.range (N + 1),
      (kernel N j : ℝ) * boundaryCorrection A (N - j)) =
      (kernel N 0 : ℝ) * (-A) + (kernel N 1 : ℝ) * (1 - A) := by
  calc
    (∑ j ∈ Finset.range (N + 1),
      (kernel N j : ℝ) * boundaryCorrection A (N - j)) =
        ∑ j ∈ Finset.range (N + 1),
          (kernel N j : ℝ) *
            ((if j = N then -A else 0) +
              (if j = N - 1 then 1 - A else 0)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjN : j ≤ N := by
        have := Finset.mem_range.mp hj
        omega
      have hzero : N - j = 0 ↔ j = N := by omega
      have hone : N - j = 1 ↔ j = N - 1 := by omega
      simp [boundaryCorrection, hzero, hone]
      split_ifs <;> simp_all [mul_neg]
    _ = (kernel N N : ℝ) * (-A) +
        (kernel N (N - 1) : ℝ) * (1 - A) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq']
      have hNmem : N ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
      have hNm1mem : N - 1 ∈ Finset.range (N + 1) :=
        Finset.mem_range.mpr (by omega)
      rw [if_pos hNmem, if_pos hNm1mem]
    _ = _ := by rw [kernel_last_eq_first, kernel_penultimate_eq_second hN]

lemma boundaryCorrection_product_zero
    {N j : ℕ} (hN : 4 ≤ N) (A : ℝ) :
    boundaryCorrection A j * boundaryCorrection A (N - j) = 0 := by
  by_cases h0 : j = 0
  · subst j
    have hN0 : N ≠ 0 := by omega
    have hN1 : N ≠ 1 := by omega
    simp [boundaryCorrection, hN0, hN1]
  by_cases h1 : j = 1
  · subst j
    have hNm10 : N - 1 ≠ 0 := by omega
    have hNm11 : N - 1 ≠ 1 := by omega
    simp [boundaryCorrection, hNm10, hNm11]
  · simp [boundaryCorrection, h0, h1]

lemma scalarCurvatureCoefficient_one_formula
    {N : ℕ} (hN : 4 ≤ N) (etaValue : ℝ) :
    scalarCurvatureCoefficient 1 etaValue N =
      scalarA 1 etaValue ^ 2 * (2 : ℝ) ^ N +
        2 * scalarA 1 etaValue *
          ((kernel N 0 : ℝ) * (-scalarA 1 etaValue) +
            (kernel N 1 : ℝ) * (1 - scalarA 1 etaValue)) := by
  let AA := scalarA 1 etaValue
  have hpoint (j : ℕ) :
      (kernel N j : ℝ) * scalarDerivative 1 etaValue j *
          scalarDerivative 1 etaValue (N - j) =
        (kernel N j : ℝ) * AA ^ 2 +
          AA * ((kernel N j : ℝ) * boundaryCorrection AA j) +
          AA * ((kernel N j : ℝ) * boundaryCorrection AA (N - j)) +
          (kernel N j : ℝ) *
            (boundaryCorrection AA j * boundaryCorrection AA (N - j)) := by
    rw [scalarDerivative_one_eq_correction,
      scalarDerivative_one_eq_correction]
    dsimp [AA]
    ring
  unfold scalarCurvatureCoefficient
  simp_rw [hpoint, boundaryCorrection_product_zero hN, mul_zero]
  simp_rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  rw [sum_kernel_real,
    sum_kernel_mul_boundaryCorrection (by omega) AA,
    sum_kernel_mul_boundaryCorrection_reverse (by omega) AA]
  dsimp [AA]
  simp
  ring

lemma kernel_zero_real {N : ℕ} (hN : 2 ≤ N) :
    (kernel N 0 : ℝ) =
      ((N : ℝ) * ((N : ℝ) - 1) + 2) / 2 := by
  unfold kernel
  simp
  push_cast
  ring

lemma kernel_one_real {N : ℕ} (hN : 3 ≤ N) :
    (kernel N 1 : ℝ) =
      (N : ℝ) * ((N : ℝ) - 2) * ((N : ℝ) - 3) / 2 := by
  unfold kernel
  simp [Nat.choose_one_right]
  push_cast
  ring

lemma quadratic_le_two_pow {N : ℕ} (hN : 4 ≤ N) :
    (N : ℝ) * ((N : ℝ) - 1) + 2 ≤ (2 : ℝ) ^ N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show 4 + (k + 1) = (4 + k) + 1 by omega, pow_succ]
      push_cast
      have ih' := ih (by omega : 4 ≤ 4 + k)
      have hk : (4 : ℝ) ≤ (4 + k : ℕ) := by exact_mod_cast (by omega : 4 ≤ 4 + k)
      have hk1 : 0 ≤ ((4 + k : ℕ) : ℝ) - 1 := by linarith
      have hk2 : 0 ≤ ((4 + k : ℕ) : ℝ) - 2 := by linarith
      have hprod : 0 ≤ (((4 + k : ℕ) : ℝ) - 1) *
          (((4 + k : ℕ) : ℝ) - 2) := mul_nonneg hk1 hk2
      have hstep : (((4 + k : ℕ) : ℝ) + 1) * ((4 + k : ℕ) : ℝ) + 2 ≤
          2 * (((4 + k : ℕ) : ℝ) * (((4 + k : ℕ) : ℝ) - 1) + 2) := by
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left ih' (by norm_num : (0 : ℝ) ≤ 2)
      norm_num at hmul ⊢
      nlinarith

theorem scalarCurvatureCoefficient_one_nonneg
    {N : ℕ} (hN : 4 ≤ N) {etaValue : ℝ}
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) :
    0 ≤ scalarCurvatureCoefficient 1 etaValue N := by
  rw [scalarCurvatureCoefficient_one_formula hN,
    kernel_zero_real (by omega), kernel_one_real (by omega)]
  have hA0 : 0 ≤ scalarA 1 etaValue := by
    unfold scalarA
    linarith
  have hA1 : scalarA 1 etaValue ≤ 1 := by
    unfold scalarA
    linarith
  have hk0 : 0 ≤ (N : ℝ) * ((N : ℝ) - 2) * ((N : ℝ) - 3) / 2 := by
    have hn : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hn0 : 0 ≤ (N : ℝ) := by positivity
    have hn2 : 0 ≤ (N : ℝ) - 2 := by linarith
    have hn3 : 0 ≤ (N : ℝ) - 3 := by linarith
    positivity
  have hpow := quadratic_le_two_pow hN
  nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hA1)]

theorem scalarCurvatureCoefficient_nonneg_all
    {N : ℕ} (hN : 4 ≤ N)
    {rhoValue etaValue : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) :
    0 ≤ scalarCurvatureCoefficient rhoValue etaValue N := by
  obtain ⟨hz0, _hz1, _hA0, _hA1, _hzA, _hB0, _hB1⟩ :=
    scalar_parameter_bounds hrho0 hrho1 heta0 heta1
  rcases hz0.eq_or_lt with hz | hz
  · have hrho : rhoValue = 1 := by
      unfold scalarZ at hz
      nlinarith [sq_nonneg (rhoValue - 1)]
    subst rhoValue
    exact scalarCurvatureCoefficient_one_nonneg hN heta0 heta1
  · exact scalarCurvatureCoefficient_nonneg_of_scalarZ_pos hN
      hrho0 hrho1 heta0 heta1 hz

end SSP.K3CyclicComplex.MiddleCoeff
