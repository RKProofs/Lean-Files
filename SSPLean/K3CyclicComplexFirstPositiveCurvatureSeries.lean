import SSPLean.K3CyclicComplexFirstPositiveSeries

/-! # Curvature Cauchy products for the positive complex-first chart -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.PositiveCoeff

open scoped BigOperators

noncomputable def egfConvolution
    (r τ : ℝ) (a b : ℕ) (x : ℝ) (M : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (M + 1),
    egfTerm r τ a i x * egfTerm r τ b (M - i) x

theorem egfConvolution_summable
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (a b : ℕ) :
    Summable (egfConvolution r τ a b x) := by
  have ha := (egfTerm_summable (x := x) hr0 hr1 hτ0 hτ1 a).norm
  have hb := (egfTerm_summable (x := x) hr0 hr1 hτ0 hτ1 b).norm
  exact (summable_norm_sum_mul_range_of_summable_norm ha hb).of_norm

theorem egf_tsum_mul_tsum
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (a b : ℕ) :
    (∑' n, egfTerm r τ a n x) * (∑' n, egfTerm r τ b n x) =
      ∑' M, egfConvolution r τ a b x M := by
  have ha := (egfTerm_summable (x := x) hr0 hr1 hτ0 hτ1 a).norm
  have hb := (egfTerm_summable (x := x) hr0 hr1 hτ0 hτ1 b).norm
  simpa only [egfConvolution] using
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm ha hb

noncomputable def recurrenceCurvature (r τ x : ℝ) : ℝ :=
  x ^ 2 * (recurrenceF r τ x * recurrenceF2 r τ x -
    recurrenceF1 r τ x ^ 2) + 2 * recurrenceF r τ x ^ 2

noncomputable def rawCurvatureConvolution (r τ x : ℝ) (M : ℕ) : ℝ :=
  x ^ 2 * (egfConvolution r τ 0 2 x M -
    egfConvolution r τ 1 1 x M) +
      2 * egfConvolution r τ 0 0 x M

theorem rawCurvatureConvolution_summable
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    Summable (rawCurvatureConvolution r τ x) := by
  exact (((egfConvolution_summable hr0 hr1 hτ0 hτ1 0 2).sub
    (egfConvolution_summable hr0 hr1 hτ0 hτ1 1 1)).mul_left (x ^ 2)).add
      ((egfConvolution_summable hr0 hr1 hτ0 hτ1 0 0).mul_left 2)

theorem recurrenceCurvature_eq_rawSeries
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    recurrenceCurvature r τ x =
      ∑' M, rawCurvatureConvolution r τ x M := by
  have h02 := egf_tsum_mul_tsum (x := x) hr0 hr1 hτ0 hτ1 0 2
  have h11 := egf_tsum_mul_tsum (x := x) hr0 hr1 hτ0 hτ1 1 1
  have h00 := egf_tsum_mul_tsum (x := x) hr0 hr1 hτ0 hτ1 0 0
  have hs02 := egfConvolution_summable (x := x) hr0 hr1 hτ0 hτ1 0 2
  have hs11 := egfConvolution_summable (x := x) hr0 hr1 hτ0 hτ1 1 1
  have hs00 := egfConvolution_summable (x := x) hr0 hr1 hτ0 hτ1 0 0
  have h11sq : (∑' n, egfTerm r τ 1 n x) ^ 2 =
      ∑' M, egfConvolution r τ 1 1 x M := by rw [pow_two, h11]
  have h00sq : (∑' n, egfTerm r τ 0 n x) ^ 2 =
      ∑' M, egfConvolution r τ 0 0 x M := by rw [pow_two, h00]
  unfold recurrenceCurvature
  rw [recurrenceF_eq_egf hr0 hr1 hτ0 hτ1,
    recurrenceF1_eq_egf hr0 hr1 hτ0 hτ1,
    recurrenceF2_eq_egf hr0 hr1 hτ0 hτ1,
    h02, h11sq, h00sq]
  simpa only [rawCurvatureConvolution] using
    ((((hs02.hasSum.sub hs11.hasSum).mul_left (x ^ 2)).add
      (hs00.hasSum.mul_left 2)).tsum_eq.symm)

theorem egfTerm_mul_complement
    (r τ x : ℝ) {M i : ℕ} (hi : i ≤ M) (a b : ℕ) :
    egfTerm r τ a i x * egfTerm r τ b (M - i) x =
      (Nat.choose M i : ℝ) * scalarDerivative r τ (i + a) *
        scalarDerivative r τ (M - i + b) * x ^ M /
          (Nat.factorial M : ℝ) := by
  unfold egfTerm
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial hi
  have hchoose :
      (Nat.choose M i : ℝ) * (Nat.factorial i : ℝ) *
          (Nat.factorial (M - i) : ℝ) = (Nat.factorial M : ℝ) := by
    exact_mod_cast hchooseNat
  have hchooseNe : (Nat.choose M i : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hi).ne'
  have hpow : x ^ i * x ^ (M - i) = x ^ M := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  rw [← hchoose, ← hpow]
  field_simp [hchooseNe]

theorem egfConvolution_eq
    (r τ x : ℝ) (a b M : ℕ) :
    egfConvolution r τ a b x M =
      ∑ i ∈ Finset.range (M + 1),
        (Nat.choose M i : ℝ) * scalarDerivative r τ (i + a) *
          scalarDerivative r τ (M - i + b) * x ^ M /
            (Nat.factorial M : ℝ) := by
  unfold egfConvolution
  apply Finset.sum_congr rfl
  intro i hi
  exact egfTerm_mul_complement r τ x
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) a b

noncomputable def nonsymmetricKernelWeight (N j : ℕ) : ℝ :=
  (Nat.choose N j : ℝ) *
    (2 + ((N : ℝ) - j) * ((N : ℝ) - 2 * j - 1))

/-- Symmetrizing the coefficient of `F * F'' - (F')²` gives exactly the
integer kernel used by the executable certificate. -/
theorem average_nonsymmetricKernelWeight_eq
    {N j : ℕ} (hj : j ≤ N) :
    (nonsymmetricKernelWeight N j +
      nonsymmetricKernelWeight N (N - j)) / 2 =
        (ComplexCoeff.kernel N j : ℝ) := by
  unfold nonsymmetricKernelWeight ComplexCoeff.kernel
  rw [Nat.choose_symm hj]
  push_cast [Nat.cast_sub hj]
  ring

theorem nonsymmetricKernel_sum_eq_scalarCurvatureCoefficient
    (d : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1),
      nonsymmetricKernelWeight N j * d j * d (N - j)) =
        SSP.K3CyclicComplex.scalarCurvatureCoefficient d N := by
  let f : ℕ → ℝ := fun j =>
    nonsymmetricKernelWeight N j * d j * d (N - j)
  have href0 := Finset.sum_range_reflect f (N + 1)
  have href :
      (∑ j ∈ Finset.range (N + 1),
        nonsymmetricKernelWeight N (N - j) * d j * d (N - j)) =
      ∑ j ∈ Finset.range (N + 1),
        nonsymmetricKernelWeight N j * d j * d (N - j) := by
    rw [← href0]
    apply Finset.sum_congr rfl
    intro j hjmem
    have hj : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hjmem)
    dsimp [f]
    rw [Nat.sub_sub_self hj]
    ring
  unfold SSP.K3CyclicComplex.scalarCurvatureCoefficient
  calc
    (∑ j ∈ Finset.range (N + 1),
        nonsymmetricKernelWeight N j * d j * d (N - j)) =
        ((∑ j ∈ Finset.range (N + 1),
            nonsymmetricKernelWeight N j * d j * d (N - j)) +
          ∑ j ∈ Finset.range (N + 1),
            nonsymmetricKernelWeight N (N - j) * d j * d (N - j)) / 2 := by
      rw [href]
      ring
    _ = ∑ j ∈ Finset.range (N + 1),
        ((nonsymmetricKernelWeight N j +
          nonsymmetricKernelWeight N (N - j)) / 2) * d j * d (N - j) := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ j ∈ Finset.range (N + 1),
        (ComplexCoeff.kernel N j : ℝ) * d j * d (N - j) := by
      apply Finset.sum_congr rfl
      intro j hjmem
      rw [average_nonsymmetricKernelWeight_eq
        (Nat.le_of_lt_succ (Finset.mem_range.mp hjmem))]

theorem choose_two_step_right_factorial {M i : ℕ} (hi : i ≤ M) :
    (Nat.choose (M + 2) i : ℝ) * (((M + 2 : ℕ) : ℝ) - (i : ℝ)) *
        (((M + 2 : ℕ) : ℝ) - (i : ℝ) - 1) /
          (Nat.factorial (M + 2) : ℝ) =
      1 / ((Nat.factorial i : ℝ) * (Nat.factorial (M - i) : ℝ)) := by
  have hiN : i ≤ M + 2 := by omega
  have hsub : M + 2 - i = (M - i) + 2 := by omega
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial hiN
  have hchoose :
      (Nat.choose (M + 2) i : ℝ) * (Nat.factorial i : ℝ) *
          (Nat.factorial (M + 2 - i) : ℝ) =
        (Nat.factorial (M + 2) : ℝ) := by exact_mod_cast hchooseNat
  have hchooseNe : (Nat.choose (M + 2) i : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hiN).ne'
  rw [← hchoose]
  push_cast [Nat.cast_sub hiN, Nat.cast_sub hi]
  rw [hsub, Nat.factorial_succ, Nat.factorial_succ]
  field_simp [hchooseNe]
  push_cast [Nat.cast_sub hi]
  ring

theorem choose_one_step_each_factorial {M i : ℕ} (hi : i ≤ M) :
    (Nat.choose (M + 2) (i + 1) : ℝ) * ((i + 1 : ℕ) : ℝ) *
        (((M + 2 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) /
          (Nat.factorial (M + 2) : ℝ) =
      1 / ((Nat.factorial i : ℝ) * (Nat.factorial (M - i) : ℝ)) := by
  have hiN : i + 1 ≤ M + 2 := by omega
  have hsub : M + 2 - (i + 1) = (M - i) + 1 := by omega
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial hiN
  have hchoose :
      (Nat.choose (M + 2) (i + 1) : ℝ) *
          (Nat.factorial (i + 1) : ℝ) *
          (Nat.factorial (M + 2 - (i + 1)) : ℝ) =
        (Nat.factorial (M + 2) : ℝ) := by exact_mod_cast hchooseNat
  have hchooseNe : (Nat.choose (M + 2) (i + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hiN).ne'
  rw [← hchoose]
  rw [hsub]
  push_cast [Nat.cast_sub hiN, Nat.cast_sub hi]
  rw [Nat.factorial_succ, Nat.factorial_succ]
  field_simp [hchooseNe]
  push_cast [Nat.cast_sub hi]
  ring

noncomputable def secondRightTerm
    (r τ x : ℝ) (N j : ℕ) : ℝ :=
  (Nat.choose N j : ℝ) * ((N : ℝ) - j) * ((N : ℝ) - j - 1) *
    scalarDerivative r τ j * scalarDerivative r τ (N - j) * x ^ N /
      (Nat.factorial N : ℝ)

noncomputable def firstSquareTerm
    (r τ x : ℝ) (N j : ℕ) : ℝ :=
  (Nat.choose N j : ℝ) * (j : ℝ) * ((N : ℝ) - j) *
    scalarDerivative r τ j * scalarDerivative r τ (N - j) * x ^ N /
      (Nat.factorial N : ℝ)

theorem choose_factorial_ratio {M i : ℕ} (hi : i ≤ M) :
    (Nat.choose M i : ℝ) / (Nat.factorial M : ℝ) =
      1 / ((Nat.factorial i : ℝ) * (Nat.factorial (M - i) : ℝ)) := by
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial hi
  have hchoose :
      (Nat.choose M i : ℝ) * (Nat.factorial i : ℝ) *
          (Nat.factorial (M - i) : ℝ) = (Nat.factorial M : ℝ) := by
    exact_mod_cast hchooseNat
  have hchooseNe : (Nat.choose M i : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hi).ne'
  rw [← hchoose]
  field_simp [hchooseNe]

theorem secondRightTerm_eq_shifted_egf
    (r τ x : ℝ) {M i : ℕ} (hi : i ≤ M) :
    secondRightTerm r τ x (M + 2) i =
      x ^ 2 * (egfTerm r τ 0 i x * egfTerm r τ 2 (M - i) x) := by
  have hsub : M + 2 - i = M - i + 2 := by omega
  have hcoeff :
      (Nat.choose (M + 2) i : ℝ) * (((M + 2 : ℕ) : ℝ) - i) *
          (((M + 2 : ℕ) : ℝ) - i - 1) /
            (Nat.factorial (M + 2) : ℝ) =
        (Nat.choose M i : ℝ) / (Nat.factorial M : ℝ) := by
    rw [choose_two_step_right_factorial hi, choose_factorial_ratio hi]
  rw [egfTerm_mul_complement r τ x hi 0 2]
  simp only [Nat.add_zero]
  calc
    secondRightTerm r τ x (M + 2) i =
        ((Nat.choose (M + 2) i : ℝ) * (((M + 2 : ℕ) : ℝ) - i) *
          (((M + 2 : ℕ) : ℝ) - i - 1) /
            (Nat.factorial (M + 2) : ℝ)) *
          (scalarDerivative r τ i * scalarDerivative r τ (M - i + 2) *
            x ^ (M + 2)) := by unfold secondRightTerm; rw [hsub]; ring
    _ = ((Nat.choose M i : ℝ) / (Nat.factorial M : ℝ)) *
          (scalarDerivative r τ i * scalarDerivative r τ (M - i + 2) *
            x ^ (M + 2)) := by rw [hcoeff]
    _ = x ^ 2 *
        ((Nat.choose M i : ℝ) * scalarDerivative r τ i *
          scalarDerivative r τ (M - i + 2) * x ^ M /
            (Nat.factorial M : ℝ)) := by
      rw [show x ^ (M + 2) = x ^ 2 * x ^ M by rw [pow_add, mul_comm]]
      ring

theorem firstSquareTerm_eq_shifted_egf
    (r τ x : ℝ) {M i : ℕ} (hi : i ≤ M) :
    firstSquareTerm r τ x (M + 2) (i + 1) =
      x ^ 2 * (egfTerm r τ 1 i x * egfTerm r τ 1 (M - i) x) := by
  have hsub : M + 2 - (i + 1) = M - i + 1 := by omega
  have hcoeff :
      (Nat.choose (M + 2) (i + 1) : ℝ) * ((i + 1 : ℕ) : ℝ) *
          (((M + 2 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) /
            (Nat.factorial (M + 2) : ℝ) =
        (Nat.choose M i : ℝ) / (Nat.factorial M : ℝ) := by
    rw [choose_one_step_each_factorial hi, choose_factorial_ratio hi]
  rw [egfTerm_mul_complement r τ x hi 1 1]
  calc
    firstSquareTerm r τ x (M + 2) (i + 1) =
        ((Nat.choose (M + 2) (i + 1) : ℝ) * ((i + 1 : ℕ) : ℝ) *
          (((M + 2 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) /
            (Nat.factorial (M + 2) : ℝ)) *
          (scalarDerivative r τ (i + 1) *
            scalarDerivative r τ (M - i + 1) * x ^ (M + 2)) := by
      unfold firstSquareTerm
      rw [hsub]
      ring
    _ = ((Nat.choose M i : ℝ) / (Nat.factorial M : ℝ)) *
          (scalarDerivative r τ (i + 1) *
            scalarDerivative r τ (M - i + 1) * x ^ (M + 2)) := by rw [hcoeff]
    _ = x ^ 2 *
        ((Nat.choose M i : ℝ) * scalarDerivative r τ (i + 1) *
          scalarDerivative r τ (M - i + 1) * x ^ M /
            (Nat.factorial M : ℝ)) := by
      rw [show x ^ (M + 2) = x ^ 2 * x ^ M by rw [pow_add, mul_comm]]
      ring

theorem sum_secondRightTerm_eq_convolution
    (r τ x : ℝ) (M : ℕ) :
    (∑ j ∈ Finset.range (M + 2 + 1), secondRightTerm r τ x (M + 2) j) =
      x ^ 2 * egfConvolution r τ 0 2 x M := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hlast : secondRightTerm r τ x (M + 2) (M + 2) = 0 := by
    unfold secondRightTerm
    norm_num
  have hpenult : secondRightTerm r τ x (M + 2) (M + 1) = 0 := by
    unfold secondRightTerm
    push_cast
    ring
  rw [hlast, hpenult, add_zero, add_zero]
  unfold egfConvolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact secondRightTerm_eq_shifted_egf r τ x
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

theorem sum_firstSquareTerm_eq_convolution
    (r τ x : ℝ) (M : ℕ) :
    (∑ j ∈ Finset.range (M + 2 + 1), firstSquareTerm r τ x (M + 2) j) =
      x ^ 2 * egfConvolution r τ 1 1 x M := by
  rw [Finset.sum_range_succ']
  rw [Finset.sum_range_succ]
  have hzero : firstSquareTerm r τ x (M + 2) 0 = 0 := by
    unfold firstSquareTerm
    norm_num
  have hlast : firstSquareTerm r τ x (M + 2) (M + 1 + 1) = 0 := by
    unfold firstSquareTerm
    push_cast
    ring
  rw [hzero, hlast, add_zero, add_zero]
  unfold egfConvolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact firstSquareTerm_eq_shifted_egf r τ x
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

noncomputable def baseCurvatureTerm
    (r τ x : ℝ) (N j : ℕ) : ℝ :=
  2 * (Nat.choose N j : ℝ) * scalarDerivative r τ j *
    scalarDerivative r τ (N - j) * x ^ N / (Nat.factorial N : ℝ)

theorem sum_baseCurvatureTerm_eq_convolution
    (r τ x : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), baseCurvatureTerm r τ x N j) =
      2 * egfConvolution r τ 0 0 x N := by
  rw [egfConvolution_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  unfold baseCurvatureTerm
  simp only [Nat.add_zero]
  ring

noncomputable def curvatureSeriesTerm (r τ x : ℝ) (N : ℕ) : ℝ :=
  SSP.K3CyclicComplex.scalarCurvatureCoefficient (scalarDerivative r τ) N *
    x ^ N / (Nat.factorial N : ℝ)

theorem curvatureSeriesTerm_shift (r τ x : ℝ) (M : ℕ) :
    curvatureSeriesTerm r τ x (M + 2) =
      x ^ 2 * (egfConvolution r τ 0 2 x M -
        egfConvolution r τ 1 1 x M) +
      2 * egfConvolution r τ 0 0 x (M + 2) := by
  unfold curvatureSeriesTerm
  rw [← nonsymmetricKernel_sum_eq_scalarCurvatureCoefficient]
  rw [Finset.sum_mul, Finset.sum_div]
  calc
    (∑ j ∈ Finset.range (M + 2 + 1),
        nonsymmetricKernelWeight (M + 2) j *
          scalarDerivative r τ j * scalarDerivative r τ (M + 2 - j) *
          x ^ (M + 2) / (Nat.factorial (M + 2) : ℝ)) =
      ∑ j ∈ Finset.range (M + 2 + 1),
        (baseCurvatureTerm r τ x (M + 2) j +
          secondRightTerm r τ x (M + 2) j -
          firstSquareTerm r τ x (M + 2) j) := by
      apply Finset.sum_congr rfl
      intro j hj
      unfold nonsymmetricKernelWeight baseCurvatureTerm secondRightTerm
        firstSquareTerm
      ring
    _ = (∑ j ∈ Finset.range (M + 2 + 1),
          baseCurvatureTerm r τ x (M + 2) j) +
        (∑ j ∈ Finset.range (M + 2 + 1),
          secondRightTerm r τ x (M + 2) j) -
        (∑ j ∈ Finset.range (M + 2 + 1),
          firstSquareTerm r τ x (M + 2) j) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_baseCurvatureTerm_eq_convolution,
        sum_secondRightTerm_eq_convolution,
        sum_firstSquareTerm_eq_convolution]
      ring

@[simp] theorem curvatureSeriesTerm_zero (r τ x : ℝ) :
    curvatureSeriesTerm r τ x 0 =
      2 * egfConvolution r τ 0 0 x 0 := by
  unfold curvatureSeriesTerm
  rw [← nonsymmetricKernel_sum_eq_scalarCurvatureCoefficient]
  norm_num [nonsymmetricKernelWeight, egfConvolution, egfTerm,
    scalarDerivative]

@[simp] theorem curvatureSeriesTerm_one (r τ x : ℝ) :
    curvatureSeriesTerm r τ x 1 =
      2 * egfConvolution r τ 0 0 x 1 := by
  unfold curvatureSeriesTerm
  rw [← nonsymmetricKernel_sum_eq_scalarCurvatureCoefficient]
  norm_num [nonsymmetricKernelWeight, egfConvolution, egfTerm,
    scalarDerivative, Finset.sum_range_succ]
  ring

theorem curvatureSeriesTerm_summable
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    Summable (curvatureSeriesTerm r τ x) := by
  let A : ℕ → ℝ := fun M => x ^ 2 *
    (egfConvolution r τ 0 2 x M - egfConvolution r τ 1 1 x M)
  let B : ℕ → ℝ := fun N => 2 * egfConvolution r τ 0 0 x N
  have hA : Summable A :=
    ((egfConvolution_summable (x := x) hr0 hr1 hτ0 hτ1 0 2).sub
      (egfConvolution_summable (x := x) hr0 hr1 hτ0 hτ1 1 1)).mul_left
        (x ^ 2)
  have hB : Summable B :=
    (egfConvolution_summable (x := x) hr0 hr1 hτ0 hτ1 0 0).mul_left 2
  have hBshift : Summable (fun M => B (M + 2)) :=
    (summable_nat_add_iff 2).2 hB
  have hshift : Summable (fun M => curvatureSeriesTerm r τ x (M + 2)) := by
    apply Summable.congr (hA.add hBshift)
    intro M
    rw [curvatureSeriesTerm_shift]
  exact (summable_nat_add_iff 2).1 hshift

theorem recurrenceCurvature_eq_coefficientSeries
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    recurrenceCurvature r τ x = ∑' N, curvatureSeriesTerm r τ x N := by
  let A : ℕ → ℝ := fun M => x ^ 2 *
    (egfConvolution r τ 0 2 x M - egfConvolution r τ 1 1 x M)
  let B : ℕ → ℝ := fun N => 2 * egfConvolution r τ 0 0 x N
  have hA : Summable A :=
    ((egfConvolution_summable (x := x) hr0 hr1 hτ0 hτ1 0 2).sub
      (egfConvolution_summable (x := x) hr0 hr1 hτ0 hτ1 1 1)).mul_left
        (x ^ 2)
  have hB : Summable B :=
    (egfConvolution_summable (x := x) hr0 hr1 hτ0 hτ1 0 0).mul_left 2
  have hBshift : Summable (fun M => B (M + 2)) :=
    (summable_nat_add_iff 2).2 hB
  have hC := curvatureSeriesTerm_summable (x := x) hr0 hr1 hτ0 hτ1
  have hrawSum : (∑' M, rawCurvatureConvolution r τ x M) =
      (∑' M, A M) + ∑' M, B M := by
    rw [show rawCurvatureConvolution r τ x = fun M => A M + B M by
      funext M
      rfl]
    exact (hA.hasSum.add hB.hasSum).tsum_eq
  have hshiftSum : (∑' M, curvatureSeriesTerm r τ x (M + 2)) =
      (∑' M, A M) + ∑' M, B (M + 2) := by
    rw [show (fun M => curvatureSeriesTerm r τ x (M + 2)) =
        fun M => A M + B (M + 2) by
      funext M
      rw [curvatureSeriesTerm_shift]]
    exact (hA.hasSum.add hBshift.hasSum).tsum_eq
  have hCsplit := hC.sum_add_tsum_nat_add 2
  have hBsplit := hB.sum_add_tsum_nat_add 2
  rw [recurrenceCurvature_eq_rawSeries hr0 hr1 hτ0 hτ1, hrawSum]
  rw [← hCsplit, ← hBsplit, hshiftSum]
  norm_num [B, Finset.sum_range_succ]
  ring

theorem recurrenceF1_eq_firstF1
    {m₀ ω r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hr : r = 3 * m₀) (hz : scalarZ r τ = ω ^ 2) (hω : ω ≠ 0) :
    recurrenceF1 r τ = firstF1 m₀ ω := by
  have hfun := recurrenceF_eq_firstF hr0 hr1 hτ0 hτ1 hr hz hω
  funext x
  have h := congrArg (fun f : ℝ → ℝ => deriv f x) hfun
  rw [(recurrenceF_hasDerivAt hr0 hr1 hτ0 hτ1).deriv,
    (firstF_hasDerivAt (m := m₀) (ω := ω) (x := x) hω).deriv] at h
  exact h

theorem recurrenceF2_eq_firstF2
    {m₀ ω r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hr : r = 3 * m₀) (hz : scalarZ r τ = ω ^ 2) (hω : ω ≠ 0) :
    recurrenceF2 r τ = firstF2 m₀ ω := by
  have hfun := recurrenceF1_eq_firstF1 hr0 hr1 hτ0 hτ1 hr hz hω
  funext x
  have h := congrArg (fun f : ℝ → ℝ => deriv f x) hfun
  rw [(recurrenceF1_hasDerivAt hr0 hr1 hτ0 hτ1).deriv,
    (firstF1_hasDerivAt (m := m₀) (ω := ω) (x := x) hω).deriv] at h
  exact h

theorem firstFCurvature_eq_coefficientSeries
    {m₀ ω r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hr : r = 3 * m₀) (hz : scalarZ r τ = ω ^ 2) (hω : ω ≠ 0) :
    x ^ 2 * (firstF m₀ ω x * firstF2 m₀ ω x -
        firstF1 m₀ ω x ^ 2) + 2 * firstF m₀ ω x ^ 2 =
      ∑' N, curvatureSeriesTerm r τ x N := by
  rw [← recurrenceF_eq_firstF hr0 hr1 hτ0 hτ1 hr hz hω,
    ← recurrenceF1_eq_firstF1 hr0 hr1 hτ0 hτ1 hr hz hω,
    ← recurrenceF2_eq_firstF2 hr0 hr1 hτ0 hτ1 hr hz hω]
  exact recurrenceCurvature_eq_coefficientSeries hr0 hr1 hτ0 hτ1

end SSP.K3CyclicComplex.PositiveCoeff
