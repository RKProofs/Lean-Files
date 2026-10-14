import SSPLean.K3CyclicComplexMiddleSeries
import SSPLean.K3CyclicComplexFirstPositiveCurvatureSeries

/-! # Regrouping the complex-middle curvature series by total degree -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

open scoped BigOperators

theorem middleEgfTerm_mul_complement
    (rhoValue etaValue x : ℝ) {M i : ℕ} (hi : i ≤ M) (a b : ℕ) :
    middleEgfTerm rhoValue etaValue a i x *
        middleEgfTerm rhoValue etaValue b (M - i) x =
      (Nat.choose M i : ℝ) * scalarDerivative rhoValue etaValue (i + a) *
        scalarDerivative rhoValue etaValue (M - i + b) * x ^ M /
          (Nat.factorial M : ℝ) := by
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial hi
  have hchoose :
      (Nat.choose M i : ℝ) * (Nat.factorial i : ℝ) *
          (Nat.factorial (M - i) : ℝ) = (Nat.factorial M : ℝ) := by
    exact_mod_cast hchooseNat
  have hchooseNe : (Nat.choose M i : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hi).ne'
  have hpow : x ^ i * x ^ (M - i) = x ^ M := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  unfold middleEgfTerm
  rw [← hchoose, ← hpow]
  field_simp [hchooseNe]

theorem middleEgfConvolution_eq
    (rhoValue etaValue x : ℝ) (a b M : ℕ) :
    middleEgfConvolution rhoValue etaValue a b x M =
      ∑ i ∈ Finset.range (M + 1),
        (Nat.choose M i : ℝ) *
          scalarDerivative rhoValue etaValue (i + a) *
          scalarDerivative rhoValue etaValue (M - i + b) * x ^ M /
            (Nat.factorial M : ℝ) := by
  unfold middleEgfConvolution
  apply Finset.sum_congr rfl
  intro i hi
  exact middleEgfTerm_mul_complement rhoValue etaValue x
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) a b

noncomputable def middleNonsymmetricKernelWeight (N j : ℕ) : ℝ :=
  (Nat.choose N j : ℝ) *
    (1 + ((N : ℝ) - j) * ((N : ℝ) - 2 * j - 1))

theorem average_middleNonsymmetricKernelWeight_eq
    {N j : ℕ} (hj : j ≤ N) :
    (middleNonsymmetricKernelWeight N j +
      middleNonsymmetricKernelWeight N (N - j)) / 2 =
        (kernel N j : ℝ) := by
  unfold middleNonsymmetricKernelWeight kernel
  rw [Nat.choose_symm hj]
  push_cast [Nat.cast_sub hj]
  ring

theorem middleNonsymmetricKernel_sum_eq_scalarCurvatureCoefficient
    (rhoValue etaValue : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1),
      middleNonsymmetricKernelWeight N j *
        scalarDerivative rhoValue etaValue j *
        scalarDerivative rhoValue etaValue (N - j)) =
      scalarCurvatureCoefficient rhoValue etaValue N := by
  let f : ℕ → ℝ := fun j =>
    middleNonsymmetricKernelWeight N j *
      scalarDerivative rhoValue etaValue j *
      scalarDerivative rhoValue etaValue (N - j)
  have href0 := Finset.sum_range_reflect f (N + 1)
  have href :
      (∑ j ∈ Finset.range (N + 1),
        middleNonsymmetricKernelWeight N (N - j) *
          scalarDerivative rhoValue etaValue j *
          scalarDerivative rhoValue etaValue (N - j)) =
      ∑ j ∈ Finset.range (N + 1),
        middleNonsymmetricKernelWeight N j *
          scalarDerivative rhoValue etaValue j *
          scalarDerivative rhoValue etaValue (N - j) := by
    rw [← href0]
    apply Finset.sum_congr rfl
    intro j hjmem
    have hj : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hjmem)
    dsimp [f]
    rw [Nat.sub_sub_self hj]
    ring
  unfold scalarCurvatureCoefficient
  calc
    (∑ j ∈ Finset.range (N + 1),
      middleNonsymmetricKernelWeight N j *
        scalarDerivative rhoValue etaValue j *
        scalarDerivative rhoValue etaValue (N - j)) =
      ((∑ j ∈ Finset.range (N + 1),
          middleNonsymmetricKernelWeight N j *
            scalarDerivative rhoValue etaValue j *
            scalarDerivative rhoValue etaValue (N - j)) +
        ∑ j ∈ Finset.range (N + 1),
          middleNonsymmetricKernelWeight N (N - j) *
            scalarDerivative rhoValue etaValue j *
            scalarDerivative rhoValue etaValue (N - j)) / 2 := by
      rw [href]
      ring
    _ = ∑ j ∈ Finset.range (N + 1),
        ((middleNonsymmetricKernelWeight N j +
          middleNonsymmetricKernelWeight N (N - j)) / 2) *
          scalarDerivative rhoValue etaValue j *
          scalarDerivative rhoValue etaValue (N - j) := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ j ∈ Finset.range (N + 1),
        (kernel N j : ℝ) * scalarDerivative rhoValue etaValue j *
          scalarDerivative rhoValue etaValue (N - j) := by
      apply Finset.sum_congr rfl
      intro j hjmem
      rw [average_middleNonsymmetricKernelWeight_eq
        (Nat.le_of_lt_succ (Finset.mem_range.mp hjmem))]

noncomputable def middleSecondRightTerm
    (rhoValue etaValue x : ℝ) (N j : ℕ) : ℝ :=
  (Nat.choose N j : ℝ) * ((N : ℝ) - j) * ((N : ℝ) - j - 1) *
    scalarDerivative rhoValue etaValue j *
    scalarDerivative rhoValue etaValue (N - j) * x ^ N /
      (Nat.factorial N : ℝ)

noncomputable def middleFirstSquareTerm
    (rhoValue etaValue x : ℝ) (N j : ℕ) : ℝ :=
  (Nat.choose N j : ℝ) * (j : ℝ) * ((N : ℝ) - j) *
    scalarDerivative rhoValue etaValue j *
    scalarDerivative rhoValue etaValue (N - j) * x ^ N /
      (Nat.factorial N : ℝ)

theorem middleSecondRightTerm_eq_shifted_egf
    (rhoValue etaValue x : ℝ) {M i : ℕ} (hi : i ≤ M) :
    middleSecondRightTerm rhoValue etaValue x (M + 2) i =
      x ^ 2 * (middleEgfTerm rhoValue etaValue 0 i x *
        middleEgfTerm rhoValue etaValue 2 (M - i) x) := by
  have hsub : M + 2 - i = M - i + 2 := by omega
  have hcoeff :
      (Nat.choose (M + 2) i : ℝ) * (((M + 2 : ℕ) : ℝ) - i) *
          (((M + 2 : ℕ) : ℝ) - i - 1) /
            (Nat.factorial (M + 2) : ℝ) =
        (Nat.choose M i : ℝ) / (Nat.factorial M : ℝ) := by
    rw [SSP.K3CyclicComplex.PositiveCoeff.choose_two_step_right_factorial hi,
      SSP.K3CyclicComplex.PositiveCoeff.choose_factorial_ratio hi]
  rw [middleEgfTerm_mul_complement rhoValue etaValue x hi 0 2]
  simp only [Nat.add_zero]
  calc
    middleSecondRightTerm rhoValue etaValue x (M + 2) i =
        ((Nat.choose (M + 2) i : ℝ) * (((M + 2 : ℕ) : ℝ) - i) *
          (((M + 2 : ℕ) : ℝ) - i - 1) /
            (Nat.factorial (M + 2) : ℝ)) *
          (scalarDerivative rhoValue etaValue i *
            scalarDerivative rhoValue etaValue (M - i + 2) *
            x ^ (M + 2)) := by
      unfold middleSecondRightTerm
      rw [hsub]
      ring
    _ = ((Nat.choose M i : ℝ) / (Nat.factorial M : ℝ)) *
          (scalarDerivative rhoValue etaValue i *
            scalarDerivative rhoValue etaValue (M - i + 2) *
            x ^ (M + 2)) := by rw [hcoeff]
    _ = x ^ 2 *
        ((Nat.choose M i : ℝ) * scalarDerivative rhoValue etaValue i *
          scalarDerivative rhoValue etaValue (M - i + 2) * x ^ M /
            (Nat.factorial M : ℝ)) := by
      rw [show x ^ (M + 2) = x ^ 2 * x ^ M by rw [pow_add, mul_comm]]
      ring

theorem middleFirstSquareTerm_eq_shifted_egf
    (rhoValue etaValue x : ℝ) {M i : ℕ} (hi : i ≤ M) :
    middleFirstSquareTerm rhoValue etaValue x (M + 2) (i + 1) =
      x ^ 2 * (middleEgfTerm rhoValue etaValue 1 i x *
        middleEgfTerm rhoValue etaValue 1 (M - i) x) := by
  have hsub : M + 2 - (i + 1) = M - i + 1 := by omega
  have hcoeff :
      (Nat.choose (M + 2) (i + 1) : ℝ) * ((i + 1 : ℕ) : ℝ) *
          (((M + 2 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) /
            (Nat.factorial (M + 2) : ℝ) =
        (Nat.choose M i : ℝ) / (Nat.factorial M : ℝ) := by
    rw [SSP.K3CyclicComplex.PositiveCoeff.choose_one_step_each_factorial hi,
      SSP.K3CyclicComplex.PositiveCoeff.choose_factorial_ratio hi]
  rw [middleEgfTerm_mul_complement rhoValue etaValue x hi 1 1]
  calc
    middleFirstSquareTerm rhoValue etaValue x (M + 2) (i + 1) =
        ((Nat.choose (M + 2) (i + 1) : ℝ) * ((i + 1 : ℕ) : ℝ) *
          (((M + 2 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) /
            (Nat.factorial (M + 2) : ℝ)) *
          (scalarDerivative rhoValue etaValue (i + 1) *
            scalarDerivative rhoValue etaValue (M - i + 1) *
            x ^ (M + 2)) := by
      unfold middleFirstSquareTerm
      rw [hsub]
      ring
    _ = ((Nat.choose M i : ℝ) / (Nat.factorial M : ℝ)) *
          (scalarDerivative rhoValue etaValue (i + 1) *
            scalarDerivative rhoValue etaValue (M - i + 1) *
            x ^ (M + 2)) := by rw [hcoeff]
    _ = x ^ 2 *
        ((Nat.choose M i : ℝ) * scalarDerivative rhoValue etaValue (i + 1) *
          scalarDerivative rhoValue etaValue (M - i + 1) * x ^ M /
            (Nat.factorial M : ℝ)) := by
      rw [show x ^ (M + 2) = x ^ 2 * x ^ M by rw [pow_add, mul_comm]]
      ring

theorem sum_middleSecondRightTerm_eq_convolution
    (rhoValue etaValue x : ℝ) (M : ℕ) :
    (∑ j ∈ Finset.range (M + 2 + 1),
      middleSecondRightTerm rhoValue etaValue x (M + 2) j) =
      x ^ 2 * middleEgfConvolution rhoValue etaValue 0 2 x M := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hlast : middleSecondRightTerm rhoValue etaValue x
      (M + 2) (M + 2) = 0 := by
    unfold middleSecondRightTerm
    norm_num
  have hpenult : middleSecondRightTerm rhoValue etaValue x
      (M + 2) (M + 1) = 0 := by
    unfold middleSecondRightTerm
    push_cast
    ring
  rw [hlast, hpenult, add_zero, add_zero]
  unfold middleEgfConvolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact middleSecondRightTerm_eq_shifted_egf rhoValue etaValue x
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

theorem sum_middleFirstSquareTerm_eq_convolution
    (rhoValue etaValue x : ℝ) (M : ℕ) :
    (∑ j ∈ Finset.range (M + 2 + 1),
      middleFirstSquareTerm rhoValue etaValue x (M + 2) j) =
      x ^ 2 * middleEgfConvolution rhoValue etaValue 1 1 x M := by
  rw [Finset.sum_range_succ']
  rw [Finset.sum_range_succ]
  have hzero : middleFirstSquareTerm rhoValue etaValue x (M + 2) 0 = 0 := by
    unfold middleFirstSquareTerm
    norm_num
  have hlast : middleFirstSquareTerm rhoValue etaValue x
      (M + 2) (M + 1 + 1) = 0 := by
    unfold middleFirstSquareTerm
    push_cast
    ring
  rw [hzero, hlast, add_zero, add_zero]
  unfold middleEgfConvolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact middleFirstSquareTerm_eq_shifted_egf rhoValue etaValue x
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

noncomputable def middleBaseCurvatureTerm
    (rhoValue etaValue x : ℝ) (N j : ℕ) : ℝ :=
  (Nat.choose N j : ℝ) * scalarDerivative rhoValue etaValue j *
    scalarDerivative rhoValue etaValue (N - j) * x ^ N /
      (Nat.factorial N : ℝ)

theorem sum_middleBaseCurvatureTerm_eq_convolution
    (rhoValue etaValue x : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1),
      middleBaseCurvatureTerm rhoValue etaValue x N j) =
      middleEgfConvolution rhoValue etaValue 0 0 x N := by
  rw [middleEgfConvolution_eq]
  apply Finset.sum_congr rfl
  intro j hj
  unfold middleBaseCurvatureTerm
  simp only [Nat.add_zero]

noncomputable def middleCurvatureSeriesTerm
    (rhoValue etaValue x : ℝ) (N : ℕ) : ℝ :=
  scalarCurvatureCoefficient rhoValue etaValue N * x ^ N /
    (Nat.factorial N : ℝ)

theorem middleCurvatureSeriesTerm_shift
    (rhoValue etaValue x : ℝ) (M : ℕ) :
    middleCurvatureSeriesTerm rhoValue etaValue x (M + 2) =
      x ^ 2 * (middleEgfConvolution rhoValue etaValue 0 2 x M -
        middleEgfConvolution rhoValue etaValue 1 1 x M) +
      middleEgfConvolution rhoValue etaValue 0 0 x (M + 2) := by
  unfold middleCurvatureSeriesTerm
  rw [← middleNonsymmetricKernel_sum_eq_scalarCurvatureCoefficient]
  rw [Finset.sum_mul, Finset.sum_div]
  calc
    (∑ j ∈ Finset.range (M + 2 + 1),
      middleNonsymmetricKernelWeight (M + 2) j *
        scalarDerivative rhoValue etaValue j *
        scalarDerivative rhoValue etaValue (M + 2 - j) *
        x ^ (M + 2) / (Nat.factorial (M + 2) : ℝ)) =
      ∑ j ∈ Finset.range (M + 2 + 1),
        (middleBaseCurvatureTerm rhoValue etaValue x (M + 2) j +
          middleSecondRightTerm rhoValue etaValue x (M + 2) j -
          middleFirstSquareTerm rhoValue etaValue x (M + 2) j) := by
      apply Finset.sum_congr rfl
      intro j hj
      unfold middleNonsymmetricKernelWeight middleBaseCurvatureTerm
        middleSecondRightTerm middleFirstSquareTerm
      ring
    _ = (∑ j ∈ Finset.range (M + 2 + 1),
          middleBaseCurvatureTerm rhoValue etaValue x (M + 2) j) +
        (∑ j ∈ Finset.range (M + 2 + 1),
          middleSecondRightTerm rhoValue etaValue x (M + 2) j) -
        (∑ j ∈ Finset.range (M + 2 + 1),
          middleFirstSquareTerm rhoValue etaValue x (M + 2) j) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_middleBaseCurvatureTerm_eq_convolution,
        sum_middleSecondRightTerm_eq_convolution,
        sum_middleFirstSquareTerm_eq_convolution]
      ring

@[simp] theorem middleCurvatureSeriesTerm_zero
    (rhoValue etaValue x : ℝ) :
    middleCurvatureSeriesTerm rhoValue etaValue x 0 =
      middleEgfConvolution rhoValue etaValue 0 0 x 0 := by
  unfold middleCurvatureSeriesTerm
  rw [← middleNonsymmetricKernel_sum_eq_scalarCurvatureCoefficient]
  norm_num [middleNonsymmetricKernelWeight, middleEgfConvolution,
    middleEgfTerm]

@[simp] theorem middleCurvatureSeriesTerm_one
    (rhoValue etaValue x : ℝ) :
    middleCurvatureSeriesTerm rhoValue etaValue x 1 =
      middleEgfConvolution rhoValue etaValue 0 0 x 1 := by
  unfold middleCurvatureSeriesTerm
  rw [← middleNonsymmetricKernel_sum_eq_scalarCurvatureCoefficient]
  norm_num [middleNonsymmetricKernelWeight, middleEgfConvolution,
    middleEgfTerm, Finset.sum_range_succ]
  ring

theorem middleCurvatureSeriesTerm_summable
    {rhoValue etaValue x : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) :
    Summable (middleCurvatureSeriesTerm rhoValue etaValue x) := by
  let A : ℕ → ℝ := fun M => x ^ 2 *
    (middleEgfConvolution rhoValue etaValue 0 2 x M -
      middleEgfConvolution rhoValue etaValue 1 1 x M)
  let B : ℕ → ℝ := fun N =>
    middleEgfConvolution rhoValue etaValue 0 0 x N
  have hA : Summable A :=
    ((middleEgfConvolution_summable (x := x)
      hrho0 hrho1 heta0 heta1 0 2).sub
      (middleEgfConvolution_summable (x := x)
        hrho0 hrho1 heta0 heta1 1 1)).mul_left (x ^ 2)
  have hB : Summable B :=
    middleEgfConvolution_summable (x := x)
      hrho0 hrho1 heta0 heta1 0 0
  have hBshift : Summable (fun M => B (M + 2)) :=
    (summable_nat_add_iff 2).2 hB
  have hshift : Summable
      (fun M => middleCurvatureSeriesTerm rhoValue etaValue x (M + 2)) := by
    apply Summable.congr (hA.add hBshift)
    intro M
    rw [middleCurvatureSeriesTerm_shift]
  exact (summable_nat_add_iff 2).1 hshift

theorem middleRecurrenceCurvature_eq_coefficientSeries
    {rhoValue etaValue x : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) :
    middleRecurrenceCurvature rhoValue etaValue x =
      ∑' N, middleCurvatureSeriesTerm rhoValue etaValue x N := by
  let A : ℕ → ℝ := fun M => x ^ 2 *
    (middleEgfConvolution rhoValue etaValue 0 2 x M -
      middleEgfConvolution rhoValue etaValue 1 1 x M)
  let B : ℕ → ℝ := fun N =>
    middleEgfConvolution rhoValue etaValue 0 0 x N
  have hA : Summable A :=
    ((middleEgfConvolution_summable (x := x)
      hrho0 hrho1 heta0 heta1 0 2).sub
      (middleEgfConvolution_summable (x := x)
        hrho0 hrho1 heta0 heta1 1 1)).mul_left (x ^ 2)
  have hB : Summable B :=
    middleEgfConvolution_summable (x := x)
      hrho0 hrho1 heta0 heta1 0 0
  have hBshift : Summable (fun M => B (M + 2)) :=
    (summable_nat_add_iff 2).2 hB
  have hC := middleCurvatureSeriesTerm_summable
    (x := x) hrho0 hrho1 heta0 heta1
  have hrawSum :
      (∑' M, middleRawCurvatureConvolution rhoValue etaValue x M) =
        (∑' M, A M) + ∑' M, B M := by
    rw [show middleRawCurvatureConvolution rhoValue etaValue x =
        fun M => A M + B M by funext M; rfl]
    exact (hA.hasSum.add hB.hasSum).tsum_eq
  have hshiftSum :
      (∑' M, middleCurvatureSeriesTerm rhoValue etaValue x (M + 2)) =
        (∑' M, A M) + ∑' M, B (M + 2) := by
    rw [show (fun M => middleCurvatureSeriesTerm rhoValue etaValue x (M + 2)) =
        fun M => A M + B (M + 2) by
      funext M
      rw [middleCurvatureSeriesTerm_shift]]
    exact (hA.hasSum.add hBshift.hasSum).tsum_eq
  have hCsplit := hC.sum_add_tsum_nat_add 2
  have hBsplit := hB.sum_add_tsum_nat_add 2
  rw [middleRecurrenceCurvature_eq_rawSeries
    hrho0 hrho1 heta0 heta1, hrawSum]
  rw [← hCsplit, ← hBsplit, hshiftSum]
  norm_num [B, Finset.sum_range_succ]
  ring

lemma scalarCurvatureCoefficient_low_zero
    (rhoValue etaValue : ℝ) {N : ℕ} (hN : N < 4) :
    scalarCurvatureCoefficient rhoValue etaValue N = 0 := by
  interval_cases N <;>
    norm_num [scalarCurvatureCoefficient, kernel, scalarDerivative,
      cosineSign, sineSign, Finset.sum_range_succ]

theorem middleRecurrenceCurvature_nonneg
    {rhoValue etaValue x : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1)
    (hx : 0 ≤ x) :
    0 ≤ middleRecurrenceCurvature rhoValue etaValue x := by
  rw [middleRecurrenceCurvature_eq_coefficientSeries
    hrho0 hrho1 heta0 heta1]
  apply tsum_nonneg
  intro N
  unfold middleCurvatureSeriesTerm
  have hcoeff : 0 ≤ scalarCurvatureCoefficient rhoValue etaValue N := by
    by_cases hN : 4 ≤ N
    · exact scalarCurvatureCoefficient_nonneg_all hN
        hrho0 hrho1 heta0 heta1
    · rw [scalarCurvatureCoefficient_low_zero rhoValue etaValue (by omega)]
  exact div_nonneg (mul_nonneg hcoeff (pow_nonneg hx _)) (by positivity)

end SSP.K3CyclicComplex.MiddleCoeff
