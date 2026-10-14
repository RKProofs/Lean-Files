import SSPLean.K3CyclicComplexFirstCoefficientSemantics
import SSPLean.K3CyclicComplexFirstAnalyticODE

/-! # Scalar recurrence behind the positive complex-first certificate -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.PositiveCoeff

open SSP.K3CyclicComplex Dense

noncomputable def scalarM (r : ℝ) : ℝ := r / 3

noncomputable def scalarZ (r τ : ℝ) : ℝ :=
  τ * (3 - 2 * r - r ^ 2) / 12

/-- The scalar derivative sequence represented by `derivativeTriple`. -/
noncomputable def scalarDerivative (r τ : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => -scalarM r
  | 2 => scalarM r ^ 2
  | n + 3 => scalarDerivative r τ (n + 2) -
      scalarZ r τ * scalarDerivative r τ (n + 1) +
      scalarZ r τ * scalarDerivative r τ n

@[simp] theorem beval_m (r τ : ℝ) :
    beval m r τ = scalarM r := by
  simp [m, scalarM, beval_mul]
  ring

@[simp] theorem beval_z (r τ : ℝ) :
    beval z r τ = scalarZ r τ := by
  simp [z, scalarZ, beval_mul, beval_sub, beval_pow]
  ring

theorem derivativeTriple_eval (r τ : ℝ) (n : ℕ) :
    beval (derivativeTriple n).1 r τ = scalarDerivative r τ n ∧
      beval (derivativeTriple n).2.1 r τ = scalarDerivative r τ (n + 1) ∧
      beval (derivativeTriple n).2.2 r τ = scalarDerivative r τ (n + 2) := by
  induction n with
  | zero =>
      simp [derivativeTriple, initialTriple, bone, scalarDerivative,
        beval_pow]
  | succ n ih =>
      rcases ih with ⟨ih0, ih1, ih2⟩
      simp only [derivativeTriple, nextTriple]
      refine ⟨ih1, ih2, ?_⟩
      rw [beval_add, beval_sub, beval_mul, beval_mul, beval_z,
        ih0, ih1, ih2]
      rw [show n + 1 + 2 = n + 3 by omega, scalarDerivative]

theorem derivativeValue_eq (r τ : ℝ) (n : ℕ) :
    derivativeValue r τ n = scalarDerivative r τ n := by
  exact (derivativeTriple_eval r τ n).1

/-- Under the chart substitution, the executable sequence has exactly the
initial values and recurrence of the normalized analytic function `firstF`. -/
theorem scalarDerivative_chart_rec (ω r τ : ℝ)
    (hz : scalarZ r τ = ω ^ 2) (n : ℕ) :
    scalarDerivative r τ (n + 3) =
      scalarDerivative r τ (n + 2) -
        ω ^ 2 * scalarDerivative r τ (n + 1) +
          ω ^ 2 * scalarDerivative r τ n := by
  rw [scalarDerivative, hz]

theorem scalarDerivative_chart_initial (m₀ ω r τ : ℝ)
    (hr : r = 3 * m₀) :
    scalarDerivative r τ 0 = firstF m₀ ω 0 ∧
      scalarDerivative r τ 1 = firstF1 m₀ ω 0 ∧
      scalarDerivative r τ 2 = firstF2 m₀ ω 0 := by
  subst r
  simp [scalarDerivative, scalarM]

theorem scalarZ_mem_unit {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    0 ≤ scalarZ r τ ∧ scalarZ r τ ≤ 1 := by
  unfold scalarZ
  have hbracket0 : 0 ≤ 3 - 2 * r - r ^ 2 := by nlinarith
  have hbracket1 : 3 - 2 * r - r ^ 2 ≤ 3 := by nlinarith
  constructor
  · positivity
  · have hmul : τ * (3 - 2 * r - r ^ 2) ≤ 3 := by
      nlinarith [mul_le_mul hτ1 hbracket1 hbracket0 (by norm_num : (0 : ℝ) ≤ 1)]
    nlinarith

/-- A deliberately coarse but uniform recurrence bound.  The base `3` is
small enough for the degree-70 remainder estimate and keeps the proof purely
real and elementary. -/
theorem abs_scalarDerivative_le_three_pow
    {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    |scalarDerivative r τ n| ≤ (3 : ℝ) ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with (_ | _ | _ | n)
      · simp [scalarDerivative]
      · rw [scalarDerivative]
        unfold scalarM
        rw [abs_neg, abs_div, abs_of_nonneg hr0]
        norm_num
        nlinarith
      · rw [scalarDerivative, abs_sq]
        have hm : |scalarM r| ≤ 1 := by
          unfold scalarM
          rw [abs_div, abs_of_nonneg hr0]
          norm_num
          nlinarith
        calc
          scalarM r ^ 2 = |scalarM r| ^ 2 := (sq_abs (scalarM r)).symm
          _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hm 2
          _ ≤ (3 : ℝ) ^ 2 := by norm_num
      · rw [scalarDerivative]
        obtain ⟨hz0, hz1⟩ := scalarZ_mem_unit hr0 hr1 hτ0 hτ1
        have hzabs : |scalarZ r τ| ≤ 1 := by simpa [abs_of_nonneg hz0]
        have h0 := ih n (by omega)
        have h1 := ih (n + 1) (by omega)
        have h2 := ih (n + 2) (by omega)
        calc
          |scalarDerivative r τ (n + 2) -
                scalarZ r τ * scalarDerivative r τ (n + 1) +
              scalarZ r τ * scalarDerivative r τ n| ≤
              |scalarDerivative r τ (n + 2)| +
                |scalarZ r τ * scalarDerivative r τ (n + 1)| +
                  |scalarZ r τ * scalarDerivative r τ n| := by
            refine (abs_add_le
              (scalarDerivative r τ (n + 2) -
                scalarZ r τ * scalarDerivative r τ (n + 1))
              (scalarZ r τ * scalarDerivative r τ n)).trans ?_
            exact add_le_add_left
              (abs_sub (scalarDerivative r τ (n + 2))
                (scalarZ r τ * scalarDerivative r τ (n + 1))) _
          _ ≤ (3 : ℝ) ^ (n + 2) + 3 ^ (n + 1) + 3 ^ n := by
            rw [abs_mul, abs_mul]
            have hz1bound : |scalarZ r τ| * |scalarDerivative r τ (n + 1)| ≤
                (3 : ℝ) ^ (n + 1) := by
              calc
                |scalarZ r τ| * |scalarDerivative r τ (n + 1)| ≤
                    1 * |scalarDerivative r τ (n + 1)| :=
                      mul_le_mul_of_nonneg_right hzabs (abs_nonneg _)
                _ ≤ (3 : ℝ) ^ (n + 1) := by simpa using h1
            have hz0bound : |scalarZ r τ| * |scalarDerivative r τ n| ≤
                (3 : ℝ) ^ n := by
              calc
                |scalarZ r τ| * |scalarDerivative r τ n| ≤
                    1 * |scalarDerivative r τ n| :=
                      mul_le_mul_of_nonneg_right hzabs (abs_nonneg _)
                _ ≤ (3 : ℝ) ^ n := by simpa using h0
            linarith
          _ ≤ (3 : ℝ) ^ (n + 3) := by
            simp only [pow_add]
            norm_num
            nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) n]

noncomputable def constantMode (r τ : ℝ) : ℝ :=
  (scalarM r ^ 2 + scalarZ r τ) / (1 + scalarZ r τ)

noncomputable def oscillatorMode (r τ : ℝ) : ℕ → ℝ
  | 0 => 1 - constantMode r τ
  | 1 => -scalarM r - constantMode r τ
  | n + 2 => -scalarZ r τ * oscillatorMode r τ n

theorem one_add_scalarZ_ne_zero
    {r τ : ℝ} (hz0 : 0 ≤ scalarZ r τ) : 1 + scalarZ r τ ≠ 0 := by
  linarith

theorem constantMode_add_oscillator_two
    {r τ : ℝ} (hz0 : 0 ≤ scalarZ r τ) :
    constantMode r τ + oscillatorMode r τ 2 = scalarM r ^ 2 := by
  simp only [oscillatorMode]
  unfold constantMode
  field_simp [one_add_scalarZ_ne_zero hz0]
  ring

theorem modelDerivative_rec (r τ : ℝ) (n : ℕ) :
    constantMode r τ + oscillatorMode r τ (n + 3) =
      (constantMode r τ + oscillatorMode r τ (n + 2)) -
        scalarZ r τ * (constantMode r τ + oscillatorMode r τ (n + 1)) +
          scalarZ r τ * (constantMode r τ + oscillatorMode r τ n) := by
  rw [show n + 3 = (n + 1) + 2 by omega,
    show n + 2 = n + 2 by rfl]
  simp only [oscillatorMode]
  ring

theorem scalarDerivative_eq_modes
    {r τ : ℝ} (hz0 : 0 ≤ scalarZ r τ) (n : ℕ) :
    scalarDerivative r τ n = constantMode r τ + oscillatorMode r τ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with (_ | _ | _ | n)
      · simp [scalarDerivative, oscillatorMode]
      · simp [scalarDerivative, oscillatorMode]
      · rw [scalarDerivative, constantMode_add_oscillator_two hz0]
      · rw [scalarDerivative, ih n (by omega), ih (n + 1) (by omega),
          ih (n + 2) (by omega)]
        exact (modelDerivative_rec r τ n).symm

theorem constantMode_mem_unit
    {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    0 ≤ constantMode r τ ∧ constantMode r τ ≤ 1 := by
  obtain ⟨hz0, hz1⟩ := scalarZ_mem_unit hr0 hr1 hτ0 hτ1
  have hm0 : 0 ≤ scalarM r := by unfold scalarM; positivity
  have hm1 : scalarM r ≤ 1 / 3 := by unfold scalarM; linarith
  have hden : 0 < 1 + scalarZ r τ := by linarith
  unfold constantMode
  constructor
  · exact div_nonneg (by positivity) hden.le
  · apply (div_le_one hden).2
    nlinarith [sq_nonneg (scalarM r)]

theorem abs_oscillatorMode_le_one
    {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    |oscillatorMode r τ n| ≤ 1 := by
  obtain ⟨hz0, hz1⟩ := scalarZ_mem_unit hr0 hr1 hτ0 hτ1
  obtain ⟨hα0, hα1⟩ := constantMode_mem_unit hr0 hr1 hτ0 hτ1
  have hm0 : 0 ≤ scalarM r := by unfold scalarM; positivity
  have hm1 : scalarM r ≤ 1 / 3 := by unfold scalarM; linarith
  have hzQuarter : scalarZ r τ ≤ 1 / 4 := by
    unfold scalarZ
    have hbracket0 : 0 ≤ 3 - 2 * r - r ^ 2 := by nlinarith
    have hbracket1 : 3 - 2 * r - r ^ 2 ≤ 3 := by nlinarith
    have hmul : τ * (3 - 2 * r - r ^ 2) ≤ 3 := by
      nlinarith [mul_le_mul hτ1 hbracket1 hbracket0
        (by norm_num : (0 : ℝ) ≤ 1)]
    nlinarith
  have hp1 : |-scalarM r - constantMode r τ| ≤ 1 := by
    have hαsmall : constantMode r τ ≤ 2 / 3 := by
      unfold constantMode
      have hden : 0 < 1 + scalarZ r τ := by linarith
      apply (div_le_iff₀ hden).2
      have hmprod : 0 ≤ scalarM r * (1 / 3 - scalarM r) :=
        mul_nonneg hm0 (by linarith)
      nlinarith
    rw [abs_of_nonpos (by linarith)]
    linarith
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with (_ | _ | n)
      · rw [oscillatorMode, abs_of_nonneg (by linarith)]
        linarith
      · simpa [oscillatorMode] using hp1
      · rw [oscillatorMode, abs_mul, abs_neg, abs_of_nonneg hz0]
        have hn := ih n (by omega)
        nlinarith [mul_le_mul hz1 hn (abs_nonneg _)
          (by norm_num : (0 : ℝ) ≤ 1)]

/-- Sharp enough uniform spectral bound for the degree-70 tail estimate. -/
theorem abs_scalarDerivative_le_two
    {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    |scalarDerivative r τ n| ≤ 2 := by
  obtain ⟨hz0, _hz1⟩ := scalarZ_mem_unit hr0 hr1 hτ0 hτ1
  rw [scalarDerivative_eq_modes hz0]
  calc
    |constantMode r τ + oscillatorMode r τ n| ≤
        |constantMode r τ| + |oscillatorMode r τ n| := abs_add_le _ _
    _ ≤ 1 + 1 := add_le_add
      (by
        obtain ⟨h0, h1⟩ := constantMode_mem_unit hr0 hr1 hτ0 hτ1
        simpa [abs_of_nonneg h0] using h1)
      (abs_oscillatorMode_le_one hr0 hr1 hτ0 hτ1 n)
    _ = 2 := by norm_num

end SSP.K3CyclicComplex.PositiveCoeff
