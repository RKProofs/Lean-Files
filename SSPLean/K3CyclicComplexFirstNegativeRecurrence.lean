import SSPLean.K3CyclicComplexFirstCoefficientSemantics
import SSPLean.K3CyclicComplexFirstAnalyticODE

/-! # Scalar recurrence behind the negative-m complex-first certificate -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.NegativeCoeff

open SSP.K3CyclicComplex Dense

noncomputable def scalarM (r : ℝ) : ℝ := -r / 3

noncomputable def scalarZ (r τ : ℝ) : ℝ :=
  r * (2 - r) / 3 + τ * (1 - r) ^ 2 / 4

noncomputable def scalarTrace (r : ℝ) : ℝ := 1 - r

noncomputable def scalarPair (r τ : ℝ) : ℝ :=
  r ^ 2 / 3 - 2 * r / 3 + scalarZ r τ

noncomputable def scalarFeedback (r τ : ℝ) : ℝ :=
  (1 - r / 3) * (r ^ 2 / 9 + scalarZ r τ)

noncomputable def scalarDerivative (r τ : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | n + 3 => scalarTrace r * scalarDerivative r τ (n + 2) -
      scalarPair r τ * scalarDerivative r τ (n + 1) +
      scalarFeedback r τ * scalarDerivative r τ n

@[simp] theorem beval_trace (r τ : ℝ) :
    beval trace r τ = scalarTrace r := by
  simp [trace, bone, scalarTrace, beval_sub]

@[simp] theorem beval_z (r τ : ℝ) :
    beval z r τ = scalarZ r τ := by
  simp [z, bone, scalarZ, beval_add, beval_mul, beval_sub, beval_pow]
  ring

@[simp] theorem beval_pair (r τ : ℝ) :
    beval pair r τ = scalarPair r τ := by
  simp [pair, scalarPair, beval_add, beval_sub, beval_mul, beval_pow]
  ring

@[simp] theorem beval_feedback (r τ : ℝ) :
    beval feedback r τ = scalarFeedback r τ := by
  simp [feedback, bone, scalarFeedback, beval_add, beval_sub, beval_mul, beval_pow]
  ring

theorem derivativeTriple_eval (r τ : ℝ) (n : ℕ) :
    beval (derivativeTriple n).1 r τ = scalarDerivative r τ n ∧
      beval (derivativeTriple n).2.1 r τ = scalarDerivative r τ (n + 1) ∧
      beval (derivativeTriple n).2.2 r τ = scalarDerivative r τ (n + 2) := by
  induction n with
  | zero => simp [derivativeTriple, initialTriple, bone, bzero, scalarDerivative]
  | succ n ih =>
      rcases ih with ⟨ih0, ih1, ih2⟩
      simp only [derivativeTriple, nextTriple]
      refine ⟨ih1, ih2, ?_⟩
      rw [beval_add, beval_sub, beval_mul, beval_mul, beval_mul,
        beval_trace, beval_pair, beval_feedback, ih0, ih1, ih2]
      rw [show n + 1 + 2 = n + 3 by omega, scalarDerivative]

theorem derivativeValue_eq (r τ : ℝ) (n : ℕ) :
    derivativeValue r τ n = scalarDerivative r τ n := by
  exact (derivativeTriple_eval r τ n).1

theorem scalarZ_bounds
    {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    0 ≤ scalarZ r τ ∧ scalarZ r τ ≤ 1 / 3 ∧
      r * (2 - r) / 3 ≤ scalarZ r τ := by
  unfold scalarZ
  have hrGap : 0 ≤ r * (2 - r) := mul_nonneg hr0 (by linarith)
  have htGap : 0 ≤ τ * (1 - r) ^ 2 := by positivity
  have htUpper : τ * (1 - r) ^ 2 ≤ (1 - r) ^ 2 := by
    nlinarith [mul_le_mul hτ1 (le_refl ((1 - r) ^ 2))
      (sq_nonneg (1 - r)) (by norm_num : (0 : ℝ) ≤ 1)]
  constructor
  · exact add_nonneg (div_nonneg hrGap (by norm_num))
      (div_nonneg htGap (by norm_num))
  constructor
  · nlinarith [sq_nonneg (r - 1)]
  · exact le_add_of_nonneg_right (div_nonneg htGap (by norm_num))

noncomputable def spectralRadiusSq (r τ : ℝ) : ℝ :=
  scalarM r ^ 2 + scalarZ r τ

noncomputable def realRoot (r : ℝ) : ℝ := 1 + scalarM r

noncomputable def realMode (r τ : ℝ) : ℝ :=
  spectralRadiusSq r τ / (1 + scalarZ r τ)

noncomputable def oscillatorMode (r τ : ℝ) : ℕ → ℝ
  | 0 => 1 - realMode r τ
  | 1 => -realMode r τ * realRoot r
  | n + 2 => 2 * scalarM r * oscillatorMode r τ (n + 1) -
      spectralRadiusSq r τ * oscillatorMode r τ n

theorem one_add_scalarZ_ne_zero
    {r τ : ℝ} (hz0 : 0 ≤ scalarZ r τ) :
    1 + scalarZ r τ ≠ 0 := by linarith

theorem scalar_coefficients_factored (r τ : ℝ) :
    scalarTrace r = realRoot r + 2 * scalarM r ∧
    scalarPair r τ = spectralRadiusSq r τ +
      2 * realRoot r * scalarM r ∧
    scalarFeedback r τ = realRoot r * spectralRadiusSq r τ := by
  unfold scalarTrace scalarPair scalarFeedback realRoot spectralRadiusSq scalarM
  constructor
  · ring
  constructor <;> ring

theorem modelDerivative_zero_two
    {r τ : ℝ} (hz0 : 0 ≤ scalarZ r τ) :
    realMode r τ * realRoot r ^ 2 + oscillatorMode r τ 2 = 0 := by
  simp only [oscillatorMode]
  unfold realMode spectralRadiusSq realRoot
  field_simp [one_add_scalarZ_ne_zero hz0]
  ring

theorem modelDerivative_rec (r τ : ℝ) (n : ℕ) :
    realMode r τ * realRoot r ^ (n + 3) + oscillatorMode r τ (n + 3) =
      scalarTrace r *
          (realMode r τ * realRoot r ^ (n + 2) + oscillatorMode r τ (n + 2)) -
        scalarPair r τ *
          (realMode r τ * realRoot r ^ (n + 1) + oscillatorMode r τ (n + 1)) +
        scalarFeedback r τ *
          (realMode r τ * realRoot r ^ n + oscillatorMode r τ n) := by
  obtain ⟨htrace, hpair, hfeedback⟩ := scalar_coefficients_factored r τ
  have hosc : oscillatorMode r τ (n + 2) =
      2 * scalarM r * oscillatorMode r τ (n + 1) -
        spectralRadiusSq r τ * oscillatorMode r τ n := by
    rw [oscillatorMode]
  rw [show n + 3 = (n + 1) + 2 by omega, oscillatorMode,
    htrace, hpair, hfeedback, hosc]
  simp only [pow_succ]
  ring

theorem scalarDerivative_eq_modes
    {r τ : ℝ} (hz0 : 0 ≤ scalarZ r τ) (n : ℕ) :
    scalarDerivative r τ n =
      realMode r τ * realRoot r ^ n + oscillatorMode r τ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with (_ | _ | _ | n)
      · simp [scalarDerivative, oscillatorMode]
      · simp [scalarDerivative, oscillatorMode]
      · rw [scalarDerivative, modelDerivative_zero_two hz0]
      · rw [scalarDerivative, ih n (by omega), ih (n + 1) (by omega),
          ih (n + 2) (by omega)]
        exact (modelDerivative_rec r τ n).symm

noncomputable def oscillatorEnergy (r τ : ℝ) (n : ℕ) : ℝ :=
  scalarZ r τ * oscillatorMode r τ n ^ 2 +
    (oscillatorMode r τ (n + 1) -
      scalarM r * oscillatorMode r τ n) ^ 2

theorem oscillatorEnergy_succ (r τ : ℝ) (n : ℕ) :
    oscillatorEnergy r τ (n + 1) =
      spectralRadiusSq r τ * oscillatorEnergy r τ n := by
  unfold oscillatorEnergy
  rw [show n + 1 + 1 = n + 2 by omega, oscillatorMode]
  unfold spectralRadiusSq
  ring

theorem parameter_bounds
    {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    0 ≤ scalarZ r τ ∧ scalarZ r τ ≤ 1 / 3 ∧
    -(1 / 3 : ℝ) ≤ scalarM r ∧ scalarM r ≤ 0 ∧
    scalarM r ^ 2 ≤ scalarZ r τ ∧
    0 ≤ spectralRadiusSq r τ ∧ spectralRadiusSq r τ ≤ 1 := by
  obtain ⟨hz0, hz1, hzLower⟩ := scalarZ_bounds hr0 hr1 hτ0 hτ1
  have hm0 : -(1 / 3 : ℝ) ≤ scalarM r := by unfold scalarM; linarith
  have hm1 : scalarM r ≤ 0 := by unfold scalarM; linarith
  have hmSq : scalarM r ^ 2 ≤ scalarZ r τ := by
    unfold scalarM at *
    nlinarith [mul_nonneg hr0 (by linarith : 0 ≤ 1 - r)]
  have hrho0 : 0 ≤ spectralRadiusSq r τ := by
    unfold spectralRadiusSq
    positivity
  have hrho1 : spectralRadiusSq r τ ≤ 1 := by
    unfold spectralRadiusSq
    nlinarith [sq_nonneg (scalarM r + 1 / 3)]
  exact ⟨hz0, hz1, hm0, hm1, hmSq, hrho0, hrho1⟩

theorem realMode_bounds
    {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    0 ≤ realMode r τ ∧ realMode r τ ≤ 2 * scalarZ r τ ∧
      realMode r τ ≤ 2 / 3 := by
  obtain ⟨hz0, hz1, _hm0, _hm1, hmSq, _hrho0, _hrho1⟩ :=
    parameter_bounds hr0 hr1 hτ0 hτ1
  have hden : 0 < 1 + scalarZ r τ := by linarith
  have hrhoLe : spectralRadiusSq r τ ≤ 2 * scalarZ r τ := by
    unfold spectralRadiusSq
    linarith
  unfold realMode
  constructor
  · exact div_nonneg (by unfold spectralRadiusSq; positivity) hden.le
  constructor
  · apply (div_le_iff₀ hden).2
    nlinarith
  · apply (div_le_iff₀ hden).2
    nlinarith

theorem oscillatorEnergy_zero_le_six_z
    {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    oscillatorEnergy r τ 0 ≤ 6 * scalarZ r τ := by
  obtain ⟨hz0, _hz1, _hm0, _hm1, hmSq, _hrho0, _hrho1⟩ :=
    parameter_bounds hr0 hr1 hτ0 hτ1
  obtain ⟨hα0, hαz, hαupper⟩ := realMode_bounds hr0 hr1 hτ0 hτ1
  have hαsq : realMode r τ ^ 2 ≤ (4 / 3 : ℝ) * scalarZ r τ := by
    nlinarith [mul_nonneg hα0 (sub_nonneg.mpr hαupper)]
  have hpSq : (1 - realMode r τ) ^ 2 ≤ 1 := by
    have hα1 : realMode r τ ≤ 1 := by linarith
    nlinarith
  have hcross :
      (realMode r τ + scalarM r) ^ 2 ≤
        2 * realMode r τ ^ 2 + 2 * scalarM r ^ 2 := by
    nlinarith [sq_nonneg (realMode r τ - scalarM r)]
  unfold oscillatorEnergy
  simp only [oscillatorMode]
  have hcombo :
      -realMode r τ * realRoot r -
          scalarM r * (1 - realMode r τ) =
        -(realMode r τ + scalarM r) := by
    unfold realRoot
    ring
  rw [hcombo]
  have hzpart := mul_le_mul_of_nonneg_left hpSq hz0
  nlinarith

theorem oscillatorEnergy_le_six_z
    {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    oscillatorEnergy r τ n ≤ 6 * scalarZ r τ := by
  obtain ⟨hz0, _hz1, _hm0, _hm1, _hmSq, hrho0, hrho1⟩ :=
    parameter_bounds hr0 hr1 hτ0 hτ1
  induction n with
  | zero => exact oscillatorEnergy_zero_le_six_z hr0 hr1 hτ0 hτ1
  | succ n ih =>
      rw [oscillatorEnergy_succ]
      exact (mul_le_of_le_one_left
        (by positivity : 0 ≤ 6 * scalarZ r τ) hrho1).trans'
          (mul_le_mul_of_nonneg_left ih hrho0)

theorem abs_oscillatorMode_le_three
    {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    |oscillatorMode r τ n| ≤ 3 := by
  obtain ⟨hz0, _hz1, _hm0, _hm1, _hmSq, _hrho0, _hrho1⟩ :=
    parameter_bounds hr0 hr1 hτ0 hτ1
  by_cases hz : scalarZ r τ = 0
  · have hr : r = 0 := by
      unfold scalarZ at hz
      have hfirst : 0 ≤ r * (2 - r) / 3 := by
        exact div_nonneg (mul_nonneg hr0 (by linarith)) (by norm_num)
      have hsecond : 0 ≤ τ * (1 - r) ^ 2 / 4 := by positivity
      have : r * (2 - r) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with hr | hr
      · exact hr
      · linarith
    subst r
    rcases n with (_ | _ | n)
    · simp [oscillatorMode, realMode, spectralRadiusSq, scalarM, hz]
    · simp [oscillatorMode, realMode, spectralRadiusSq, scalarM, hz]
    · simp [oscillatorMode, realMode, spectralRadiusSq, scalarM, hz]
  · have hzpos : 0 < scalarZ r τ := lt_of_le_of_ne hz0 (Ne.symm hz)
    have henergy := oscillatorEnergy_le_six_z hr0 hr1 hτ0 hτ1 n
    have hcomponent :
        scalarZ r τ * oscillatorMode r τ n ^ 2 ≤
          oscillatorEnergy r τ n := by
      unfold oscillatorEnergy
      nlinarith [sq_nonneg (oscillatorMode r τ (n + 1) -
        scalarM r * oscillatorMode r τ n)]
    have hsquare : oscillatorMode r τ n ^ 2 ≤ 6 := by
      nlinarith
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (oscillatorMode r τ n - 3),
      sq_nonneg (oscillatorMode r τ n + 3)]

theorem abs_scalarDerivative_le_four
    {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    |scalarDerivative r τ n| ≤ 4 := by
  obtain ⟨hz0, _hz1, hm0, hm1, _hmSq, _hrho0, _hrho1⟩ :=
    parameter_bounds hr0 hr1 hτ0 hτ1
  obtain ⟨hα0, _hαz, hα1⟩ := realMode_bounds hr0 hr1 hτ0 hτ1
  have ha0 : 0 ≤ realRoot r := by unfold realRoot; linarith
  have ha1 : realRoot r ≤ 1 := by unfold realRoot; linarith
  rw [scalarDerivative_eq_modes hz0]
  calc
    |realMode r τ * realRoot r ^ n + oscillatorMode r τ n| ≤
        |realMode r τ * realRoot r ^ n| + |oscillatorMode r τ n| :=
      abs_add_le _ _
    _ ≤ 1 + 3 := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg hα0, abs_of_nonneg (pow_nonneg ha0 n)]
        have hpow : realRoot r ^ n ≤ 1 := by
          simpa using (pow_le_one₀ ha0 ha1 : realRoot r ^ n ≤ 1)
        nlinarith
      · exact abs_oscillatorMode_le_three hr0 hr1 hτ0 hτ1 n
    _ = 4 := by norm_num

theorem abs_scalarDerivative_le_three_pow
    {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    |scalarDerivative r τ n| ≤ (3 : ℝ) ^ n := by
  rcases n with (_ | _ | _ | n)
  · simp [scalarDerivative]
  · simp [scalarDerivative]
  · simp [scalarDerivative]
  · have hfour := abs_scalarDerivative_le_four hr0 hr1 hτ0 hτ1 (n + 3)
    have hbase : (4 : ℝ) ≤ 3 ^ (n + 3) := by
      have hp : (1 : ℝ) ≤ 3 ^ n := by
        exact one_le_pow₀ (by norm_num)
      calc
        (4 : ℝ) ≤ 27 * 3 ^ n := by nlinarith
        _ = 3 ^ (n + 3) := by rw [pow_add]; norm_num; ring
    exact hfour.trans hbase

end SSP.K3CyclicComplex.NegativeCoeff
