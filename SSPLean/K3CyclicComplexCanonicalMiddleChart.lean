import SSPLean.K3CyclicComplexCanonicalMiddleBridge

/-! # Canonical inequalities for the complex middle chart -/

set_option autoImplicit false

namespace SSP.K3Cyclic

open SSP.K3CyclicComplex.MiddleCoeff

/-- The ordered nonnegative canonical diagonal parameters force the normalized
middle coefficient into the exact compact interval used by the certificate. -/
theorem canonical_middleChart_interval
    {a b mu d rhoValue AValue : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : a ≤ b)
    (hd : 0 < d)
    (hrho0 : 0 ≤ rhoValue)
    (hsum : a + b = 3 * mu + d)
    (hpair : a * b = 3 * mu ^ 2 + 2 * mu * d +
      d ^ 2 * scalarZ rhoValue)
    (ha : a = 2 * mu + d * AValue) :
    2 * (1 - rhoValue) / 3 ≤ AValue ∧
      AValue ≤ (2 - rhoValue) / 3 := by
  have hb : b = mu + d - d * AValue := by
    linarith [hsum, ha]
  have hpair' := hpair
  rw [ha, hb] at hpair'
  unfold scalarZ at hpair'
  have hlowIdentity :
      4 * d ^ 2 * rhoValue ^ 2 =
        d ^ 2 * (2 - 3 * AValue) ^ 2 + 3 * a ^ 2 := by
    rw [ha]
    nlinarith [hpair']
  have hupperIdentity :
      d ^ 2 * rhoValue ^ 2 - d ^ 2 * (2 - 3 * AValue) ^ 2 =
        3 * b * (a - b) := by
    rw [ha, hb]
    nlinarith [hpair']
  have hscaledLow : d * (2 - 3 * AValue) ≤ 2 * d * rhoValue := by
    have hx0 : 0 ≤ 2 * d * rhoValue := by positivity
    nlinarith [hlowIdentity,
      sq_nonneg (2 * d * rhoValue + d * (2 - 3 * AValue))]
  have hAupper0 : 0 ≤ 2 - 3 * AValue := by
    rw [ha] at ha0 hab
    rw [hb] at hb0 hab
    nlinarith
  have hscaledUpper : d * rhoValue ≤ d * (2 - 3 * AValue) := by
    have hprod : 3 * b * (a - b) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num) hb0) (sub_nonpos.mpr hab)
    have hx0 : 0 ≤ d * (2 - 3 * AValue) :=
      mul_nonneg hd.le hAupper0
    have hr0 : 0 ≤ d * rhoValue := mul_nonneg hd.le hrho0
    nlinarith [hupperIdentity,
      sq_nonneg (d * (2 - 3 * AValue) + d * rhoValue)]
  constructor <;> nlinarith

/-- Vieta data plus ordered canonical diagonals imply the actual canonical
middle-coordinate curvature inequality. -/
theorem canonicalMiddle_complex_middleCurvature3_nonneg_of_vieta
    {a b c x2 x3 mu d rhoValue AValue t : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : a ≤ b)
    (hd : 0 < d) (ht : 0 ≤ t)
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (hsum : a + b = 3 * mu + d)
    (hpair : a * b = 3 * mu ^ 2 + 2 * mu * d +
      d ^ 2 * scalarZ rhoValue)
    (hprod : c * x2 * x3 =
      (mu + d) * (mu ^ 2 + d ^ 2 * scalarZ rhoValue))
    (ha : a = 2 * mu + d * AValue) :
    0 ≤ middleCurvature3 t
      (canonicalMiddle a b c x2 x3 t)
      (canonicalMiddleDeriv a b c x2 x3 t)
      (canonicalMiddleDeriv2 a b c x2 x3 t) := by
  rcases canonical_middleChart_interval ha0 hb0 hab hd hrho0
    hsum hpair ha with ⟨hAlo, hAhi⟩
  exact canonicalMiddle_complex_middleCurvature3_nonneg_of_chart
    hrho0 hrho1 hAlo hAhi hd ht hsum hpair hprod ha

theorem complex_frequency_sq_le_one_third
    {a b mu d omega : ℝ} (hd : 0 < d)
    (hsum : a + b = 3 * mu + d)
    (hpair : a * b = 3 * mu ^ 2 + 2 * mu * d + d ^ 2 * omega ^ 2) :
    omega ^ 2 ≤ 1 / 3 := by
  have hdiscIdentity :
      (a - b) ^ 2 = d ^ 2 - 2 * mu * d - 3 * mu ^ 2 -
        4 * d ^ 2 * omega ^ 2 := by
    calc
      (a - b) ^ 2 = (a + b) ^ 2 - 4 * (a * b) := by ring
      _ = d ^ 2 - 2 * mu * d - 3 * mu ^ 2 -
          4 * d ^ 2 * omega ^ 2 := by rw [hsum, hpair]; ring
  have hscaled : d ^ 2 * omega ^ 2 ≤ d ^ 2 * (1 / 3 : ℝ) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (3 * mu + d)]
  exact le_of_mul_le_mul_left hscaled (sq_pos_of_pos hd)

theorem exists_middleChart_rho_of_frequency
    {omega : ℝ} (homega : omega ^ 2 ≤ 1 / 3) :
    ∃ rhoValue : ℝ, 0 ≤ rhoValue ∧ rhoValue ≤ 1 ∧
      scalarZ rhoValue = omega ^ 2 := by
  let rhoValue := Real.sqrt (1 - 3 * omega ^ 2)
  have hrad : 0 ≤ 1 - 3 * omega ^ 2 := by linarith
  have hrho0 : 0 ≤ rhoValue := by dsimp [rhoValue]; positivity
  have hrhoSq : rhoValue ^ 2 = 1 - 3 * omega ^ 2 := by
    dsimp [rhoValue]
    exact Real.sq_sqrt hrad
  have hrho1 : rhoValue ≤ 1 := by
    nlinarith [sq_nonneg (rhoValue - 1)]
  refine ⟨rhoValue, hrho0, hrho1, ?_⟩
  unfold scalarZ
  rw [hrhoSq]
  ring

/-- Fully normalized complex-pair form: the compact chart variables are
constructed from the Vieta frequency and the ordered canonical diagonals. -/
theorem canonicalMiddle_complexPair_middleCurvature3_nonneg
    {a b c x2 x3 mu d omega t : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : a ≤ b)
    (hd : 0 < d) (ht : 0 ≤ t)
    (hsum : a + b = 3 * mu + d)
    (hpair : a * b = 3 * mu ^ 2 + 2 * mu * d + d ^ 2 * omega ^ 2)
    (hprod : c * x2 * x3 =
      (mu + d) * (mu ^ 2 + d ^ 2 * omega ^ 2)) :
    0 ≤ middleCurvature3 t
      (canonicalMiddle a b c x2 x3 t)
      (canonicalMiddleDeriv a b c x2 x3 t)
      (canonicalMiddleDeriv2 a b c x2 x3 t) := by
  have homega := complex_frequency_sq_le_one_third hd hsum hpair
  obtain ⟨rhoValue, hrho0, hrho1, hrho⟩ :=
    exists_middleChart_rho_of_frequency homega
  let AValue := (a - 2 * mu) / d
  have ha : a = 2 * mu + d * AValue := by
    dsimp [AValue]
    field_simp [hd.ne']
    ring
  have hpair' : a * b = 3 * mu ^ 2 + 2 * mu * d +
      d ^ 2 * scalarZ rhoValue := by rw [hrho]; exact hpair
  have hprod' : c * x2 * x3 =
      (mu + d) * (mu ^ 2 + d ^ 2 * scalarZ rhoValue) := by
    rw [hrho]
    exact hprod
  exact canonicalMiddle_complex_middleCurvature3_nonneg_of_vieta
    ha0 hb0 hab hd ht hrho0 hrho1 hsum hpair' hprod' ha

end SSP.K3Cyclic
