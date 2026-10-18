import SSPLean.K3CyclicCanonicalMiddle
import SSPLean.K3CyclicComplexMiddleAnalyticODE

/-! # Complex-spectrum canonical middle-coordinate bridge

This file identifies the actual middle coordinate of the canonical matrix
exponential with the normalized complex-middle exponential generating series.
The proof uses only the common scalar cubic ODE and its initial data.
-/

set_option autoImplicit false

namespace SSP.K3Cyclic

open SSP.K3CyclicComplex.MiddleCoeff

noncomputable def complexMiddleModel
    (q mu d rhoValue etaValue t : ℝ) : ℝ :=
  q * Real.exp (mu * t) * middleEgf rhoValue etaValue 0 (d * t)

noncomputable def complexMiddleModelDeriv
    (q mu d rhoValue etaValue t : ℝ) : ℝ :=
  q * Real.exp (mu * t) *
    (mu * middleEgf rhoValue etaValue 0 (d * t) +
      d * middleEgf rhoValue etaValue 1 (d * t))

noncomputable def complexMiddleModelDeriv2
    (q mu d rhoValue etaValue t : ℝ) : ℝ :=
  q * Real.exp (mu * t) *
    (mu ^ 2 * middleEgf rhoValue etaValue 0 (d * t) +
      2 * mu * d * middleEgf rhoValue etaValue 1 (d * t) +
      d ^ 2 * middleEgf rhoValue etaValue 2 (d * t))

theorem complexMiddleModel_hasDerivAt
    {q mu d rhoValue etaValue t : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) :
    HasDerivAt (complexMiddleModel q mu d rhoValue etaValue)
      (complexMiddleModelDeriv q mu d rhoValue etaValue t) t := by
  have he := Real.hasDerivAt_exp (mu * t)
  have harg : HasDerivAt (fun u : ℝ => d * u) d t :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul d
  have hF := (middleEgf_hasDerivAt hrho0 hrho1 heta0 heta1 0).comp t harg
  have h := ((he.comp t ((hasDerivAt_id t).const_mul mu)).mul hF).const_mul q
  convert h using 1
  all_goals try rfl
  · funext y
    dsimp [complexMiddleModel, Function.comp_def]
    ring
  · dsimp [complexMiddleModelDeriv]
    ring

theorem complexMiddleModelDeriv_hasDerivAt
    {q mu d rhoValue etaValue t : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) :
    HasDerivAt (complexMiddleModelDeriv q mu d rhoValue etaValue)
      (complexMiddleModelDeriv2 q mu d rhoValue etaValue t) t := by
  have he := Real.hasDerivAt_exp (mu * t)
  have harg : HasDerivAt (fun u : ℝ => d * u) d t :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul d
  have hF0 := (middleEgf_hasDerivAt hrho0 hrho1 heta0 heta1 0).comp t harg
  have hF1 := (middleEgf_hasDerivAt hrho0 hrho1 heta0 heta1 1).comp t harg
  have hinside := (hF0.const_mul mu).add (hF1.const_mul d)
  have h := ((he.comp t ((hasDerivAt_id t).const_mul mu)).mul hinside).const_mul q
  convert h using 1
  all_goals try rfl
  · funext y
    dsimp [complexMiddleModelDeriv, Function.comp_def]
    ring
  · dsimp [complexMiddleModelDeriv2]
    ring

theorem complexMiddleModelDeriv2_hasDerivAt
    {q mu d rhoValue etaValue t : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) :
    HasDerivAt (complexMiddleModelDeriv2 q mu d rhoValue etaValue)
      (q * Real.exp (mu * t) *
        (mu ^ 3 * middleEgf rhoValue etaValue 0 (d * t) +
          3 * mu ^ 2 * d * middleEgf rhoValue etaValue 1 (d * t) +
          3 * mu * d ^ 2 * middleEgf rhoValue etaValue 2 (d * t) +
          d ^ 3 * middleEgf rhoValue etaValue 3 (d * t))) t := by
  have he := Real.hasDerivAt_exp (mu * t)
  have harg : HasDerivAt (fun u : ℝ => d * u) d t :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul d
  have hF0 := (middleEgf_hasDerivAt hrho0 hrho1 heta0 heta1 0).comp t harg
  have hF1 := (middleEgf_hasDerivAt hrho0 hrho1 heta0 heta1 1).comp t harg
  have hF2 := (middleEgf_hasDerivAt hrho0 hrho1 heta0 heta1 2).comp t harg
  have hinside :=
    ((hF0.const_mul (mu ^ 2)).add
      (hF1.const_mul (2 * mu * d))).add
        (hF2.const_mul (d ^ 2))
  have h := ((he.comp t ((hasDerivAt_id t).const_mul mu)).mul hinside).const_mul q
  convert h using 1
  all_goals try rfl
  · funext y
    dsimp [complexMiddleModelDeriv2, Function.comp_def]
    ring
  · simp only [Function.comp_apply, Pi.add_apply, Nat.zero_add, Nat.reduceAdd,
      mul_one]
    ring

@[simp] theorem scalarDerivative_zero (rhoValue etaValue : ℝ) :
    scalarDerivative rhoValue etaValue 0 = 0 := by
  norm_num [scalarDerivative, scalarA, scalarB, cosineSign, sineSign]

@[simp] theorem scalarDerivative_one (rhoValue etaValue : ℝ) :
    scalarDerivative rhoValue etaValue 1 = 1 + scalarZ rhoValue := by
  norm_num [scalarDerivative, scalarA, scalarB, cosineSign, sineSign]
  ring

@[simp] theorem scalarDerivative_two (rhoValue etaValue : ℝ) :
    scalarDerivative rhoValue etaValue 2 =
      scalarA rhoValue etaValue * (1 + scalarZ rhoValue) := by
  norm_num [scalarDerivative, scalarA, scalarB, cosineSign, sineSign]

theorem complexMiddleModelDeriv2_hasDerivAt_cubic
    {a b c x2 x3 q mu d rhoValue etaValue t : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1)
    (hsum : a + b = 3 * mu + d)
    (hpair : a * b = 3 * mu ^ 2 + 2 * mu * d +
      d ^ 2 * scalarZ rhoValue)
    (hprod : c * x2 * x3 =
      (mu + d) * (mu ^ 2 + d ^ 2 * scalarZ rhoValue)) :
    HasDerivAt (complexMiddleModelDeriv2 q mu d rhoValue etaValue)
      ((c * x2 * x3) * complexMiddleModel q mu d rhoValue etaValue t -
        a * b * complexMiddleModelDeriv q mu d rhoValue etaValue t +
          (a + b) * complexMiddleModelDeriv2 q mu d rhoValue etaValue t) t := by
  have hraw := complexMiddleModelDeriv2_hasDerivAt
    (q := q) (mu := mu) (d := d) (t := t)
    hrho0 hrho1 heta0 heta1
  convert hraw using 1
  rw [middleEgf_cubic_ode hrho0 hrho1 heta0 heta1,
    hsum, hpair, hprod]
  dsimp [complexMiddleModel, complexMiddleModelDeriv,
    complexMiddleModelDeriv2]
  ring

/-- The actual canonical middle coordinate is the shifted and time-scaled
complex-middle EGF whenever the normalized spectral identities and initial
amplitude identities hold. -/
theorem canonicalMiddle_eq_complexMiddleModel
    {a b c x2 x3 q mu d rhoValue etaValue : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1)
    (hsum : a + b = 3 * mu + d)
    (hpair : a * b = 3 * mu ^ 2 + 2 * mu * d +
      d ^ 2 * scalarZ rhoValue)
    (hprod : c * x2 * x3 =
      (mu + d) * (mu ^ 2 + d ^ 2 * scalarZ rhoValue))
    (hscale : q * d * (1 + scalarZ rhoValue) = x2)
    (ha : a = 2 * mu + d * scalarA rhoValue etaValue) :
    canonicalMiddle a b c x2 x3 =
      complexMiddleModel q mu d rhoValue etaValue := by
  apply SSP.CubicODE.eq_of_cubic_ode
    (c0 := c * x2 * x3) (c1 := -(a * b)) (c2 := a + b) (t0 := 0)
    (fun t => canonicalMiddle_hasDerivAt a b c x2 x3 t)
    (fun t => canonicalMiddleDeriv_hasDerivAt a b c x2 x3 t)
    (fun t => by
      convert canonicalMiddleDeriv2_hasDerivAt a b c x2 x3 t using 1; ring)
    (fun t => complexMiddleModel_hasDerivAt hrho0 hrho1 heta0 heta1)
    (fun t => complexMiddleModelDeriv_hasDerivAt hrho0 hrho1 heta0 heta1)
    (fun t => by
      convert complexMiddleModelDeriv2_hasDerivAt_cubic
        hrho0 hrho1 heta0 heta1 hsum hpair hprod using 1; ring)
  · simp [complexMiddleModel,
      middleEgf_zero hrho0 hrho1 heta0 heta1]
  · simp [complexMiddleModelDeriv,
      middleEgf_zero hrho0 hrho1 heta0 heta1]
    simpa only [mul_assoc] using hscale.symm
  · simp only [canonicalMiddleDeriv2_zero, complexMiddleModelDeriv2, mul_zero,
      Real.exp_zero, mul_one, middleEgf_zero hrho0 hrho1 heta0 heta1,
      scalarDerivative_zero, scalarDerivative_one, zero_add, scalarDerivative_two]
    rw [← hscale, ha]
    ring

/-! ## Transport of the stronger middle curvature -/

noncomputable def middleCurvature3 (t f f1 f2 : ℝ) : ℝ :=
  t ^ 2 * (f * f2 - f1 ^ 2) + f ^ 2

theorem middleCurvature3_complexMiddleModel
    (q mu d rhoValue etaValue t : ℝ) :
    middleCurvature3 t
        (complexMiddleModel q mu d rhoValue etaValue t)
        (complexMiddleModelDeriv q mu d rhoValue etaValue t)
        (complexMiddleModelDeriv2 q mu d rhoValue etaValue t) =
      q ^ 2 * Real.exp (2 * mu * t) *
        ((d * t) ^ 2 *
            (middleEgf rhoValue etaValue 0 (d * t) *
                middleEgf rhoValue etaValue 2 (d * t) -
              middleEgf rhoValue etaValue 1 (d * t) ^ 2) +
          middleEgf rhoValue etaValue 0 (d * t) ^ 2) := by
  have hexp : Real.exp (2 * mu * t) = Real.exp (mu * t) ^ 2 := by
    rw [show 2 * mu * t = mu * t + mu * t by ring, Real.exp_add, pow_two]
  rw [hexp]
  unfold middleCurvature3 complexMiddleModel complexMiddleModelDeriv
    complexMiddleModelDeriv2
  ring

theorem complexMiddleModel_middleCurvature3_nonneg
    {q mu d rhoValue etaValue t : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1)
    (hd : 0 ≤ d) (ht : 0 ≤ t) :
    0 ≤ middleCurvature3 t
      (complexMiddleModel q mu d rhoValue etaValue t)
      (complexMiddleModelDeriv q mu d rhoValue etaValue t)
      (complexMiddleModelDeriv2 q mu d rhoValue etaValue t) := by
  rw [middleCurvature3_complexMiddleModel]
  exact mul_nonneg
    (mul_nonneg (sq_nonneg q) (Real.exp_pos _).le)
    (middleEgf_curvature_nonneg hrho0 hrho1 heta0 heta1
      (mul_nonneg hd ht))

theorem canonicalMiddle_complex_middleCurvature3_nonneg
    {a b c x2 x3 q mu d rhoValue etaValue t : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1)
    (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hsum : a + b = 3 * mu + d)
    (hpair : a * b = 3 * mu ^ 2 + 2 * mu * d +
      d ^ 2 * scalarZ rhoValue)
    (hprod : c * x2 * x3 =
      (mu + d) * (mu ^ 2 + d ^ 2 * scalarZ rhoValue))
    (hscale : q * d * (1 + scalarZ rhoValue) = x2)
    (ha : a = 2 * mu + d * scalarA rhoValue etaValue) :
    0 ≤ middleCurvature3 t
      (canonicalMiddle a b c x2 x3 t)
      (canonicalMiddleDeriv a b c x2 x3 t)
      (canonicalMiddleDeriv2 a b c x2 x3 t) := by
  have hEq := canonicalMiddle_eq_complexMiddleModel
    hrho0 hrho1 heta0 heta1 hsum hpair hprod hscale ha
  have h0 := congrFun hEq t
  have h1 : canonicalMiddleDeriv a b c x2 x3 t =
      complexMiddleModelDeriv q mu d rhoValue etaValue t := by
    have hc := canonicalMiddle_hasDerivAt a b c x2 x3 t
    have hm := complexMiddleModel_hasDerivAt
      (q := q) (mu := mu) (d := d) (t := t)
      hrho0 hrho1 heta0 heta1
    rw [hEq] at hc
    exact hc.unique hm
  have h2 : canonicalMiddleDeriv2 a b c x2 x3 t =
      complexMiddleModelDeriv2 q mu d rhoValue etaValue t := by
    have hc := canonicalMiddleDeriv_hasDerivAt a b c x2 x3 t
    have hm := complexMiddleModelDeriv_hasDerivAt
      (q := q) (mu := mu) (d := d) (t := t)
      hrho0 hrho1 heta0 heta1
    have hfun : canonicalMiddleDeriv a b c x2 x3 =
        complexMiddleModelDeriv q mu d rhoValue etaValue := by
      funext u
      have hcu := canonicalMiddle_hasDerivAt a b c x2 x3 u
      have hmu := complexMiddleModel_hasDerivAt
        (q := q) (mu := mu) (d := d) (t := u)
        hrho0 hrho1 heta0 heta1
      rw [hEq] at hcu
      exact hcu.unique hmu
    rw [hfun] at hc
    exact hc.unique hm
  rw [h0, h1, h2]
  exact complexMiddleModel_middleCurvature3_nonneg
    hrho0 hrho1 heta0 heta1 hd ht

/-- The affine middle chart fills exactly the interval used by the complex
middle certificate. -/
theorem exists_middleChart_eta
    {rhoValue AValue : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (hAlo : 2 * (1 - rhoValue) / 3 ≤ AValue)
    (hAhi : AValue ≤ (2 - rhoValue) / 3) :
    ∃ etaValue : ℝ, 0 ≤ etaValue ∧ etaValue ≤ 1 ∧
      scalarA rhoValue etaValue = AValue := by
  by_cases hrho : rhoValue = 0
  · subst rhoValue
    refine ⟨0, by norm_num, by norm_num, ?_⟩
    unfold scalarA
    norm_num at hAlo hAhi ⊢
    linarith
  · have hrhoPos : 0 < rhoValue := lt_of_le_of_ne hrho0 (Ne.symm hrho)
    let etaValue := (3 * AValue - 2 + 2 * rhoValue) / rhoValue
    refine ⟨etaValue, ?_, ?_, ?_⟩
    · dsimp [etaValue]
      exact div_nonneg (by linarith) hrhoPos.le
    · apply (div_le_one hrhoPos).2
      linarith
    · unfold scalarA
      dsimp [etaValue]
      field_simp [hrho]
      ring

/-- Public chart form of the complex-spectrum middle theorem.  The nuisance
amplitude and affine-chart coordinate are constructed internally. -/
theorem canonicalMiddle_complex_middleCurvature3_nonneg_of_chart
    {a b c x2 x3 mu d rhoValue AValue t : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (hAlo : 2 * (1 - rhoValue) / 3 ≤ AValue)
    (hAhi : AValue ≤ (2 - rhoValue) / 3)
    (hd : 0 < d) (ht : 0 ≤ t)
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
  obtain ⟨etaValue, heta0, heta1, hetaA⟩ :=
    exists_middleChart_eta hrho0 hrho1 hAlo hAhi
  let q := x2 / (d * (1 + scalarZ rhoValue))
  have hz0 : 0 ≤ scalarZ rhoValue := by
    unfold scalarZ
    nlinarith [mul_nonneg hrho0 (sub_nonneg.mpr hrho1)]
  have hden : d * (1 + scalarZ rhoValue) ≠ 0 := by positivity
  have hscale : q * d * (1 + scalarZ rhoValue) = x2 := by
    dsimp [q]
    field_simp
  apply canonicalMiddle_complex_middleCurvature3_nonneg
    hrho0 hrho1 heta0 heta1 hd.le ht hsum hpair hprod hscale
  rw [hetaA]
  exact ha

end SSP.K3Cyclic
