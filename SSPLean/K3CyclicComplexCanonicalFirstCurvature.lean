import SSPLean.K3CyclicComplexCanonicalFirstBridge
import SSPLean.K3CyclicComplexFirstFull

/-! # Complex-spectrum curvature for the actual canonical first coordinate -/

set_option autoImplicit false

namespace SSP.K3Cyclic

open SSP.K3CyclicComplex

theorem shiftedFirstF_correctedCurvature3_nonneg
    {m omega x : ℝ} (hdom : FirstDomain m omega)
    (hx : 0 ≤ x) (homega : omega ≠ 0) :
    0 ≤ correctedCurvature3 x
      (shiftedFirstF m omega x) (shiftedFirstF1 m omega x)
      (shiftedFirstF2 m omega x) := by
  have hH := firstH_correctedCurvature3_nonneg hdom hx homega
  have hscale := correctedCurvature3_nonneg_of_amplitude
    (q := 1 / (1 + omega ^ 2)) hH
  have hF : 0 ≤ correctedCurvature3 x
      (firstF m omega x) (firstF1 m omega x) (firstF2 m omega x) := by
    convert hscale using 1;
      simp [firstF, firstF1, firstF2, div_eq_mul_inv, mul_comm]
  rw [shiftedFirstF_correctedCurvature3_eq]
  exact mul_nonneg (Real.exp_pos _).le hF

theorem complexFirstModel_correctedCurvature3_nonneg
    {m omega d t : ℝ} (hdom : FirstDomain m omega)
    (hd : 0 ≤ d) (ht : 0 ≤ t) (homega : omega ≠ 0) :
    0 ≤ correctedCurvature3 t
      (complexFirstModel m omega d t)
      (complexFirstModelDeriv m omega d t)
      (complexFirstModelDeriv2 m omega d t) := by
  rw [show correctedCurvature3 t
      (complexFirstModel m omega d t)
      (complexFirstModelDeriv m omega d t)
      (complexFirstModelDeriv2 m omega d t) =
      correctedCurvature3 (d * t)
        (shiftedFirstF m omega (d * t))
        (shiftedFirstF1 m omega (d * t))
        (shiftedFirstF2 m omega (d * t)) by
    unfold complexFirstModel complexFirstModelDeriv complexFirstModelDeriv2
    exact correctedCurvature3_time_scale d t _ _ _]
  exact shiftedFirstF_correctedCurvature3_nonneg hdom
    (mul_nonneg hd ht) homega

theorem canonicalFirst_complexPair_correctedCurvature3_nonneg
    {a b c x2 x3 m omega d t : ℝ}
    (hdom : FirstDomain m omega) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (homega : omega ≠ 0)
    (hsum : a + b = d * (1 + 3 * m))
    (hpair : a * b = d ^ 2 * (3 * m ^ 2 + 2 * m + omega ^ 2))
    (hprod : c * x2 * x3 =
      d ^ 3 * ((1 + m) * (m ^ 2 + omega ^ 2))) :
    0 ≤ correctedCurvature3 t
      (canonicalFirst a b c x2 x3 t)
      (canonicalFirstDeriv a b c x2 x3 t)
      (canonicalFirstDeriv2 a b c x2 x3 t) := by
  have hEq := canonicalFirst_eq_complexFirstModel homega hsum hpair hprod
  have h0 := congrFun hEq t
  have h1 : canonicalFirstDeriv a b c x2 x3 t =
      complexFirstModelDeriv m omega d t := by
    have hc := canonicalFirst_hasDerivAt a b c x2 x3 t
    have hm := complexFirstModel_hasDerivAt
      (m := m) (omega := omega) (d := d) (t := t) homega
    rw [hEq] at hc
    exact hc.unique hm
  have hfun : canonicalFirstDeriv a b c x2 x3 =
      complexFirstModelDeriv m omega d := by
    funext u
    have hc := canonicalFirst_hasDerivAt a b c x2 x3 u
    have hm := complexFirstModel_hasDerivAt
      (m := m) (omega := omega) (d := d) (t := u) homega
    rw [hEq] at hc
    exact hc.unique hm
  have h2 : canonicalFirstDeriv2 a b c x2 x3 t =
      complexFirstModelDeriv2 m omega d t := by
    have hc := canonicalFirstDeriv_hasDerivAt a b c x2 x3 t
    have hm := complexFirstModelDeriv_hasDerivAt
      (m := m) (omega := omega) (d := d) (t := t) homega
    rw [hfun] at hc
    exact hc.unique hm
  rw [h0, h1, h2]
  exact complexFirstModel_correctedCurvature3_nonneg hdom hd ht homega

theorem canonical_complexPair_firstDomain
    {a b m omega d : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hd : 0 < d)
    (hsum : a + b = d * (1 + 3 * m))
    (hpair : a * b = d ^ 2 * (3 * m ^ 2 + 2 * m + omega ^ 2)) :
    FirstDomain m omega := by
  have hsum0 : 0 ≤ d * (1 + 3 * m) := by
    rw [← hsum]
    exact add_nonneg ha0 hb0
  have hmLower : -(1 / 3 : ℝ) ≤ m := by
    have : 0 ≤ 1 + 3 * m := nonneg_of_mul_nonneg_left
      (by simpa [mul_comm] using hsum0) hd
    linarith
  have hpair0 : 0 ≤ d ^ 2 * (3 * m ^ 2 + 2 * m + omega ^ 2) := by
    rw [← hpair]
    exact mul_nonneg ha0 hb0
  have hspectralLower : 0 ≤ 3 * m ^ 2 + 2 * m + omega ^ 2 :=
    nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hpair0)
      (sq_pos_of_pos hd)
  have hdiscIdentity :
      (a - b) ^ 2 =
        d ^ 2 * (1 - 2 * m - 3 * m ^ 2 - 4 * omega ^ 2) := by
    calc
      (a - b) ^ 2 = (a + b) ^ 2 - 4 * (a * b) := by ring
      _ = d ^ 2 * (1 - 2 * m - 3 * m ^ 2 - 4 * omega ^ 2) := by
        rw [hsum, hpair]
        ring
  have hdiscScaled :
      0 ≤ d ^ 2 * (1 - 2 * m - 3 * m ^ 2 - 4 * omega ^ 2) := by
    rw [← hdiscIdentity]
    exact sq_nonneg (a - b)
  have hdisc : 0 ≤ 1 - 2 * m - 3 * m ^ 2 - 4 * omega ^ 2 :=
    nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hdiscScaled)
      (sq_pos_of_pos hd)
  have hmUpper : m ≤ 1 / 3 := by
    nlinarith [sq_nonneg omega]
  refine ⟨hmLower, hmUpper, sq_nonneg omega, ?_, ?_⟩
  · linarith
  · linarith

/-- Actual complex first-start inequality with only canonical sign and Vieta
hypotheses. -/
theorem canonicalFirst_complexPair_correctedCurvature3_nonneg_of_vieta
    {a b c x2 x3 m omega d t : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hd : 0 < d) (ht : 0 ≤ t)
    (homega : omega ≠ 0)
    (hsum : a + b = d * (1 + 3 * m))
    (hpair : a * b = d ^ 2 * (3 * m ^ 2 + 2 * m + omega ^ 2))
    (hprod : c * x2 * x3 =
      d ^ 3 * ((1 + m) * (m ^ 2 + omega ^ 2))) :
    0 ≤ correctedCurvature3 t
      (canonicalFirst a b c x2 x3 t)
      (canonicalFirstDeriv a b c x2 x3 t)
      (canonicalFirstDeriv2 a b c x2 x3 t) := by
  exact canonicalFirst_complexPair_correctedCurvature3_nonneg
    (canonical_complexPair_firstDomain ha0 hb0 hd hsum hpair)
    hd.le ht homega hsum hpair hprod

end SSP.K3Cyclic
