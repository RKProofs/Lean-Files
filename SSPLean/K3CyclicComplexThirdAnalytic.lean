import SSPLean.K3CyclicComplexFirstAnalyticODE

/-! # Normalized analytic third coordinate for a complex spectral pair -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex

noncomputable def thirdJ (omega x : ℝ) : ℝ :=
  (Real.exp x - Real.cos (omega * x) - sinc omega x) /
    (1 + omega ^ 2)

noncomputable def thirdJ1 (omega x : ℝ) : ℝ :=
  (Real.exp x + omega * Real.sin (omega * x) -
    Real.cos (omega * x)) / (1 + omega ^ 2)

noncomputable def thirdJ2 (omega x : ℝ) : ℝ :=
  (Real.exp x + omega ^ 2 * Real.cos (omega * x) +
    omega * Real.sin (omega * x)) / (1 + omega ^ 2)

noncomputable def thirdJ3 (omega x : ℝ) : ℝ :=
  (Real.exp x - omega ^ 3 * Real.sin (omega * x) +
    omega ^ 2 * Real.cos (omega * x)) / (1 + omega ^ 2)

theorem thirdJ_hasDerivAt {omega x : ℝ} (homega : omega ≠ 0) :
    HasDerivAt (thirdJ omega) (thirdJ1 omega x) x := by
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (omega * y))
      (-Real.sin (omega * x) * omega) x := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_cos (omega * x)).comp x
        (hasDerivAt_const_mul omega)
  have h := ((Real.hasDerivAt_exp x).sub hcos).sub
    (sinc_hasDerivAt (ω := omega) (x := x) homega)
  convert h.div_const (1 + omega ^ 2) using 1
  all_goals try rfl
  unfold thirdJ1
  ring

theorem thirdJ1_hasDerivAt {omega x : ℝ} :
    HasDerivAt (thirdJ1 omega) (thirdJ2 omega x) x := by
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (omega * y))
      (Real.cos (omega * x) * omega) x := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_sin (omega * x)).comp x
        (hasDerivAt_const_mul omega)
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (omega * y))
      (-Real.sin (omega * x) * omega) x := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_cos (omega * x)).comp x
        (hasDerivAt_const_mul omega)
  have h := ((Real.hasDerivAt_exp x).add (hsin.const_mul omega)).sub hcos
  convert h.div_const (1 + omega ^ 2) using 1
  all_goals try rfl
  unfold thirdJ2
  ring

theorem thirdJ2_hasDerivAt {omega x : ℝ} :
    HasDerivAt (thirdJ2 omega) (thirdJ3 omega x) x := by
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (omega * y))
      (Real.cos (omega * x) * omega) x := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_sin (omega * x)).comp x
        (hasDerivAt_const_mul omega)
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (omega * y))
      (-Real.sin (omega * x) * omega) x := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_cos (omega * x)).comp x
        (hasDerivAt_const_mul omega)
  have h := ((Real.hasDerivAt_exp x).add
    (hcos.const_mul (omega ^ 2))).add (hsin.const_mul omega)
  convert h.div_const (1 + omega ^ 2) using 1
  all_goals try rfl
  unfold thirdJ3
  ring

theorem thirdJ_cubic_ode (omega x : ℝ) :
    thirdJ3 omega x = thirdJ2 omega x -
      omega ^ 2 * thirdJ1 omega x + omega ^ 2 * thirdJ omega x := by
  unfold thirdJ thirdJ1 thirdJ2 thirdJ3
  by_cases homega : omega = 0
  · subst omega
    simp [sinc]
  · rw [sinc_eq homega]
    field_simp [homega]
    ring

@[simp] theorem thirdJ_zero (omega : ℝ) : thirdJ omega 0 = 0 := by
  simp [thirdJ, sinc]

@[simp] theorem thirdJ1_zero (omega : ℝ) : thirdJ1 omega 0 = 0 := by
  simp [thirdJ1]

@[simp] theorem thirdJ2_zero (omega : ℝ) : thirdJ2 omega 0 = 1 := by
  simp [thirdJ2, one_add_sq_ne_zero]

end SSP.K3CyclicComplex
