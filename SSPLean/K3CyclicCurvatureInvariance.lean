import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Invariances of dimension-three corrected curvature

These algebraic identities justify the amplitude, time, and exponential
normalizations used in the three-state spectral reduction.
-/

set_option autoImplicit false

namespace SSP.K3Cyclic

/-- Pointwise corrected curvature for dimension three.  The arguments are a
function value and its first two derivatives at time `t`. -/
noncomputable def correctedCurvature3
    (t f f1 f2 : ℝ) : ℝ :=
  t ^ 2 * (f * f2 - f1 ^ 2) + 2 * f ^ 2

theorem correctedCurvature3_amplitude
    (q t f f1 f2 : ℝ) :
    correctedCurvature3 t (q * f) (q * f1) (q * f2) =
      q ^ 2 * correctedCurvature3 t f f1 f2 := by
  unfold correctedCurvature3
  ring

theorem correctedCurvature3_time_scale
    (a t f f1 f2 : ℝ) :
    correctedCurvature3 t f (a * f1) (a ^ 2 * f2) =
      correctedCurvature3 (a * t) f f1 f2 := by
  unfold correctedCurvature3
  ring

/-- Multiplication of a function by `exp (c t)` multiplies corrected
curvature by the positive factor `exp (2 c t)`. -/
theorem correctedCurvature3_exp_shift
    (c t f f1 f2 : ℝ) :
    correctedCurvature3 t
        (Real.exp (c * t) * f)
        (Real.exp (c * t) * (f1 + c * f))
        (Real.exp (c * t) * (f2 + 2 * c * f1 + c ^ 2 * f)) =
      Real.exp (2 * c * t) * correctedCurvature3 t f f1 f2 := by
  have hexp : Real.exp (2 * c * t) = Real.exp (c * t) ^ 2 := by
    rw [show 2 * c * t = c * t + c * t by ring, Real.exp_add, pow_two]
  rw [hexp]
  unfold correctedCurvature3
  ring

theorem correctedCurvature3_nonneg_of_amplitude
    {q t f f1 f2 : ℝ} (hcurv : 0 ≤ correctedCurvature3 t f f1 f2) :
    0 ≤ correctedCurvature3 t (q * f) (q * f1) (q * f2) := by
  rw [correctedCurvature3_amplitude]
  exact mul_nonneg (sq_nonneg q) hcurv

theorem correctedCurvature3_nonneg_of_time_scale
    {a t f f1 f2 : ℝ}
    (hcurv : 0 ≤ correctedCurvature3 (a * t) f f1 f2) :
    0 ≤ correctedCurvature3 t f (a * f1) (a ^ 2 * f2) := by
  rwa [correctedCurvature3_time_scale]

theorem correctedCurvature3_nonneg_of_exp_shift
    {c t f f1 f2 : ℝ} (hcurv : 0 ≤ correctedCurvature3 t f f1 f2) :
    0 ≤ correctedCurvature3 t
      (Real.exp (c * t) * f)
      (Real.exp (c * t) * (f1 + c * f))
      (Real.exp (c * t) * (f2 + 2 * c * f1 + c ^ 2 * f)) := by
  rw [correctedCurvature3_exp_shift]
  exact mul_nonneg (Real.exp_pos _).le hcurv

end SSP.K3Cyclic
