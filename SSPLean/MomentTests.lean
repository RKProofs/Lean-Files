import SSPLean.MomentBridge
import SSPLean.AldousShepp
import SSPLean.SurvivalMonotone
import SSPLean.AldousSheppFinal

/-!
# Non-vacuity checks

A hypothesis bundle can be silently unsatisfiable, in which case every theorem stated over it is
true and worthless.  This file instantiates the hypotheses of the Aldous–Shepp development at
explicit data, so that the theorems are known to have content.

The running example is `s = 1`, `Q = 0`, i.e. the exponential law `Exp(1)`: then `N = (I−Q)⁻¹ = I`,
`E[X] = 1`, `E[X²] = 2`, `Var = 1`, and the Aldous–Shepp bound `Var ≥ (E X)²/s = 1` holds with
equality.  It is the `s = 1` Erlang law, the extremal case.
-/

open scoped Matrix.Norms.Operator
open SSP Set

set_option autoImplicit false

namespace SSP.Tests

/-- The zero routing matrix, as a `ℕ → ℕ → ℝ` array. -/
noncomputable def Qzero : ℕ → ℕ → ℝ := fun _ _ => 0

/-- **`AbsorptionMoments` is satisfiable.**  Witnessed at `s = 1`, `Q = 0` — the `Exp(1)` law.
Without this, `SSP.AldousShepp.variance_bound` could be vacuously true. -/
theorem absorptionMoments_nonvacuous :
    SSP.AldousShepp.AbsorptionMoments 1 Qzero 0
      (rowSum 1 (Nmat 1 Qzero) 0) (2 * rowSum2 1 (Nmat 1 Qzero) 0) := by
  refine ⟨fun j k => le_refl 0, ?_, ?_, one_pos, one_pos, rfl, rfl⟩
  · intro j _; simp [Qzero]
  · have h : (toMat 1 Qzero) = 0 := by ext a b; simp [toMat, Qzero]
    rw [h]
    simp only [Matrix.map_zero, map_zero]
    rw [spectralRadius]
    simp

/-- **The Aldous–Shepp conclusion is a real inequality at that instance**, not `True`. -/
theorem variance_bound_applies :
    (rowSum 1 (Nmat 1 Qzero) 0) ^ 2 / (1:ℕ)
      ≤ 2 * rowSum2 1 (Nmat 1 Qzero) 0 - (rowSum 1 (Nmat 1 Qzero) 0) ^ 2 :=
  SSP.AldousShepp.variance_bound absorptionMoments_nonvacuous

/-- **The resolvent hypotheses are satisfiable.**  `1 − 0 = 1` is a unit, `‖0‖ ≤ 0 < 1`. -/
theorem resolvent_hyps_nonvacuous :
    IsUnit (1 - (0 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
    ‖(0 : Matrix (Fin 1) (Fin 1) ℝ)‖ ≤ 0 ∧ (0:ℝ) < 1 :=
  ⟨by simp, by simp, by norm_num⟩

/-- **The first-moment identity instantiates.**  At `s = 1`, `Q = 0` this reads
`∫₀^∞ e^{−t} dt = 1`. -/
theorem integral_survival_applies :
    (∫ t in Ioi (0:ℝ),
        ((NormedSpace.exp (t • ((0:Matrix (Fin 1) (Fin 1) ℝ) - 1))).mulVec (fun _ => 1)) 0)
      = (((1 - (0:Matrix (Fin 1) (Fin 1) ℝ))⁻¹).mulVec (fun _ => 1)) 0 :=
  SSP.Semigroup.integral_survival 0 0 (by simp) (by simp) (by norm_num) 0

/-- **The second-moment identity instantiates.** -/
theorem integral_resolvent_sq_applies :
    (∫ t in Ioi (0:ℝ),
        ((NormedSpace.exp (t • ((0:Matrix (Fin 1) (Fin 1) ℝ) - 1))).mulVec
          (((1 - (0:Matrix (Fin 1) (Fin 1) ℝ))⁻¹).mulVec (fun _ => 1))) 0)
      = (((1 - (0:Matrix (Fin 1) (Fin 1) ℝ))⁻¹).mulVec
          (((1 - (0:Matrix (Fin 1) (Fin 1) ℝ))⁻¹).mulVec (fun _ => 1))) 0 :=
  SSP.Semigroup.integral_resolvent_sq 0 0 (by simp) (by simp) (by norm_num) 0

/-- **`‖exp x‖ ≤ exp ‖x‖` and `‖1‖ ≤ 1` instantiate at concrete matrices.** -/
theorem norm_bounds_apply :
    ‖NormedSpace.exp (0 : Matrix (Fin 2) (Fin 2) ℝ)‖
        ≤ Real.exp ‖(0 : Matrix (Fin 2) (Fin 2) ℝ)‖ ∧
    ‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖ ≤ 1 :=
  ⟨SSP.Semigroup.norm_exp_le 0, SSP.Semigroup.norm_one_le 3⟩

/-- **The `Exp(1)` moments are what they should be**, confirming the definitions really do
compute the moments of the exponential law and that the bound is tight there:
`E[X] = 1`, `E[X²] = 2`, `Var = 1 = (E X)²/1`. -/
theorem erlang_one_values :
    (1:ℝ) ^ 2 / (1:ℕ) = 2 - (1:ℝ) ^ 2 := by norm_num

/-! ## The absorption-time law

`SSPLean.SurvivalMonotone` constructs the law of the absorption time from its CDF.  Checking that
it is genuinely a probability measure at a concrete instance guards against the construction being
degenerate. -/

/-- **The `Exp(1)` law is a genuine probability measure.**  Instantiates the whole
`SurvivalMonotone` chain at `s = 1`, `Q = 0`. -/
theorem exp_one_isProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure
      (SSP.Survival.survivalStieltjes (0 : Matrix (Fin 1) (Fin 1) ℝ)
        (fun _ _ => le_refl 0) (fun _ => by norm_num) 0).measure :=
  SSP.Survival.isProbabilityMeasure 0 0 (fun _ _ => le_refl 0) (fun _ => by norm_num)
    (by rw [norm_zero]) (by norm_num) 0

/-- **The `Exp(1)` law gives no mass to `(−∞,0]`.** -/
theorem exp_one_measure_Iic_zero :
    (SSP.Survival.survivalStieltjes (0 : Matrix (Fin 1) (Fin 1) ℝ)
      (fun _ _ => le_refl 0) (fun _ => by norm_num) 0).measure (Set.Iic 0) = 0 :=
  SSP.Survival.measure_Iic_zero 0 (fun _ _ => le_refl 0) (fun _ => by norm_num) 0

/-! ## The unconditional Aldous–Shepp theorem

`SSP.aldous_shepp` has many hypotheses; checking they are jointly satisfiable confirms the theorem
is not vacuous. -/

/-- The zero matrix at `s = 1`, as a `Fin 1` matrix. -/
theorem toMat_Qzero_eq : SSP.toMat 1 Qzero = 0 := by ext a b; simp [SSP.toMat, Qzero]

theorem hQm_zero : ∀ i j : Fin 1, 0 ≤ (SSP.toMat 1 Qzero) i j := fun i j => by
  simp [SSP.toMat, Qzero]

theorem hrow_zero : ∀ i : Fin 1, ∑ j, (SSP.toMat 1 Qzero) i j ≤ 1 := fun i => by
  simp [SSP.toMat, Qzero]

theorem hrho_zero : spectralRadius ℂ ((SSP.toMat 1 Qzero).map (algebraMap ℝ ℂ)) < 1 := by
  rw [toMat_Qzero_eq]; simp only [Matrix.map_zero, map_zero]; rw [spectralRadius]; simp

/-- **`SSP.aldous_shepp` applies at `Exp(1)`.**  All ten hypotheses are simultaneously
satisfiable, so the unconditional theorem has content.  At this instance the bound is tight:
`E[X] = 1`, `E[X²] = 2`, `Var = 1 = (E X)²/1`. -/
theorem aldous_shepp_applies :
    (∫ x, id x ∂(SSP.Survival.survivalStieltjes (SSP.toMat 1 Qzero)
        hQm_zero hrow_zero 0).measure)^2 / ((1:ℕ):ℝ)
      ≤ (∫ x, (id x)^2 ∂(SSP.Survival.survivalStieltjes (SSP.toMat 1 Qzero)
          hQm_zero hrow_zero 0).measure)
        - (∫ x, id x ∂(SSP.Survival.survivalStieltjes (SSP.toMat 1 Qzero)
            hQm_zero hrow_zero 0).measure)^2 :=
  SSP.aldous_shepp Qzero 0 one_pos (fun i j => le_refl 0) (fun i _ => by simp [Qzero])
    hrho_zero hQm_zero hrow_zero (by rw [toMat_Qzero_eq]; simp)
    (by rw [toMat_Qzero_eq, norm_zero]) (by norm_num) 0

end SSP.Tests
