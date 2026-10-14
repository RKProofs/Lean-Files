import SSPLean.K3CyclicRealCanonicalBridge

/-! # Complex-spectrum canonical first start

Algebraic reduction of the complex-pair first-start curvature to the
derivative-free oscillator expression used by the compact certificate.
The finite Bernstein and analytic-tail certificates are deliberately kept
out of this lightweight identity module.
-/

set_option autoImplicit false

namespace SSP.K3CyclicComplex

open Real SSP.K3Cyclic

/-- The continuously extended quotient `sin (ωx) / ω`. -/
noncomputable def sinc (ω x : ℝ) : ℝ :=
  if ω = 0 then x else Real.sin (ω * x) / ω

noncomputable def firstA (m ω : ℝ) : ℝ := m ^ 2 + ω ^ 2

noncomputable def firstT (m ω x : ℝ) : ℝ :=
  (1 - m ^ 2) * Real.cos (ω * x) -
    (m + 1) * (m + ω ^ 2) * sinc ω x

noncomputable def firstT1 (m ω x : ℝ) : ℝ :=
  -(1 - m ^ 2) * ω * Real.sin (ω * x) -
    (m + 1) * (m + ω ^ 2) * Real.cos (ω * x)

noncomputable def firstH (m ω x : ℝ) : ℝ :=
  firstA m ω * Real.exp x + firstT m ω x

noncomputable def firstH1 (m ω x : ℝ) : ℝ :=
  firstA m ω * Real.exp x + firstT1 m ω x

noncomputable def firstH2 (m ω x : ℝ) : ℝ :=
  firstA m ω * Real.exp x - ω ^ 2 * firstT m ω x

noncomputable def firstU (m ω x : ℝ) : ℝ :=
  Real.cos (ω * x) + (ω ^ 2 - m) / (m + 1) * sinc ω x

/-- The compact complex-root parameter domain. -/
def FirstDomain (m ω : ℝ) : Prop :=
  -(1 / 3 : ℝ) ≤ m ∧ m ≤ 1 / 3 ∧
    0 ≤ ω ^ 2 ∧
    -(3 * m ^ 2 + 2 * m) ≤ ω ^ 2 ∧
    4 * ω ^ 2 ≤ 1 - 2 * m - 3 * m ^ 2

/-- Elementary uniform bounds used by the analytic tail certificate. -/
theorem FirstDomain.bounds {m ω : ℝ} (h : FirstDomain m ω) :
    0 ≤ firstA m ω ∧ ω ^ 2 ≤ 1 / 3 ∧ firstA m ω ≤ 4 / 9 ∧
      (ω ^ 2 - m) ^ 2 ≤ firstA m ω ∧ 2 / 3 ≤ m + 1 ∧
      (m + 1) ^ 2 * (1 + ω ^ 2) ≤ 64 / 27 := by
  rcases h with ⟨hm0, hm1, hz0, _hzlower, hzupper⟩
  have hz1 : ω ^ 2 ≤ 1 / 3 := by
    nlinarith [sq_nonneg (m + 1 / 3)]
  have hmplus : 2 / 3 ≤ m + 1 := by linarith
  have hmminus0 : 0 ≤ 1 - m := by linarith
  have hmminus1 : 1 - m ≤ 4 / 3 := by linarith
  have hmminusSq : (1 - m) ^ 2 ≤ (4 / 3 : ℝ) ^ 2 := by nlinarith
  have hA0 : 0 ≤ firstA m ω := by
    unfold firstA
    positivity
  have hA1 : firstA m ω ≤ 4 / 9 := by
    unfold firstA
    nlinarith
  have hzlin : ω ^ 2 ≤ 1 + 2 * m := by linarith
  have hgap : (ω ^ 2 - m) ^ 2 ≤ firstA m ω := by
    unfold firstA
    have hzprod : 0 ≤ ω ^ 2 * (1 + 2 * m - ω ^ 2) :=
      mul_nonneg hz0 (by linarith)
    nlinarith
  have hmplusUpper : m + 1 ≤ 4 / 3 := by linarith
  have hmplus0 : 0 ≤ m + 1 := by linarith
  have hmplusSq : (m + 1) ^ 2 ≤ (16 / 9 : ℝ) := by nlinarith
  have honez : 0 ≤ 1 + ω ^ 2 := by linarith
  have honezUpper : 1 + ω ^ 2 ≤ 4 / 3 := by linarith
  have hcoef := mul_le_mul hmplusSq honezUpper honez (by positivity : (0 : ℝ) ≤ 16 / 9)
  refine ⟨hA0, hz1, hA1, hgap, hmplus, ?_⟩
  nlinarith

@[simp] theorem sinc_eq {ω x : ℝ} (hω : ω ≠ 0) :
    sinc ω x = Real.sin (ω * x) / ω := by
  simp [sinc, hω]

theorem abs_sinc_le_abs (ω x : ℝ) : |sinc ω x| ≤ |x| := by
  by_cases hω : ω = 0
  · simp [sinc, hω]
  · rw [sinc_eq hω, abs_div]
    have habsω : 0 < |ω| := abs_pos.mpr hω
    apply (div_le_iff₀ habsω).2
    calc
      |Real.sin (ω * x)| ≤ |ω * x| := Real.abs_sin_le_abs
      _ = |x| * |ω| := by rw [abs_mul, mul_comm]

theorem firstT_eq_U {m ω x : ℝ} (hm : m + 1 ≠ 0) :
    firstT m ω x = (1 - m ^ 2) * firstU m ω x -
      2 * firstA m ω * sinc ω x := by
  rw [firstT, firstU, firstA]
  field_simp
  ring

theorem firstCompanion_eq_U {m ω x : ℝ} (hm : m + 1 ≠ 0) :
    (m + 1) * Real.cos (ω * x) + (ω ^ 2 - m) * sinc ω x =
      (m + 1) * firstU m ω x := by
  rw [firstU]
  field_simp

theorem firstT_energy {m ω x : ℝ} (hω : ω ≠ 0) :
    firstT1 m ω x ^ 2 + ω ^ 2 * firstT m ω x ^ 2 =
      firstA m ω * (m + 1) ^ 2 * (1 + ω ^ 2) := by
  rw [firstT, firstT1, firstA, sinc_eq hω]
  have htrig := Real.sin_sq_add_cos_sq (ω * x)
  field_simp
  nlinarith

theorem firstT_companion {m ω x : ℝ} (hω : ω ≠ 0) :
    (1 - ω ^ 2) * firstT m ω x - 2 * firstT1 m ω x =
      (m + 1) * (1 + ω ^ 2) *
        ((m + 1) * Real.cos (ω * x) +
          (ω ^ 2 - m) * sinc ω x) := by
  rw [firstT, firstT1, sinc_eq hω]
  field_simp
  ring

/-- Exact Wronskian factorization for the complex-pair first start. -/
theorem firstH_wronskian {m ω x : ℝ} (hω : ω ≠ 0) :
    firstH m ω x * firstH2 m ω x - firstH1 m ω x ^ 2 =
      firstA m ω * (m + 1) * (1 + ω ^ 2) *
        (Real.exp x *
            ((m + 1) * Real.cos (ω * x) +
              (ω ^ 2 - m) * sinc ω x) - (m + 1)) := by
  have henergy := firstT_energy (m := m) (ω := ω) (x := x) hω
  have hcomp := firstT_companion (m := m) (ω := ω) (x := x) hω
  rw [firstH, firstH1, firstH2]
  rw [show
      (firstA m ω * Real.exp x + firstT m ω x) *
          (firstA m ω * Real.exp x - ω ^ 2 * firstT m ω x) -
          (firstA m ω * Real.exp x + firstT1 m ω x) ^ 2 =
        firstA m ω * Real.exp x *
            ((1 - ω ^ 2) * firstT m ω x - 2 * firstT1 m ω x) -
          (firstT1 m ω x ^ 2 + ω ^ 2 * firstT m ω x ^ 2) by ring]
  rw [hcomp, henergy]
  ring

/-- The corrected curvature is exactly the derivative-free oscillator target. -/
theorem firstH_correctedCurvature3_eq {m ω x : ℝ} (hω : ω ≠ 0) :
    correctedCurvature3 x (firstH m ω x) (firstH1 m ω x) (firstH2 m ω x) =
      2 * firstH m ω x ^ 2 +
        x ^ 2 * firstA m ω * (m + 1) * (1 + ω ^ 2) *
          (Real.exp x *
              ((m + 1) * Real.cos (ω * x) +
                (ω ^ 2 - m) * sinc ω x) - (m + 1)) := by
  rw [correctedCurvature3, firstH_wronskian hω]
  ring

end SSP.K3CyclicComplex
