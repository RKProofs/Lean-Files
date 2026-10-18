import SSPLean.K3CyclicComplexFirst
import SSPLean.CubicODEUniqueness

/-! # Analytic ODE for the complex-pair first start

This lightweight file supplies the derivative and cubic-ODE facts needed to
identify the compact executable recurrences with the analytic first-start
function.  It deliberately imports no finite certificate.
-/

set_option autoImplicit false

namespace SSP.K3CyclicComplex

/-- The normalized analytic function used in the positive-`m` compact chart. -/
noncomputable def firstF (m ω x : ℝ) : ℝ :=
  firstH m ω x / (1 + ω ^ 2)

noncomputable def firstF1 (m ω x : ℝ) : ℝ :=
  firstH1 m ω x / (1 + ω ^ 2)

noncomputable def firstF2 (m ω x : ℝ) : ℝ :=
  firstH2 m ω x / (1 + ω ^ 2)

/-- A convenient explicit representative of the third derivative. -/
noncomputable def firstF3 (m ω x : ℝ) : ℝ :=
  (firstA m ω * Real.exp x - ω ^ 2 * firstT1 m ω x) /
    (1 + ω ^ 2)

theorem sinc_hasDerivAt {ω x : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (sinc ω) (Real.cos (ω * x)) x := by
  rw [show sinc ω = fun y => Real.sin (ω * y) / ω by
    funext y
    exact sinc_eq hω]
  simpa [Function.comp_def, hω] using
    (((Real.hasDerivAt_sin (ω * x)).comp x
      (hasDerivAt_const_mul ω)).div_const ω)

theorem firstT_hasDerivAt {m ω x : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (firstT m ω) (firstT1 m ω x) x := by
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (ω * y))
      (-Real.sin (ω * x) * ω) x := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_cos (ω * x)).comp x (hasDerivAt_const_mul ω)
  have hsinc := sinc_hasDerivAt (ω := ω) (x := x) hω
  have h := ((hasDerivAt_const x (1 - m ^ 2)).mul hcos).sub
    ((hasDerivAt_const x ((m + 1) * (m + ω ^ 2))).mul hsinc)
  have h' : HasDerivAt (firstT m ω)
      ((1 - m ^ 2) * (-Real.sin (ω * x) * ω) -
        (m + 1) * (m + ω ^ 2) * Real.cos (ω * x)) x := by
    convert! h using 1; try simp
  convert! h' using 1
  simp only [firstT1]
  ring

theorem firstT1_hasDerivAt {m ω x : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (firstT1 m ω) (-ω ^ 2 * firstT m ω x) x := by
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (ω * y))
      (Real.cos (ω * x) * ω) x := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_sin (ω * x)).comp x (hasDerivAt_const_mul ω)
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (ω * y))
      (-Real.sin (ω * x) * ω) x := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_cos (ω * x)).comp x (hasDerivAt_const_mul ω)
  have h := ((hasDerivAt_const x (-(1 - m ^ 2) * ω)).mul hsin).sub
    ((hasDerivAt_const x ((m + 1) * (m + ω ^ 2))).mul hcos)
  have h' : HasDerivAt (firstT1 m ω)
      (-(1 - m ^ 2) * ω * (Real.cos (ω * x) * ω) -
        (m + 1) * (m + ω ^ 2) * (-Real.sin (ω * x) * ω)) x := by
    convert! h using 1; try simp
  convert! h' using 1
  rw [firstT, sinc_eq hω]
  field_simp [hω]
  ring

theorem firstH_hasDerivAt {m ω x : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (firstH m ω) (firstH1 m ω x) x := by
  have hexp := (hasDerivAt_const x (firstA m ω)).mul (Real.hasDerivAt_exp x)
  have h := hexp.add (firstT_hasDerivAt (m := m) (ω := ω) (x := x) hω)
  convert! h using 1; try simp [firstH1]

theorem firstH1_hasDerivAt {m ω x : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (firstH1 m ω) (firstH2 m ω x) x := by
  have hexp := (hasDerivAt_const x (firstA m ω)).mul (Real.hasDerivAt_exp x)
  have h := hexp.add (firstT1_hasDerivAt (m := m) (ω := ω) (x := x) hω)
  have h' : HasDerivAt (firstH1 m ω)
      (firstA m ω * Real.exp x + -ω ^ 2 * firstT m ω x) x := by
    convert! h using 1; try simp
  convert! h' using 1
  simp only [firstH2]
  ring

theorem firstH2_hasDerivAt {m ω x : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (firstH2 m ω)
      (firstA m ω * Real.exp x - ω ^ 2 * firstT1 m ω x) x := by
  have hexp := (hasDerivAt_const x (firstA m ω)).mul (Real.hasDerivAt_exp x)
  have ht := (hasDerivAt_const x (ω ^ 2)).mul
    (firstT_hasDerivAt (m := m) (ω := ω) (x := x) hω)
  have h := hexp.sub ht
  convert! h using 1; try simp

theorem firstF_hasDerivAt {m ω x : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (firstF m ω) (firstF1 m ω x) x := by
  change HasDerivAt (fun y => firstH m ω y / (1 + ω ^ 2))
    (firstH1 m ω x / (1 + ω ^ 2)) x
  exact (firstH_hasDerivAt (m := m) (ω := ω) (x := x) hω).div_const
    (1 + ω ^ 2)

theorem firstF1_hasDerivAt {m ω x : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (firstF1 m ω) (firstF2 m ω x) x := by
  change HasDerivAt (fun y => firstH1 m ω y / (1 + ω ^ 2))
    (firstH2 m ω x / (1 + ω ^ 2)) x
  exact (firstH1_hasDerivAt (m := m) (ω := ω) (x := x) hω).div_const
    (1 + ω ^ 2)

theorem firstF2_hasDerivAt {m ω x : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (firstF2 m ω) (firstF3 m ω x) x := by
  change HasDerivAt (fun y => firstH2 m ω y / (1 + ω ^ 2))
    ((firstA m ω * Real.exp x - ω ^ 2 * firstT1 m ω x) /
      (1 + ω ^ 2)) x
  exact (firstH2_hasDerivAt (m := m) (ω := ω) (x := x) hω).div_const
    (1 + ω ^ 2)

/-- The normalized function has characteristic roots `1`, `iω`, `-iω`. -/
theorem firstF_cubic_ode (m ω x : ℝ) :
    firstF3 m ω x = firstF2 m ω x - ω ^ 2 * firstF1 m ω x +
      ω ^ 2 * firstF m ω x := by
  simp only [firstF, firstF1, firstF2, firstF3, firstH, firstH1, firstH2]
  ring

theorem one_add_sq_ne_zero (ω : ℝ) : 1 + ω ^ 2 ≠ 0 := by
  nlinarith [sq_nonneg ω]

@[simp] theorem firstF_zero (m ω : ℝ) : firstF m ω 0 = 1 := by
  simp [firstF, firstH, firstA, firstT, sinc]
  field_simp [one_add_sq_ne_zero]
  ring

@[simp] theorem firstF1_zero (m ω : ℝ) : firstF1 m ω 0 = -m := by
  simp [firstF1, firstH1, firstA, firstT1]
  field_simp [one_add_sq_ne_zero]
  ring

@[simp] theorem firstF2_zero (m ω : ℝ) : firstF2 m ω 0 = m ^ 2 := by
  simp [firstF2, firstH2, firstA, firstT, sinc]
  field_simp [one_add_sq_ne_zero]
  ring

end SSP.K3CyclicComplex
