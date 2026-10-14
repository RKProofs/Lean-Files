import SSPLean.K3CyclicComplexFirstAnalyticODE

/-! # Exponentially shifted analytic function for the negative-m chart -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex

noncomputable def shiftedFirstF (m ω x : ℝ) : ℝ :=
  Real.exp (m * x) * firstF m ω x

noncomputable def shiftedFirstF1 (m ω x : ℝ) : ℝ :=
  Real.exp (m * x) * (m * firstF m ω x + firstF1 m ω x)

noncomputable def shiftedFirstF2 (m ω x : ℝ) : ℝ :=
  Real.exp (m * x) *
    (m ^ 2 * firstF m ω x + 2 * m * firstF1 m ω x +
      firstF2 m ω x)

noncomputable def shiftedFirstF3 (m ω x : ℝ) : ℝ :=
  Real.exp (m * x) *
    (m ^ 3 * firstF m ω x + 3 * m ^ 2 * firstF1 m ω x +
      3 * m * firstF2 m ω x + firstF3 m ω x)

private theorem exp_mul_hasDerivAt (m x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (m * y))
      (m * Real.exp (m * x)) x := by
  have hid : HasDerivAt (fun y : ℝ => m * y) m x := by
    simpa using (hasDerivAt_id x).const_mul m
  have h := (Real.hasDerivAt_exp (m * x)).comp x hid
  change HasDerivAt (fun y : ℝ => Real.exp (m * y))
    (Real.exp (m * x) * m) x at h
  simpa [mul_comm] using h

theorem shiftedFirstF_hasDerivAt {m ω x : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (shiftedFirstF m ω) (shiftedFirstF1 m ω x) x := by
  have h := (exp_mul_hasDerivAt m x).mul
    (firstF_hasDerivAt (m := m) (ω := ω) (x := x) hω)
  convert! h using 1 <;> simp [shiftedFirstF, shiftedFirstF1] <;> ring

theorem shiftedFirstF1_hasDerivAt {m ω x : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (shiftedFirstF1 m ω) (shiftedFirstF2 m ω x) x := by
  have hinside :=
    ((firstF_hasDerivAt (m := m) (ω := ω) (x := x) hω).const_mul m).add
      (firstF1_hasDerivAt (m := m) (ω := ω) (x := x) hω)
  have h := (exp_mul_hasDerivAt m x).mul hinside
  convert! h using 1 <;>
    simp [shiftedFirstF1, shiftedFirstF2, Function.comp_def] <;> ring

theorem shiftedFirstF2_hasDerivAt {m ω x : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (shiftedFirstF2 m ω) (shiftedFirstF3 m ω x) x := by
  have hinside :=
    (((firstF_hasDerivAt (m := m) (ω := ω) (x := x) hω).const_mul
      (m ^ 2)).add
      ((firstF1_hasDerivAt (m := m) (ω := ω) (x := x) hω).const_mul
        (2 * m))).add
      (firstF2_hasDerivAt (m := m) (ω := ω) (x := x) hω)
  have h := (exp_mul_hasDerivAt m x).mul hinside
  convert! h using 1 <;>
    simp [shiftedFirstF2, shiftedFirstF3, Function.comp_def] <;> ring

theorem shiftedFirstF_cubic_ode (m ω x : ℝ) :
    shiftedFirstF3 m ω x =
      (1 + 3 * m) * shiftedFirstF2 m ω x -
        (3 * m ^ 2 + 2 * m + ω ^ 2) * shiftedFirstF1 m ω x +
        ((1 + m) * (m ^ 2 + ω ^ 2)) * shiftedFirstF m ω x := by
  unfold shiftedFirstF shiftedFirstF1 shiftedFirstF2 shiftedFirstF3
  rw [firstF_cubic_ode]
  ring

@[simp] theorem shiftedFirstF_zero (m ω : ℝ) :
    shiftedFirstF m ω 0 = 1 := by simp [shiftedFirstF]

@[simp] theorem shiftedFirstF1_zero (m ω : ℝ) :
    shiftedFirstF1 m ω 0 = 0 := by simp [shiftedFirstF1]

@[simp] theorem shiftedFirstF2_zero (m ω : ℝ) :
    shiftedFirstF2 m ω 0 = 0 := by
  simp [shiftedFirstF2]
  ring

end SSP.K3CyclicComplex
