import SSPLean.K3CyclicCanonicalMatrixBridge
import SSPLean.K3CyclicComplexFirstNegativeAnalyticODE

/-! # Complex-spectrum canonical first-coordinate bridge -/

set_option autoImplicit false

namespace SSP.K3Cyclic

open SSP.K3CyclicComplex

noncomputable def complexFirstModel (m omega d t : ℝ) : ℝ :=
  shiftedFirstF m omega (d * t)

noncomputable def complexFirstModelDeriv (m omega d t : ℝ) : ℝ :=
  d * shiftedFirstF1 m omega (d * t)

noncomputable def complexFirstModelDeriv2 (m omega d t : ℝ) : ℝ :=
  d ^ 2 * shiftedFirstF2 m omega (d * t)

theorem complexFirstModel_hasDerivAt
    {m omega d t : ℝ} (homega : omega ≠ 0) :
    HasDerivAt (complexFirstModel m omega d)
      (complexFirstModelDeriv m omega d t) t := by
  have harg : HasDerivAt (fun u : ℝ => d * u) d t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul d
  have h := (shiftedFirstF_hasDerivAt
    (m := m) (ω := omega) (x := d * t) homega).comp t harg
  convert h using 1
  all_goals try rfl
  simp [complexFirstModelDeriv, mul_comm]

theorem complexFirstModelDeriv_hasDerivAt
    {m omega d t : ℝ} (homega : omega ≠ 0) :
    HasDerivAt (complexFirstModelDeriv m omega d)
      (complexFirstModelDeriv2 m omega d t) t := by
  have harg : HasDerivAt (fun u : ℝ => d * u) d t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul d
  have h := ((shiftedFirstF1_hasDerivAt
    (m := m) (ω := omega) (x := d * t) homega).comp t harg).const_mul d
  convert h using 1
  all_goals try rfl
  simp [complexFirstModelDeriv2]
  ring

theorem complexFirstModelDeriv2_hasDerivAt_cubic
    {a b c x2 x3 m omega d t : ℝ} (homega : omega ≠ 0)
    (hsum : a + b = d * (1 + 3 * m))
    (hpair : a * b = d ^ 2 * (3 * m ^ 2 + 2 * m + omega ^ 2))
    (hprod : c * x2 * x3 =
      d ^ 3 * ((1 + m) * (m ^ 2 + omega ^ 2))) :
    HasDerivAt (complexFirstModelDeriv2 m omega d)
      ((c * x2 * x3) * complexFirstModel m omega d t -
        a * b * complexFirstModelDeriv m omega d t +
          (a + b) * complexFirstModelDeriv2 m omega d t) t := by
  have harg : HasDerivAt (fun u : ℝ => d * u) d t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul d
  have hraw := ((shiftedFirstF2_hasDerivAt
    (m := m) (ω := omega) (x := d * t) homega).comp t harg).const_mul (d ^ 2)
  convert hraw using 1
  all_goals try rfl
  rw [shiftedFirstF_cubic_ode, hsum, hpair, hprod]
  dsimp [complexFirstModel, complexFirstModelDeriv,
    complexFirstModelDeriv2]
  ring

/-- The actual first coordinate equals the normalized complex-pair function. -/
theorem canonicalFirst_eq_complexFirstModel
    {a b c x2 x3 m omega d : ℝ} (homega : omega ≠ 0)
    (hsum : a + b = d * (1 + 3 * m))
    (hpair : a * b = d ^ 2 * (3 * m ^ 2 + 2 * m + omega ^ 2))
    (hprod : c * x2 * x3 =
      d ^ 3 * ((1 + m) * (m ^ 2 + omega ^ 2))) :
    canonicalFirst a b c x2 x3 = complexFirstModel m omega d := by
  apply SSP.CubicODE.eq_of_cubic_ode
    (c0 := c * x2 * x3) (c1 := -(a * b)) (c2 := a + b) (t0 := 0)
    (fun t => canonicalFirst_hasDerivAt a b c x2 x3 t)
    (fun t => canonicalFirstDeriv_hasDerivAt a b c x2 x3 t)
    (fun t => by
      convert canonicalFirstDeriv2_hasDerivAt a b c x2 x3 t using 1 <;> ring)
    (fun t => complexFirstModel_hasDerivAt homega)
    (fun t => complexFirstModelDeriv_hasDerivAt homega)
    (fun t => by
      convert complexFirstModelDeriv2_hasDerivAt_cubic homega
        hsum hpair hprod using 1 <;> ring)
  · simp [complexFirstModel]
  · simp [complexFirstModelDeriv]
  · simp [complexFirstModelDeriv2]

end SSP.K3Cyclic
