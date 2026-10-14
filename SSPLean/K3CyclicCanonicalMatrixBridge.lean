import SSPLean.K3CyclicRealCanonicalODE
import SSPLean.SemigroupMoments

/-! # Canonical three-cycle matrix exponential and its scalar cubic ODE -/

set_option autoImplicit false

namespace SSP.K3Cyclic

open NormedSpace Matrix

/-- The shifted canonical three-cycle matrix from the spectral reduction. -/
noncomputable def canonicalB (a b c x2 x3 : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, c; x2, a, 0; 0, x3, b]

noncomputable def firstBasis : Fin 3 → ℝ := ![1, 0, 0]

theorem canonicalB_cubic (a b c x2 x3 : ℝ) :
    canonicalB a b c x2 x3 ^ 3 =
      (a + b) • canonicalB a b c x2 x3 ^ 2 -
        (a * b) • canonicalB a b c x2 x3 +
          (c * x2 * x3) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [canonicalB, Matrix.mul_apply, Fin.sum_univ_three, pow_succ'] <;>
    simp <;>
    ring

noncomputable def canonicalFirst (a b c x2 x3 t : ℝ) : ℝ :=
  ((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec firstBasis) 0

noncomputable def canonicalFirstDeriv (a b c x2 x3 t : ℝ) : ℝ :=
  ((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec
    ((canonicalB a b c x2 x3).mulVec firstBasis)) 0

noncomputable def canonicalFirstDeriv2 (a b c x2 x3 t : ℝ) : ℝ :=
  ((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec
    ((canonicalB a b c x2 x3).mulVec
      ((canonicalB a b c x2 x3).mulVec firstBasis))) 0

theorem canonicalFirst_hasDerivAt (a b c x2 x3 t : ℝ) :
    HasDerivAt (canonicalFirst a b c x2 x3)
      (canonicalFirstDeriv a b c x2 x3 t) t := by
  have h := SSP.Semigroup.hasDerivAt_mulVec_exp
    (canonicalB a b c x2 x3) firstBasis 0 t
  change HasDerivAt
    (fun u => ((NormedSpace.exp (u • canonicalB a b c x2 x3)).mulVec firstBasis) 0)
    (((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec
      ((canonicalB a b c x2 x3).mulVec firstBasis)) 0) t
  simpa only [Matrix.mulVec_mulVec] using h

theorem canonicalFirstDeriv_hasDerivAt (a b c x2 x3 t : ℝ) :
    HasDerivAt (canonicalFirstDeriv a b c x2 x3)
      (canonicalFirstDeriv2 a b c x2 x3 t) t := by
  have h := SSP.Semigroup.hasDerivAt_mulVec_exp
    (canonicalB a b c x2 x3)
    ((canonicalB a b c x2 x3).mulVec firstBasis) 0 t
  change HasDerivAt
    (fun u => ((NormedSpace.exp (u • canonicalB a b c x2 x3)).mulVec
      ((canonicalB a b c x2 x3).mulVec firstBasis)) 0)
    (((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec
      ((canonicalB a b c x2 x3).mulVec
        ((canonicalB a b c x2 x3).mulVec firstBasis))) 0) t
  simpa only [Matrix.mulVec_mulVec, mul_assoc] using h

theorem canonicalFirstDeriv2_hasDerivAt (a b c x2 x3 t : ℝ) :
    HasDerivAt (canonicalFirstDeriv2 a b c x2 x3)
      ((c * x2 * x3) * canonicalFirst a b c x2 x3 t -
        a * b * canonicalFirstDeriv a b c x2 x3 t +
          (a + b) * canonicalFirstDeriv2 a b c x2 x3 t) t := by
  let B := canonicalB a b c x2 x3
  have h := SSP.Semigroup.hasDerivAt_mulVec_exp B
    (B.mulVec (B.mulVec firstBasis)) 0 t
  change HasDerivAt
    (fun u => ((NormedSpace.exp (u • B)).mulVec
      (B.mulVec (B.mulVec firstBasis))) 0)
    ((c * x2 * x3) * canonicalFirst a b c x2 x3 t -
      a * b * canonicalFirstDeriv a b c x2 x3 t +
        (a + b) * canonicalFirstDeriv2 a b c x2 x3 t) t
  have hder :
      (((NormedSpace.exp (t • B) * B).mulVec
        (B.mulVec (B.mulVec firstBasis))) 0) =
        (c * x2 * x3) * canonicalFirst a b c x2 x3 t -
          a * b * canonicalFirstDeriv a b c x2 x3 t +
            (a + b) * canonicalFirstDeriv2 a b c x2 x3 t := by
    dsimp [canonicalFirst, canonicalFirstDeriv, canonicalFirstDeriv2, B]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [show (NormedSpace.exp (t • canonicalB a b c x2 x3) *
          canonicalB a b c x2 x3) * canonicalB a b c x2 x3 *
          canonicalB a b c x2 x3 =
        NormedSpace.exp (t • canonicalB a b c x2 x3) *
          canonicalB a b c x2 x3 ^ 3 by simp [pow_succ', mul_assoc]]
    rw [← Matrix.mulVec_mulVec]
    rw [canonicalB_cubic]
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    simp only [pow_two, Matrix.mulVec_mulVec]
    ring
  rw [← hder]
  exact h

@[simp] theorem canonicalFirst_zero (a b c x2 x3 : ℝ) :
    canonicalFirst a b c x2 x3 0 = 1 := by
  simp [canonicalFirst, firstBasis, NormedSpace.exp_zero]

@[simp] theorem canonicalFirstDeriv_zero (a b c x2 x3 : ℝ) :
    canonicalFirstDeriv a b c x2 x3 0 = 0 := by
  norm_num [canonicalFirstDeriv, canonicalB, firstBasis,
    NormedSpace.exp_zero, Matrix.mul_apply, Fin.sum_univ_three]

@[simp] theorem canonicalFirstDeriv2_zero (a b c x2 x3 : ℝ) :
    canonicalFirstDeriv2 a b c x2 x3 0 = 0 := by
  norm_num [canonicalFirstDeriv2, canonicalB, firstBasis,
    NormedSpace.exp_zero, Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp [Matrix.vecHead, Matrix.vecTail]

/-- For an ordered nonnegative real spectrum, the actual first coordinate
of the canonical matrix exponential is the normalized Taylor function used
by the real-root curvature certificate. -/
theorem canonicalFirst_eq_orderedRealRootSeries
    {a b c x2 x3 root1 root2 root3 : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3)
    (hroot12 : root1 ≤ root2) (hroot23 : root2 ≤ root3)
    (hroot3 : 0 < root3)
    (hsum : root1 + root2 + root3 = a + b)
    (hpair : root1 * root2 + root1 * root3 + root2 * root3 = a * b)
    (hprod : root1 * root2 * root3 = c * x2 * x3) :
    canonicalFirst a b c x2 x3 = fun t =>
      1 + SSP.K3CyclicRealTail.firstStartRemainder
        (root1 / root3) (root2 / root3) (root3 * t) := by
  apply SSP.K3CyclicRealTail.canonicalOrderedRealRoots_series_eq_of_solution
    ha hb (mul_nonneg (mul_nonneg hc hx2) hx3)
    hroot12 hroot23 hroot3 hsum hpair hprod
    (fun t => canonicalFirst_hasDerivAt a b c x2 x3 t)
    (fun t => canonicalFirstDeriv_hasDerivAt a b c x2 x3 t)
    (fun t => canonicalFirstDeriv2_hasDerivAt a b c x2 x3 t)
  · exact canonicalFirst_zero a b c x2 x3
  · exact canonicalFirstDeriv_zero a b c x2 x3
  · exact canonicalFirstDeriv2_zero a b c x2 x3

/-- The real-spectrum first-start curvature certificate, now stated for the
actual canonical matrix-exponential coordinate and its actual derivatives. -/
theorem canonicalFirst_orderedRealRoots_correctedCurvature3_nonneg
    {a b c x2 x3 root1 root2 root3 t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx2 : 0 ≤ x2) (hx3 : 0 ≤ x3)
    (hroot12 : root1 ≤ root2) (hroot23 : root2 ≤ root3)
    (hroot3 : 0 < root3)
    (hsum : root1 + root2 + root3 = a + b)
    (hpair : root1 * root2 + root1 * root3 + root2 * root3 = a * b)
    (hprod : root1 * root2 * root3 = c * x2 * x3)
    (ht : 0 ≤ t) :
    0 ≤ correctedCurvature3 t
      (canonicalFirst a b c x2 x3 t)
      (deriv (canonicalFirst a b c x2 x3) t)
      (deriv (fun x => deriv (canonicalFirst a b c x2 x3) x) t) := by
  have hseries := canonicalFirst_eq_orderedRealRootSeries
    ha hb hc hx2 hx3 hroot12 hroot23 hroot3 hsum hpair hprod
  rw [hseries]
  rcases SSP.K3CyclicRealTail.canonicalOrderedRealRoots_admissible
      ha hb (mul_nonneg (mul_nonneg hc hx2) hx3)
      hroot12 hroot23 hroot3 hsum hpair hprod with ⟨hu, hv, hroot⟩
  exact SSP.K3CyclicRealTail.scaledFirstStart_correctedCurvature3_nonneg
    hu hv hroot hroot3.le ht

end SSP.K3Cyclic
