import SSPLean.K3CyclicCanonicalMatrixBridge

/-! # The middle coordinate of the canonical three-cycle exponential -/

set_option autoImplicit false

namespace SSP.K3Cyclic

open NormedSpace Matrix

noncomputable def canonicalMiddle (a b c x2 x3 t : ℝ) : ℝ :=
  ((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec firstBasis) 1

noncomputable def canonicalMiddleDeriv (a b c x2 x3 t : ℝ) : ℝ :=
  ((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec
    ((canonicalB a b c x2 x3).mulVec firstBasis)) 1

noncomputable def canonicalMiddleDeriv2 (a b c x2 x3 t : ℝ) : ℝ :=
  ((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec
    ((canonicalB a b c x2 x3).mulVec
      ((canonicalB a b c x2 x3).mulVec firstBasis))) 1

theorem canonicalMiddle_hasDerivAt (a b c x2 x3 t : ℝ) :
    HasDerivAt (canonicalMiddle a b c x2 x3)
      (canonicalMiddleDeriv a b c x2 x3 t) t := by
  have h := SSP.Semigroup.hasDerivAt_mulVec_exp
    (canonicalB a b c x2 x3) firstBasis 1 t
  change HasDerivAt
    (fun u => ((NormedSpace.exp (u • canonicalB a b c x2 x3)).mulVec firstBasis) 1)
    (((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec
      ((canonicalB a b c x2 x3).mulVec firstBasis)) 1) t
  simpa only [Matrix.mulVec_mulVec] using h

theorem canonicalMiddleDeriv_hasDerivAt (a b c x2 x3 t : ℝ) :
    HasDerivAt (canonicalMiddleDeriv a b c x2 x3)
      (canonicalMiddleDeriv2 a b c x2 x3 t) t := by
  have h := SSP.Semigroup.hasDerivAt_mulVec_exp
    (canonicalB a b c x2 x3)
    ((canonicalB a b c x2 x3).mulVec firstBasis) 1 t
  change HasDerivAt
    (fun u => ((NormedSpace.exp (u • canonicalB a b c x2 x3)).mulVec
      ((canonicalB a b c x2 x3).mulVec firstBasis)) 1)
    (((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec
      ((canonicalB a b c x2 x3).mulVec
        ((canonicalB a b c x2 x3).mulVec firstBasis))) 1) t
  simpa only [Matrix.mulVec_mulVec, mul_assoc] using h

theorem canonicalMiddleDeriv2_hasDerivAt (a b c x2 x3 t : ℝ) :
    HasDerivAt (canonicalMiddleDeriv2 a b c x2 x3)
      ((c * x2 * x3) * canonicalMiddle a b c x2 x3 t -
        a * b * canonicalMiddleDeriv a b c x2 x3 t +
          (a + b) * canonicalMiddleDeriv2 a b c x2 x3 t) t := by
  let B := canonicalB a b c x2 x3
  have h := SSP.Semigroup.hasDerivAt_mulVec_exp B
    (B.mulVec (B.mulVec firstBasis)) 1 t
  change HasDerivAt
    (fun u => ((NormedSpace.exp (u • B)).mulVec
      (B.mulVec (B.mulVec firstBasis))) 1)
    ((c * x2 * x3) * canonicalMiddle a b c x2 x3 t -
      a * b * canonicalMiddleDeriv a b c x2 x3 t +
        (a + b) * canonicalMiddleDeriv2 a b c x2 x3 t) t
  have hder :
      (((NormedSpace.exp (t • B) * B).mulVec
        (B.mulVec (B.mulVec firstBasis))) 1) =
        (c * x2 * x3) * canonicalMiddle a b c x2 x3 t -
          a * b * canonicalMiddleDeriv a b c x2 x3 t +
            (a + b) * canonicalMiddleDeriv2 a b c x2 x3 t := by
    dsimp [canonicalMiddle, canonicalMiddleDeriv, canonicalMiddleDeriv2, B]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [show (NormedSpace.exp (t • canonicalB a b c x2 x3) *
          canonicalB a b c x2 x3) * canonicalB a b c x2 x3 *
          canonicalB a b c x2 x3 =
        NormedSpace.exp (t • canonicalB a b c x2 x3) *
          canonicalB a b c x2 x3 ^ 3 by simp [pow_succ', mul_assoc]]
    rw [← Matrix.mulVec_mulVec, canonicalB_cubic]
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    simp only [pow_two, Matrix.mulVec_mulVec]
    ring
  rw [← hder]
  exact h

@[simp] theorem canonicalMiddle_zero (a b c x2 x3 : ℝ) :
    canonicalMiddle a b c x2 x3 0 = 0 := by
  norm_num [canonicalMiddle, firstBasis, NormedSpace.exp_zero]

@[simp] theorem canonicalMiddleDeriv_zero (a b c x2 x3 : ℝ) :
    canonicalMiddleDeriv a b c x2 x3 0 = x2 := by
  norm_num [canonicalMiddleDeriv, canonicalB, firstBasis,
    NormedSpace.exp_zero, Matrix.mul_apply, Fin.sum_univ_three]

@[simp] theorem canonicalMiddleDeriv2_zero (a b c x2 x3 : ℝ) :
    canonicalMiddleDeriv2 a b c x2 x3 0 = a * x2 := by
  norm_num [canonicalMiddleDeriv2, canonicalB, firstBasis,
    NormedSpace.exp_zero, Matrix.mul_apply, Fin.sum_univ_three];
    simp [Matrix.vecHead, Matrix.vecTail]

end SSP.K3Cyclic
