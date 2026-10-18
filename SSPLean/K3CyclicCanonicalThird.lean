import SSPLean.K3CyclicCanonicalMiddle

/-! # The third coordinate of the canonical three-cycle exponential -/

set_option autoImplicit false

namespace SSP.K3Cyclic

open NormedSpace Matrix

noncomputable def canonicalThird (a b c x2 x3 t : ℝ) : ℝ :=
  ((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec firstBasis) 2

noncomputable def canonicalThirdDeriv (a b c x2 x3 t : ℝ) : ℝ :=
  ((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec
    ((canonicalB a b c x2 x3).mulVec firstBasis)) 2

noncomputable def canonicalThirdDeriv2 (a b c x2 x3 t : ℝ) : ℝ :=
  ((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec
    ((canonicalB a b c x2 x3).mulVec
      ((canonicalB a b c x2 x3).mulVec firstBasis))) 2

theorem canonicalThird_hasDerivAt (a b c x2 x3 t : ℝ) :
    HasDerivAt (canonicalThird a b c x2 x3)
      (canonicalThirdDeriv a b c x2 x3 t) t := by
  have h := SSP.Semigroup.hasDerivAt_mulVec_exp
    (canonicalB a b c x2 x3) firstBasis 2 t
  change HasDerivAt
    (fun u => ((NormedSpace.exp (u • canonicalB a b c x2 x3)).mulVec firstBasis) 2)
    (((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec
      ((canonicalB a b c x2 x3).mulVec firstBasis)) 2) t
  simpa only [Matrix.mulVec_mulVec] using h

theorem canonicalThirdDeriv_hasDerivAt (a b c x2 x3 t : ℝ) :
    HasDerivAt (canonicalThirdDeriv a b c x2 x3)
      (canonicalThirdDeriv2 a b c x2 x3 t) t := by
  have h := SSP.Semigroup.hasDerivAt_mulVec_exp
    (canonicalB a b c x2 x3)
    ((canonicalB a b c x2 x3).mulVec firstBasis) 2 t
  change HasDerivAt
    (fun u => ((NormedSpace.exp (u • canonicalB a b c x2 x3)).mulVec
      ((canonicalB a b c x2 x3).mulVec firstBasis)) 2)
    (((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec
      ((canonicalB a b c x2 x3).mulVec
        ((canonicalB a b c x2 x3).mulVec firstBasis))) 2) t
  simpa only [Matrix.mulVec_mulVec, mul_assoc] using h

theorem canonicalThirdDeriv2_hasDerivAt (a b c x2 x3 t : ℝ) :
    HasDerivAt (canonicalThirdDeriv2 a b c x2 x3)
      ((c * x2 * x3) * canonicalThird a b c x2 x3 t -
        a * b * canonicalThirdDeriv a b c x2 x3 t +
          (a + b) * canonicalThirdDeriv2 a b c x2 x3 t) t := by
  let B := canonicalB a b c x2 x3
  have h := SSP.Semigroup.hasDerivAt_mulVec_exp B
    (B.mulVec (B.mulVec firstBasis)) 2 t
  change HasDerivAt
    (fun u => ((NormedSpace.exp (u • B)).mulVec
      (B.mulVec (B.mulVec firstBasis))) 2)
    ((c * x2 * x3) * canonicalThird a b c x2 x3 t -
      a * b * canonicalThirdDeriv a b c x2 x3 t +
        (a + b) * canonicalThirdDeriv2 a b c x2 x3 t) t
  have hder :
      (((NormedSpace.exp (t • B) * B).mulVec
        (B.mulVec (B.mulVec firstBasis))) 2) =
        (c * x2 * x3) * canonicalThird a b c x2 x3 t -
          a * b * canonicalThirdDeriv a b c x2 x3 t +
            (a + b) * canonicalThirdDeriv2 a b c x2 x3 t := by
    dsimp [canonicalThird, canonicalThirdDeriv, canonicalThirdDeriv2, B]
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

@[simp] theorem canonicalThird_zero (a b c x2 x3 : ℝ) :
    canonicalThird a b c x2 x3 0 = 0 := by
  norm_num [canonicalThird, firstBasis, NormedSpace.exp_zero];
    simp

@[simp] theorem canonicalThirdDeriv_zero (a b c x2 x3 : ℝ) :
    canonicalThirdDeriv a b c x2 x3 0 = 0 := by
  norm_num [canonicalThirdDeriv, canonicalB, firstBasis,
    NormedSpace.exp_zero, Matrix.mul_apply, Fin.sum_univ_three];
    simp [Matrix.vecHead]

@[simp] theorem canonicalThirdDeriv2_zero (a b c x2 x3 : ℝ) :
    canonicalThirdDeriv2 a b c x2 x3 0 = x2 * x3 := by
  norm_num [canonicalThirdDeriv2, canonicalB, firstBasis,
    NormedSpace.exp_zero, Matrix.mul_apply, Fin.sum_univ_three];
    simp [Matrix.vecHead, Matrix.vecTail]; ring

theorem canonicalB_mulVec_two (a b c x2 x3 : ℝ)
    (v : Fin 3 → ℝ) :
    ((canonicalB a b c x2 x3).mulVec v) 2 = x3 * v 1 + b * v 2 := by
  norm_num [canonicalB, Matrix.mul_apply, Fin.sum_univ_three];
    simp [Matrix.vecHead, Matrix.vecTail]

/-- The third coordinate is driven by the middle coordinate through the last
edge of the canonical cycle. -/
theorem canonicalThirdDeriv_eq_middle
    (a b c x2 x3 t : ℝ) :
    canonicalThirdDeriv a b c x2 x3 t =
      x3 * canonicalMiddle a b c x2 x3 t +
        b * canonicalThird a b c x2 x3 t := by
  let B := canonicalB a b c x2 x3
  have hcomm : NormedSpace.exp (t • B) * B = B * NormedSpace.exp (t • B) := by
    exact ((Commute.refl B).smul_left t).exp_left.eq
  dsimp [canonicalThirdDeriv, canonicalMiddle, canonicalThird, B]
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec,
    canonicalB_mulVec_two]

theorem canonicalThirdDeriv2_eq_middleDeriv
    (a b c x2 x3 t : ℝ) :
    canonicalThirdDeriv2 a b c x2 x3 t =
      x3 * canonicalMiddleDeriv a b c x2 x3 t +
        b * canonicalThirdDeriv a b c x2 x3 t := by
  let B := canonicalB a b c x2 x3
  have hcomm : NormedSpace.exp (t • B) * B = B * NormedSpace.exp (t • B) := by
    exact ((Commute.refl B).smul_left t).exp_left.eq
  dsimp [canonicalThirdDeriv2, canonicalMiddleDeriv,
    canonicalThirdDeriv, B]
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec,
    canonicalB_mulVec_two]

end SSP.K3Cyclic
