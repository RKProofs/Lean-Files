import SSPLean.K3CyclicCanonicalLogConvex
import SSPLean.CubicODEUniqueness

/-! # Real-spectrum middle coordinate via a positive two-state decomposition

Two-state matrix exponentials implement the divided differences without any
division by a difference of roots. Thus repeated adjacent roots are included.
-/

set_option autoImplicit false
open scoped Matrix.Norms.Operator
open Matrix Set

namespace SSP.K3Cyclic

open SSP.LogConvexIntegral

private abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
noncomputable local instance : AddCommGroup Mat2 := Matrix.linftyOpNormedAddCommGroup.toAddCommGroup
noncomputable local instance : TopologicalSpace Mat2 :=
  Matrix.linftyOpNormedAddCommGroup.toUniformSpace.toTopologicalSpace
noncomputable local instance : Module ℝ Mat2 := Matrix.linftyOpNormedSpace.toModule
noncomputable local instance : NormedAddCommGroup Mat2 := Matrix.linftyOpNormedAddCommGroup
noncomputable local instance : SeminormedAddCommGroup Mat2 := Matrix.linftyOpSeminormedAddCommGroup
noncomputable local instance : NormedSpace ℝ Mat2 := Matrix.linftyOpNormedSpace

noncomputable def twoRootB (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![u,0;1,v]
noncomputable def twoRootF (u v t : ℝ) : ℝ :=
  ((NormedSpace.exp (t • twoRootB u v)).mulVec ![1,0]) 1
noncomputable def twoRootF1 (u v t : ℝ) : ℝ :=
  ((NormedSpace.exp (t • twoRootB u v)).mulVec ((twoRootB u v).mulVec ![1,0])) 1
noncomputable def twoRootF2 (u v t : ℝ) : ℝ :=
  ((NormedSpace.exp (t • twoRootB u v)).mulVec
    ((twoRootB u v).mulVec ((twoRootB u v).mulVec ![1,0]))) 1

theorem twoRootF_hasDerivAt (u v t : ℝ) :
    HasDerivAt (twoRootF u v) (twoRootF1 u v t) t := by
  have hd : HasDerivAt
      (fun s => ((NormedSpace.exp (s • twoRootB u v)).mulVec ![1,0]) 1)
      (((NormedSpace.exp (t • twoRootB u v)*twoRootB u v).mulVec ![1,0]) 1) t := by
    convert SSP.Semigroup.hasDerivAt_mulVec_exp (twoRootB u v) ![1,0] 1 t using 1 <;> rfl
  have h : HasDerivAt (twoRootF u v)
      (((NormedSpace.exp (t • twoRootB u v)*twoRootB u v).mulVec ![1,0]) 1) t := by
    convert hd using 1 <;> rfl
  simpa only [twoRootF1, Matrix.mulVec_mulVec] using h

theorem twoRootF1_hasDerivAt (u v t : ℝ) :
    HasDerivAt (twoRootF1 u v) (twoRootF2 u v t) t := by
  have hd : HasDerivAt
      (fun s => ((NormedSpace.exp (s • twoRootB u v)).mulVec
        ((twoRootB u v).mulVec ![1,0])) 1)
      (((NormedSpace.exp (t • twoRootB u v)*twoRootB u v).mulVec
        ((twoRootB u v).mulVec ![1,0])) 1) t := by
    convert SSP.Semigroup.hasDerivAt_mulVec_exp (twoRootB u v)
      ((twoRootB u v).mulVec ![1,0]) 1 t using 1 <;> rfl
  have h : HasDerivAt (twoRootF1 u v)
      (((NormedSpace.exp (t • twoRootB u v)*twoRootB u v).mulVec
        ((twoRootB u v).mulVec ![1,0])) 1) t := by
    convert hd using 1 <;> rfl
  simpa only [twoRootF2, Matrix.mulVec_mulVec, mul_assoc] using h

theorem twoRootB_quadratic (u v : ℝ) :
    (twoRootB u v)^2 = (u+v) • twoRootB u v-(u*v) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoRootB, pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem twoRootB_cubic (u v w : ℝ) :
    (twoRootB u v)^3 = (u*v*w) • (1 : Matrix (Fin 2) (Fin 2) ℝ)-
      (u*v+u*w+v*w) • twoRootB u v+(u+v+w) • (twoRootB u v)^2 := by
  rw [pow_succ, twoRootB_quadratic]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoRootB, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem twoRootF2_hasDerivAt_cubic (u v w t : ℝ) :
    HasDerivAt (twoRootF2 u v)
      ((u*v*w)*twoRootF u v t-(u*v+u*w+v*w)*twoRootF1 u v t+
        (u+v+w)*twoRootF2 u v t) t := by
  have hd : HasDerivAt (twoRootF2 u v)
      (((NormedSpace.exp (t • twoRootB u v)*twoRootB u v).mulVec
        ((twoRootB u v).mulVec ((twoRootB u v).mulVec ![1,0]))) 1) t := by
    convert SSP.Semigroup.hasDerivAt_mulVec_exp (twoRootB u v)
      ((twoRootB u v).mulVec ((twoRootB u v).mulVec ![1,0])) 1 t using 1 <;> rfl
  convert hd using 1 <;> try rfl
  simp only [twoRootF, twoRootF1, twoRootF2, Matrix.mulVec_mulVec]
  rw [show (NormedSpace.exp (t • twoRootB u v)*twoRootB u v)*
      (twoRootB u v*twoRootB u v) = NormedSpace.exp (t • twoRootB u v)*(twoRootB u v)^3 by
    simp [pow_succ, mul_assoc]]
  rw [twoRootB_cubic u v w]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pow_two, mul_assoc]

@[simp] theorem twoRootF_zero (u v : ℝ) : twoRootF u v 0 = 0 := by
  norm_num [twoRootF, NormedSpace.exp_zero]
@[simp] theorem twoRootF1_zero (u v : ℝ) : twoRootF1 u v 0 = 1 := by
  norm_num [twoRootF1, twoRootB, NormedSpace.exp_zero]
@[simp] theorem twoRootF2_zero (u v : ℝ) : twoRootF2 u v 0 = u+v := by
  norm_num [twoRootF2, twoRootB, NormedSpace.exp_zero, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

theorem twoRootF_pos {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (t : ℝ) (ht : 0 < t) : 0 < twoRootF u v t := by
  have hne : twoRootF u v ≠ 0 := by
    intro h
    have hd := (twoRootF_hasDerivAt u v 0).deriv
    rw [h] at hd
    simp at hd
  have heq : SSP.MatrixTwo.scalar (twoRootB u v) ![0,1] ![1,0] = twoRootF u v := by
    funext s
    simp [SSP.MatrixTwo.scalar, twoRootF, dotProduct, Fin.sum_univ_two]
  rw [← heq]
  apply SSP.MatrixTwo.scalar_pos (twoRootB u v) ![0,1] ![1,0] _ _ _ _ t ht
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [twoRootB] <;> assumption
  · intro i; fin_cases i <;> norm_num
  · intro i; fin_cases i <;> norm_num
  · rwa [heq]

theorem twoRootF_log_quotient_convex {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (twoRootF u v t/t)) := by
  have hne : SSP.MatrixTwo.scalar (twoRootB u v) ![0,1] ![1,0] ≠ 0 := by
    intro h
    have hp := twoRootF_pos hu hv 1 (by norm_num)
    have he : SSP.MatrixTwo.scalar (twoRootB u v) ![0,1] ![1,0] 1 = twoRootF u v 1 := by
      simp [SSP.MatrixTwo.scalar, twoRootF, dotProduct, Fin.sum_univ_two]
    rw [h] at he
    simp [← he] at hp
  have hc := SSP.MatrixTwo.conjecture_two_two_by_two (twoRootB u v) ![0,1] ![1,0]
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [twoRootB] <;> assumption)
    (by intro i; fin_cases i <;> norm_num) (by intro i; fin_cases i <;> norm_num) hne
  simpa only [SSP.MatrixTwo.scalar, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, one_mul, zero_add, twoRootF] using hc

/-- Positive decomposition of the actual middle coordinate, with adjacent
repeated roots allowed. -/
theorem canonicalMiddle_eq_twoRoot_combination
    {a b c x2 x3 u v w theta : ℝ}
    (hsum : u+v+w = a+b) (hpair : u*v+u*w+v*w = a*b)
    (hprod : u*v*w = c*x2*x3)
    (hb : b = theta*w+(1-theta)*u) :
    canonicalMiddle a b c x2 x3 =
      fun t => x2*(theta*twoRootF u v t+(1-theta)*twoRootF v w t) := by
  apply SSP.CubicODE.eq_of_cubic_ode
    (c0 := c*x2*x3) (c1 := -a*b) (c2 := a+b) (t0 := 0)
    (f1 := canonicalMiddleDeriv a b c x2 x3)
    (f2 := canonicalMiddleDeriv2 a b c x2 x3)
    (g1 := fun t => x2*(theta*twoRootF1 u v t+(1-theta)*twoRootF1 v w t))
    (g2 := fun t => x2*(theta*twoRootF2 u v t+(1-theta)*twoRootF2 v w t))
  · exact canonicalMiddle_hasDerivAt a b c x2 x3
  · exact canonicalMiddleDeriv_hasDerivAt a b c x2 x3
  · intro t
    convert canonicalMiddleDeriv2_hasDerivAt a b c x2 x3 t using 1 <;> try rfl
    ring
  · intro t
    exact (((twoRootF_hasDerivAt u v t).const_mul theta).add
      ((twoRootF_hasDerivAt v w t).const_mul (1-theta))).const_mul x2
  · intro t
    exact (((twoRootF1_hasDerivAt u v t).const_mul theta).add
      ((twoRootF1_hasDerivAt v w t).const_mul (1-theta))).const_mul x2
  · intro t
    have h := (((twoRootF2_hasDerivAt_cubic u v w t).const_mul theta).add
      ((twoRootF2_hasDerivAt_cubic v w u t).const_mul (1-theta))).const_mul x2
    convert h using 1 <;> try rfl
    rw [show -a*b = -(a*b) by ring, ← hsum, ← hpair, ← hprod]
    ring
  · simp
  · simp
  · simp only [canonicalMiddleDeriv2_zero, twoRootF2_zero]
    rw [show a = u+v+w-b by linarith, hb]
    ring

theorem canonicalMiddle_log_quotient_convex_of_twoRoot_combination
    {a b c x2 x3 u v w theta : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (h2 : 0 < x2) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hsum : u+v+w = a+b) (hpair : u*v+u*w+v*w = a*b)
    (hprod : u*v*w = c*x2*x3)
    (hb : b = theta*w+(1-theta)*u) :
    ConvexOn ℝ (Ioi 0)
      (fun t => Real.log (canonicalMiddle a b c x2 x3 t/t)) := by
  have hc := log_nonneg_combination_convex
    (fun t => twoRootF u v t/t) (fun t => twoRootF v w t/t)
    theta (1-theta) htheta0 (by linarith) (by linarith)
    (fun t ht => div_pos (twoRootF_pos hu hv t ht) ht)
    (fun t ht => div_pos (twoRootF_pos hv hw t ht) ht)
    (twoRootF_log_quotient_convex hu hv) (twoRootF_log_quotient_convex hv hw)
  have hp : ∀ t, 0 < t → 0 < theta*twoRootF u v t+(1-theta)*twoRootF v w t := by
    intro t ht
    by_cases htheta : theta = 0
    · simp [htheta, twoRootF_pos hv hw t ht]
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne htheta0 (Ne.symm htheta)) (twoRootF_pos hu hv t ht))
        (mul_nonneg (by linarith) (twoRootF_pos hv hw t ht).le)
  have hc' : ConvexOn ℝ (Ioi 0)
      (fun t => Real.log ((theta*twoRootF u v t+(1-theta)*twoRootF v w t)/t^1)) := by
    simpa only [pow_one, add_div, mul_div_assoc] using hc
  have hf := log_quotient_const_mul_convex _ 1 x2 h2 hp hc'
  simpa only [canonicalMiddle_eq_twoRoot_combination hsum hpair hprod hb, pow_one] using hf

theorem canonicalMiddle_orderedRealRoots_log_quotient_convex
    {a b c x2 x3 u v w : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) (hc : 0 ≤ c)
    (h2 : 0 < x2) (h3 : 0 ≤ x3)
    (huv : u ≤ v) (hvw : v ≤ w) (hw : 0 < w)
    (hsum : u+v+w = a+b) (hpair : u*v+u*w+v*w = a*b)
    (hprod : u*v*w = c*x2*x3) :
    ConvexOn ℝ (Ioi 0)
      (fun t => Real.log (canonicalMiddle a b c x2 x3 t/t)) := by
  have hQ : 0 ≤ c*x2*x3 := mul_nonneg (mul_nonneg hc h2.le) h3
  have hu : 0 ≤ u := SSP.K3CyclicRealTail.orderedRealRoots_nonneg_of_coefficients
    huv hvw hw (by linarith) (by rw [hpair]; exact mul_nonneg ha hb)
    (by rwa [hprod])
  have hv : 0 ≤ v := hu.trans huv
  have huw : u < w := by
    by_contra h
    have hue : u = w := le_antisymm (huv.trans hvw) (le_of_not_gt h)
    have hve : v = w := by linarith
    rw [hue, hve] at hsum hpair
    nlinarith [sq_nonneg (a-b)]
  have hub : u ≤ b := by linarith
  have hbw : b ≤ w := by
    by_contra h
    have hwb : w < b := lt_of_not_ge h
    have hfac : (b-u)*(b-v)*(b-w) = -(c*x2*x3) := by
      calc
        _ = b^3-(u+v+w)*b^2+(u*v+u*w+v*w)*b-u*v*w := by ring
        _ = _ := by rw [hsum, hpair, hprod]; ring
    have hp : 0 < (b-u)*(b-v)*(b-w) :=
      mul_pos (mul_pos (sub_pos.mpr ((huv.trans hvw).trans_lt hwb))
        (sub_pos.mpr (hvw.trans_lt hwb))) (sub_pos.mpr hwb)
    linarith
  let theta := (b-u)/(w-u)
  have htheta0 : 0 ≤ theta := div_nonneg (sub_nonneg.mpr hub) (sub_nonneg.mpr huw.le)
  have htheta1 : theta ≤ 1 := by
    dsimp [theta]
    apply (div_le_one (sub_pos.mpr huw)).mpr
    linarith
  have htheta : b = theta*w+(1-theta)*u := by
    dsimp [theta]
    field_simp [ne_of_gt (sub_pos.mpr huw)]
    <;> ring
  exact canonicalMiddle_log_quotient_convex_of_twoRoot_combination hu hv hw.le
    h2 htheta0 htheta1 hsum hpair hprod htheta

theorem canonicalThird_orderedRealRoots_log_quotient_convex
    {a b c x2 x3 u v w : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) (hc : 0 ≤ c)
    (h2 : 0 < x2) (h3 : 0 < x3)
    (huv : u ≤ v) (hvw : v ≤ w) (hw : 0 < w)
    (hsum : u+v+w = a+b) (hpair : u*v+u*w+v*w = a*b)
    (hprod : u*v*w = c*x2*x3) :
    ConvexOn ℝ (Ioi 0)
      (fun t => Real.log (canonicalThird a b c x2 x3 t/t^2)) :=
  canonicalThird_log_quotient_convex_of_middle h3
    (canonicalMiddle_pos ha hb hc h2 h3.le)
    (canonicalMiddle_orderedRealRoots_log_quotient_convex ha hb hab hc h2 h3.le
      huv hvw hw hsum hpair hprod)

end SSP.K3Cyclic
