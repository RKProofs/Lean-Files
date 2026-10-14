import SSPLean.K3CyclicRealFullAnalytic

/-!
# Canonical real-spectrum first-start bridge

This file transports the normalized real-root first-start certificate through
the time, exponential, and amplitude normalizations used for the canonical
three-state cycle.  It contains no coefficient normalization, so changes here
do not invalidate the expensive Bernstein certificate modules.
-/

set_option autoImplicit false

namespace SSP.K3CyclicRealTail

open SSP.K3Cyclic

/-- The derivative-explicit form of the normalized first-start theorem. -/
theorem normalizedFirstStart_explicit_correctedCurvature3_nonneg
    {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) (ht : 0 ≤ t) :
    0 ≤ correctedCurvature3 t
      (1 + firstStartRemainder u v t)
      (firstStartRemainderDeriv u v t)
      (firstStartRemainderDeriv2 u v t) := by
  have hsu : Real.sqrt u ≤ 1 := by nlinarith [Real.sqrt_nonneg v]
  have hsv : Real.sqrt v ≤ 1 := by nlinarith [Real.sqrt_nonneg u]
  have hu1 : u ≤ 1 := by
    nlinarith [Real.sq_sqrt hu, Real.sqrt_nonneg u]
  have hv1 : v ≤ 1 := by
    nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v]
  simpa [firstStartRemainder_deriv_eq hu hu1 hv hv1,
    firstStartRemainder_second_deriv_eq hu hu1 hv hv1,
    firstStartRemainderDeriv_deriv_eq hu hu1 hv hv1] using
    normalizedFirstStart_correctedCurvature3_nonneg hu hv hroot ht

/-- The normalized first-start function after rescaling time. -/
noncomputable def scaledFirstStart (u v scale t : ℝ) : ℝ :=
  1 + firstStartRemainder u v (scale * t)

noncomputable def scaledFirstStartDeriv (u v scale t : ℝ) : ℝ :=
  scale * firstStartRemainderDeriv u v (scale * t)

noncomputable def scaledFirstStartDeriv2 (u v scale t : ℝ) : ℝ :=
  scale ^ 2 * firstStartRemainderDeriv2 u v (scale * t)

theorem scaledFirstStart_hasDerivAt
    {u v scale t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    HasDerivAt (fun x : ℝ => 1 + firstStartRemainder u v (scale * x))
      (scale * firstStartRemainderDeriv u v (scale * t)) t := by
  have hlin : HasDerivAt (fun x : ℝ => scale * x) scale t := by
    simpa using (hasDerivAt_id t).const_mul scale
  have hrem :=
    (firstStartRemainder_hasDerivAt hu0 hu1 hv0 hv1 (t := scale * t)).comp t hlin
  simpa [Function.comp_def, mul_comm] using
    hrem.const_add 1

/-- Function-level time-scaled certificate, stated using actual derivatives. -/
theorem scaledFirstStart_correctedCurvature3_nonneg
    {u v scale t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1)
    (hscale : 0 ≤ scale) (ht : 0 ≤ t) :
    0 ≤ correctedCurvature3 t
      (1 + firstStartRemainder u v (scale * t))
      (deriv (fun x : ℝ => 1 + firstStartRemainder u v (scale * x)) t)
      (deriv (fun x => deriv
        (fun y : ℝ => 1 + firstStartRemainder u v (scale * y)) x) t) := by
  have hsu : Real.sqrt u ≤ 1 := by nlinarith [Real.sqrt_nonneg v]
  have hsv : Real.sqrt v ≤ 1 := by nlinarith [Real.sqrt_nonneg u]
  have hu1 : u ≤ 1 := by
    nlinarith [Real.sq_sqrt hu, Real.sqrt_nonneg u]
  have hv1 : v ≤ 1 := by
    nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v]
  have hD1 : ∀ x, deriv
      (fun y : ℝ => 1 + firstStartRemainder u v (scale * y)) x =
        scale * firstStartRemainderDeriv u v (scale * x) := fun x =>
    (scaledFirstStart_hasDerivAt hu hu1 hv hv1).deriv
  have hD2 : deriv
      (fun x : ℝ => scale * firstStartRemainderDeriv u v (scale * x)) t =
      scale ^ 2 * firstStartRemainderDeriv2 u v (scale * t) := by
    rw [deriv_const_mul_field]
    have hlin : HasDerivAt (fun x : ℝ => scale * x) scale t := by
      simpa using (hasDerivAt_id t).const_mul scale
    have hrem :=
      (firstStartRemainderDeriv_hasDerivAt hu hu1 hv hv1
        (t := scale * t)).comp t hlin
    rw [show deriv (fun x : ℝ => firstStartRemainderDeriv u v (scale * x)) t =
        firstStartRemainderDeriv2 u v (scale * t) * scale by
      simpa [Function.comp_def] using hrem.deriv]
    ring
  rw [hD1 t, show deriv (fun x => deriv
      (fun y : ℝ => 1 + firstStartRemainder u v (scale * y)) x) t =
      scale ^ 2 * firstStartRemainderDeriv2 u v (scale * t) by
    rw [show (fun x => deriv
        (fun y : ℝ => 1 + firstStartRemainder u v (scale * y)) x) =
        (fun x : ℝ => scale * firstStartRemainderDeriv u v (scale * x)) by
          funext x; exact hD1 x]
    exact hD2]
  apply correctedCurvature3_nonneg_of_time_scale
  exact normalizedFirstStart_explicit_correctedCurvature3_nonneg
    hu hv hroot (mul_nonneg hscale ht)

/-- Time rescaling of the normalized first-start certificate. -/
theorem scaledFirstStart_explicit_correctedCurvature3_nonneg
    {u v scale t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1)
    (hscale : 0 ≤ scale) (ht : 0 ≤ t) :
    0 ≤ correctedCurvature3 t
      (1 + firstStartRemainder u v (scale * t))
      (scale * firstStartRemainderDeriv u v (scale * t))
      (scale ^ 2 * firstStartRemainderDeriv2 u v (scale * t)) := by
  apply correctedCurvature3_nonneg_of_time_scale
  exact normalizedFirstStart_explicit_correctedCurvature3_nonneg hu hv hroot
    (mul_nonneg hscale ht)

/-- The full canonical normalization: positive amplitude, time rescaling,
and an arbitrary common exponential shift. -/
theorem canonicalRealFirst_explicit_correctedCurvature3_nonneg
    {u v amplitude scale shift t : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1)
    (hscale : 0 ≤ scale) (ht : 0 ≤ t) :
    let F := 1 + firstStartRemainder u v (scale * t)
    let F1 := scale * firstStartRemainderDeriv u v (scale * t)
    let F2 := scale ^ 2 * firstStartRemainderDeriv2 u v (scale * t)
    0 ≤ correctedCurvature3 t
      (amplitude * (Real.exp (shift * t) * F))
      (amplitude * (Real.exp (shift * t) * (F1 + shift * F)))
      (amplitude *
        (Real.exp (shift * t) * (F2 + 2 * shift * F1 + shift ^ 2 * F))) := by
  dsimp only
  apply correctedCurvature3_nonneg_of_amplitude
  apply correctedCurvature3_nonneg_of_exp_shift
  exact scaledFirstStart_explicit_correctedCurvature3_nonneg hu hv hroot hscale ht

/-- A convenient sufficient condition for the normalized-root constraint.
This is the form obtained after ordering three nonnegative real roots and
choosing the Perron root as scale. -/
theorem normalizedRootPair_admissible
    {root1 root2 root3 : ℝ}
    (hroot1 : 0 ≤ root1) (hroot2 : 0 ≤ root2) (hroot3 : 0 < root3)
    (hsum : root1 + root2 + 2 * Real.sqrt (root1 * root2) ≤ root3) :
    0 ≤ root1 / root3 ∧ 0 ≤ root2 / root3 ∧
      Real.sqrt (root1 / root3) + Real.sqrt (root2 / root3) ≤ 1 := by
  have hsqrt3 : 0 < Real.sqrt root3 := Real.sqrt_pos.2 hroot3
  have hsqrt1 : 0 ≤ Real.sqrt root1 := Real.sqrt_nonneg _
  have hsqrt2 : 0 ≤ Real.sqrt root2 := Real.sqrt_nonneg _
  have hsqrtMul : Real.sqrt (root1 * root2) =
      Real.sqrt root1 * Real.sqrt root2 := by
    rw [Real.sqrt_mul hroot1]
  have hsquare :
      (Real.sqrt root1 + Real.sqrt root2) ^ 2 ≤ (Real.sqrt root3) ^ 2 := by
    rw [add_sq, Real.sq_sqrt hroot1, Real.sq_sqrt hroot2,
      Real.sq_sqrt hroot3.le]
    rw [hsqrtMul] at hsum
    nlinarith
  have hsqrtSum :
      Real.sqrt root1 + Real.sqrt root2 ≤ Real.sqrt root3 := by
    nlinarith [sq_nonneg
      (Real.sqrt root3 - (Real.sqrt root1 + Real.sqrt root2))]
  refine ⟨div_nonneg hroot1 hroot3.le, div_nonneg hroot2 hroot3.le, ?_⟩
  rw [Real.sqrt_div hroot1, Real.sqrt_div hroot2]
  rw [← add_div]
  apply (div_le_one hsqrt3).2
  exact hsqrtSum

/-- For ordered nonnegative roots, the quadratic discriminant selects the
positive square-root branch.  This is the algebraic step that turns reality
of the two canonical rates into the compact root-simplex constraint. -/
theorem orderedRoots_sqrt_sum_le
    {root1 root2 root3 : ℝ}
    (hroot1 : 0 ≤ root1) (hroot12 : root1 ≤ root2)
    (hroot23 : root2 ≤ root3)
    (hdisc : 4 * root1 * root2 ≤ (root3 - root1 - root2) ^ 2) :
    Real.sqrt root1 + Real.sqrt root2 ≤ Real.sqrt root3 := by
  let x := Real.sqrt root1
  let y := Real.sqrt root2
  let z := Real.sqrt root3
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hxy : x ≤ y := by
    dsimp [x, y]
    exact Real.sqrt_le_sqrt hroot12
  have hyz : y ≤ z := by
    dsimp [y, z]
    exact Real.sqrt_le_sqrt hroot23
  have hx2 : x ^ 2 = root1 := Real.sq_sqrt hroot1
  have hy2 : y ^ 2 = root2 := Real.sq_sqrt (hroot1.trans hroot12)
  have hz2 : z ^ 2 = root3 := Real.sq_sqrt (hroot1.trans (hroot12.trans hroot23))
  by_contra hnot
  have hlt : z < x + y := lt_of_not_ge hnot
  have hdisc' : (2 * x * y) ^ 2 ≤ (z ^ 2 - x ^ 2 - y ^ 2) ^ 2 := by
    rw [hx2, hy2, hz2]
    nlinarith
  have hleft : 0 < 2 * x * y - (z ^ 2 - x ^ 2 - y ^ 2) := by
    nlinarith [sq_nonneg (x + y - z)]
  have hprod :
      (2 * x * y - (z ^ 2 - x ^ 2 - y ^ 2)) *
        (2 * x * y + (z ^ 2 - x ^ 2 - y ^ 2)) ≤ 0 := by
    nlinarith
  have hright : 2 * x * y + (z ^ 2 - x ^ 2 - y ^ 2) ≤ 0 := by
    by_contra hnotRight
    have hrightPos : 0 < 2 * x * y + (z ^ 2 - x ^ 2 - y ^ 2) :=
      lt_of_not_ge hnotRight
    have := mul_pos hleft hrightPos
    linarith
  nlinarith [sq_nonneg (z - (y - x)), sq_nonneg (y - x)]

/-- Root ratios of an ordered real canonical cubic automatically lie in the
admissible normalized chart once its discriminant inequality is known. -/
theorem orderedNormalizedRootPair_admissible
    {root1 root2 root3 : ℝ}
    (hroot1 : 0 ≤ root1) (hroot12 : root1 ≤ root2)
    (hroot23 : root2 ≤ root3) (hroot3 : 0 < root3)
    (hdisc : 4 * root1 * root2 ≤ (root3 - root1 - root2) ^ 2) :
    0 ≤ root1 / root3 ∧ 0 ≤ root2 / root3 ∧
      Real.sqrt (root1 / root3) + Real.sqrt (root2 / root3) ≤ 1 := by
  have hsqrt := orderedRoots_sqrt_sum_le hroot1 hroot12 hroot23 hdisc
  apply normalizedRootPair_admissible hroot1 (hroot1.trans hroot12) hroot3
  rw [Real.sqrt_mul hroot1]
  nlinarith [Real.sq_sqrt hroot1, Real.sq_sqrt (hroot1.trans hroot12),
    Real.sq_sqrt hroot3.le, Real.sqrt_nonneg root1,
    Real.sqrt_nonneg root2, Real.sqrt_nonneg root3]

/-- Ordered real roots of a cubic with nonnegative elementary symmetric
coefficients and positive largest root cannot have a negative lower pair. -/
theorem orderedRealRoots_nonneg_of_coefficients
    {root1 root2 root3 : ℝ}
    (hroot12 : root1 ≤ root2) (hroot23 : root2 ≤ root3)
    (hroot3 : 0 < root3)
    (hsum : 0 ≤ root1 + root2 + root3)
    (hpair : 0 ≤ root1 * root2 + root1 * root3 + root2 * root3)
    (hprod : 0 ≤ root1 * root2 * root3) :
    0 ≤ root1 := by
  by_contra hnot
  have hroot1neg : root1 < 0 := lt_of_not_ge hnot
  have hroot12prod : 0 ≤ root1 * root2 := by
    by_contra hnotProd
    have hprodNeg : root1 * root2 * root3 < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hnotProd) hroot3
    linarith
  have hroot2nonpos : root2 ≤ 0 := by
    by_contra hnotRoot2
    have h12neg : root1 * root2 < 0 :=
      mul_neg_of_neg_of_pos hroot1neg (lt_of_not_ge hnotRoot2)
    linarith
  let p := -(root1 + root2)
  have hp : 0 < p := by dsimp [p]; linarith
  have hple : p ≤ root3 := by dsimp [p]; linarith
  have hpPair : root3 * p ≤ root1 * root2 := by
    dsimp [p]
    nlinarith
  have hpSq : p ^ 2 ≤ root3 * p := by
    have := mul_le_mul_of_nonneg_right hple hp.le
    simpa [pow_two, mul_comm] using this
  have hupper : 4 * (root1 * root2) ≤ p ^ 2 := by
    dsimp [p]
    nlinarith [sq_nonneg (root1 - root2)]
  nlinarith

/-- The two coefficient identities for a monic cubic express the canonical
rate discriminant as the normalized-root discriminant. -/
theorem canonicalRoot_discriminant_identity
    {a b root1 root2 root3 : ℝ}
    (hsum : root1 + root2 + root3 = a + b)
    (hpair : root1 * root2 + root1 * root3 + root2 * root3 = a * b) :
    (root3 - root1 - root2) ^ 2 - 4 * root1 * root2 = (a - b) ^ 2 := by
  calc
    (root3 - root1 - root2) ^ 2 - 4 * root1 * root2 =
        (root1 + root2 + root3) ^ 2 -
          4 * (root1 * root2 + root1 * root3 + root2 * root3) := by ring
    _ = (a + b) ^ 2 - 4 * (a * b) := by rw [hsum, hpair]
    _ = (a - b) ^ 2 := by ring

/-- Complete root-domain bridge for the real-spectrum canonical cubic.  The
three displayed equalities are Vieta's identities for
`s (s-a) (s-b) - Q`; all analytic normalization hypotheses follow. -/
theorem canonicalOrderedRealRoots_admissible
    {a b Q root1 root2 root3 : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hQ : 0 ≤ Q)
    (hroot12 : root1 ≤ root2) (hroot23 : root2 ≤ root3)
    (hroot3 : 0 < root3)
    (hsum : root1 + root2 + root3 = a + b)
    (hpair : root1 * root2 + root1 * root3 + root2 * root3 = a * b)
    (hprod : root1 * root2 * root3 = Q) :
    0 ≤ root1 / root3 ∧ 0 ≤ root2 / root3 ∧
      Real.sqrt (root1 / root3) + Real.sqrt (root2 / root3) ≤ 1 := by
  have hroot1 : 0 ≤ root1 := orderedRealRoots_nonneg_of_coefficients
    hroot12 hroot23 hroot3 (by nlinarith [hsum, ha, hb])
    (by nlinarith [hpair, mul_nonneg ha hb]) (by nlinarith [hprod, hQ])
  have hdiscEq := canonicalRoot_discriminant_identity hsum hpair
  have hdisc : 4 * root1 * root2 ≤ (root3 - root1 - root2) ^ 2 := by
    nlinarith [sq_nonneg (a - b)]
  exact orderedNormalizedRootPair_admissible hroot1 hroot12 hroot23 hroot3 hdisc

/-- The checked normalized certificate applied directly to an ordered
real-root canonical cubic.  This is the pointwise first-start inequality in
the original time variable and with the common exponential/amplitude factors
restored. -/
theorem canonicalOrderedRealRoots_firstStart_nonneg
    {a b Q root1 root2 root3 amplitude shift t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hQ : 0 ≤ Q)
    (hroot12 : root1 ≤ root2) (hroot23 : root2 ≤ root3)
    (hroot3 : 0 < root3)
    (hsum : root1 + root2 + root3 = a + b)
    (hpair : root1 * root2 + root1 * root3 + root2 * root3 = a * b)
    (hprod : root1 * root2 * root3 = Q) (ht : 0 ≤ t) :
    let u := root1 / root3
    let v := root2 / root3
    let F := 1 + firstStartRemainder u v (root3 * t)
    let F1 := root3 * firstStartRemainderDeriv u v (root3 * t)
    let F2 := root3 ^ 2 * firstStartRemainderDeriv2 u v (root3 * t)
    0 ≤ correctedCurvature3 t
      (amplitude * (Real.exp (shift * t) * F))
      (amplitude * (Real.exp (shift * t) * (F1 + shift * F)))
      (amplitude *
        (Real.exp (shift * t) * (F2 + 2 * shift * F1 + shift ^ 2 * F))) := by
  dsimp only
  rcases canonicalOrderedRealRoots_admissible ha hb hQ hroot12 hroot23
      hroot3 hsum hpair hprod with ⟨hu, hv, hroot⟩
  exact canonicalRealFirst_explicit_correctedCurvature3_nonneg
    hu hv hroot hroot3.le ht

end SSP.K3CyclicRealTail
