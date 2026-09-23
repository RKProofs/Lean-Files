import SSPLean.K3AllStagesMiddleHigh

/-!
# Return-face reduction for the uniform `k = 3` induction

The nonpositive-current-slope branch is complete.  Consequently the return
face now depends only on the compact positive-slope polynomial certificate.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

/-! ### The active-gradient restriction on the return face -/

/-- After replacing `X = aY`, the return gradient is affine in `Y`; its
slope is exactly the positive return Hessian factor. -/
theorem uniformGradA_eq_at_a_one_add
    (n a T Y q : ℝ) :
    uniformGradA n a T Y q =
      uniformGradA n 1 T (a * Y) q
        + (Y - a * Y) * uniformHAA n a T Y q := by
  unfold uniformGradA uniformHAA
  ring

/-- In the induction coordinates `0 < a ≤ 1`, a negative active return
gradient remains negative after moving to `a = 1`, `Y = aY`.  This removes
the inessential separate dependence on `a` and `Y` from the remaining
positive-slope analysis. -/
theorem uniformGradA_at_a_one_neg_of_neg
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hY : 0 < Y) (hq : 0 ≤ q)
    (hgrad : uniformGradA n a T Y q < 0) :
    uniformGradA n 1 T (a*Y) q < 0 := by
  let m := n-4
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hH : 0 < uniformHAA n a T Y q := by
    rw [← hnid]
    unfold uniformHAA
    ring_nf
    positivity
  have hYX : 0 ≤ Y - a * Y := by
    rw [show Y - a * Y = Y * (1 - a) by ring]
    positivity
  rw [uniformGradA_eq_at_a_one_add] at hgrad
  nlinarith [mul_nonneg hYX hH.le]

/-- Denominator-cleared active-gradient polynomial at the same projective
point used by `uniformFaceACurrentScaled`. -/
noncomputable def uniformFaceACurrentGradScaled
    (n T q w : ℝ) : ℝ :=
  n * (uniformFaceACurrentM n T q)^2 *
    uniformGradA n 1 T
      (w * uniformFaceACurrentK n T q /
        (n * uniformFaceACurrentM n T q)) q

/-! The two projectively scaled expressions above have removable
denominators.  Keeping their polynomial continuations explicit is useful for
the remaining semialgebraic certificates. -/

noncomputable def uniformFaceACurrentPoly
    (n T q w : ℝ) : ℝ :=
  n^3 * (uniformFaceACurrentM n T q)^3 *
      uniformFaceACoreXC0 n T q
    + n^2 * (uniformFaceACurrentM n T q)^2 * w *
      uniformFaceACurrentK n T q * uniformFaceACoreXC1 n T q
    + n * uniformFaceACurrentM n T q * w^2 *
      (uniformFaceACurrentK n T q)^2 * uniformFaceACoreXC2 n T q
    + w^3 * (uniformFaceACurrentK n T q)^3 *
      uniformFaceACoreXC3 n T q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem uniformFaceACurrentScaled_eq_poly
    (n T q w : ℝ) (hn : n ≠ 0)
    (hM : uniformFaceACurrentM n T q ≠ 0) :
    uniformFaceACurrentScaled n T q w =
      uniformFaceACurrentPoly n T q w := by
  unfold uniformFaceACurrentScaled uniformFaceACurrentPoly
  unfold uniformFaceACoreXC0 uniformFaceACoreXC1
  unfold uniformFaceACoreXC2 uniformFaceACoreXC3
  unfold uniformFaceACore
  field_simp [hn, hM]
  ring

noncomputable def uniformGradACurrentC0 (n T q : ℝ) : ℝ :=
  uniformGradA n 1 T 0 q

noncomputable def uniformGradACurrentC1 (n T q : ℝ) : ℝ :=
  uniformGradA n 1 T 1 q - uniformGradA n 1 T 0 q - n

theorem uniformGradA_at_a_one_power (n T X q : ℝ) :
    uniformGradA n 1 T X q =
      n * X^2 + uniformGradACurrentC1 n T q * X
        + uniformGradACurrentC0 n T q := by
  unfold uniformGradACurrentC0 uniformGradACurrentC1 uniformGradA
  ring

noncomputable def uniformFaceACurrentGradPoly
    (n T q w : ℝ) : ℝ :=
  w^2 * (uniformFaceACurrentK n T q)^2
    + uniformFaceACurrentM n T q * w *
      uniformFaceACurrentK n T q * uniformGradACurrentC1 n T q
    + n * (uniformFaceACurrentM n T q)^2 *
      uniformGradACurrentC0 n T q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem uniformFaceACurrentGradScaled_eq_poly
    (n T q w : ℝ) (hn : n ≠ 0)
    (hM : uniformFaceACurrentM n T q ≠ 0) :
    uniformFaceACurrentGradScaled n T q w =
      uniformFaceACurrentGradPoly n T q w := by
  unfold uniformFaceACurrentGradScaled uniformFaceACurrentGradPoly
  rw [uniformGradA_at_a_one_power]
  field_simp [hn, hM]

/-- Version of the current-slope reduction which retains the active-gradient
condition at the projective point.  This is the exact condition needed by the
KKT application and avoids requiring positivity at irrelevant points of the
ambient `(q,w)` box. -/
theorem uniformFaceACore_nonneg_of_current_scaled_of_grad
    (n a T Y q : ℝ) (hn : 0 < n) (ha : 0 < a) (hY : 0 < Y)
    (hM : 0 < uniformFaceACurrentM n T q)
    (hK : 0 < uniformFaceACurrentK n T q)
    (hreturn : uniformReturnSide n a T Y q ≤ 0)
    (hgrad : uniformGradA n 1 T (a * Y) q < 0)
    (hcert : ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      uniformFaceACurrentGradScaled n T q w < 0 →
      0 ≤ uniformFaceACurrentScaled n T q w) :
    0 ≤ uniformFaceACore n (a * Y) T q := by
  let w := n * (a * Y) * uniformFaceACurrentM n T q /
    uniformFaceACurrentK n T q
  obtain ⟨hw, hw1⟩ := uniformFaceACurrent_ratio_mem_unit
    n a T Y q hn ha hY hM hK hreturn
  have hXid : w * uniformFaceACurrentK n T q /
      (n * uniformFaceACurrentM n T q) = a * Y := by
    dsimp [w]
    field_simp [hn.ne', hM.ne', hK.ne']
  have hgradScaled : uniformFaceACurrentGradScaled n T q w < 0 := by
    unfold uniformFaceACurrentGradScaled
    rw [hXid]
    exact mul_neg_of_pos_of_neg (by positivity) hgrad
  have hscaled := hcert w hw hw1 hgradScaled
  unfold uniformFaceACurrentScaled at hscaled
  rw [hXid] at hscaled
  have hscale : 0 < n^3 * (uniformFaceACurrentM n T q)^3 := by
    positivity
  exact (mul_nonneg_iff_of_pos_left hscale).mp hscaled

/-- Polynomial-continuation form of the active-gradient reduction.  This is
the form used by the chart certificates, so they never need to normalize the
projective divisions themselves. -/
theorem uniformFaceACore_nonneg_of_current_poly_of_grad
    (n a T Y q : ℝ) (hn : 0 < n) (ha : 0 < a) (hY : 0 < Y)
    (hM : 0 < uniformFaceACurrentM n T q)
    (hK : 0 < uniformFaceACurrentK n T q)
    (hreturn : uniformReturnSide n a T Y q ≤ 0)
    (hgrad : uniformGradA n 1 T (a * Y) q < 0)
    (hcert : ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      uniformFaceACurrentGradPoly n T q w < 0 →
      0 ≤ uniformFaceACurrentPoly n T q w) :
    0 ≤ uniformFaceACore n (a * Y) T q := by
  apply uniformFaceACore_nonneg_of_current_scaled_of_grad
    n a T Y q hn ha hY hM hK hreturn hgrad
  intro w hw hw1 hgradScaled
  have hgradPoly : uniformFaceACurrentGradPoly n T q w < 0 := by
    rw [← uniformFaceACurrentGradScaled_eq_poly n T q w hn.ne' hM.ne']
    exact hgradScaled
  have hpoly := hcert w hw hw1 hgradPoly
  rwa [uniformFaceACurrentScaled_eq_poly n T q w hn.ne' hM.ne']

/-- The conditional return-face inequality, with only its positive-current-
slope compact certificate left as an input. -/
theorem uniformSharpFaceA_nonneg_of_returnSide_of_positive_certificate
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hgrad : uniformGradA n a T Y q < 0)
    (hreturn : uniformReturnSide n a T Y q ≤ 0)
    (hcertPos : ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      uniformFaceACurrentGradPoly n T q w < 0 →
      0 ≤ uniformFaceACurrentPoly n T q w) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  have hgrad1 := uniformGradA_at_a_one_neg_of_neg
    n a T Y q hn ha ha1 hT.le hY hq.le hgrad
  by_cases hT1 : T ≤ n - 1
  · exact uniformSharpFaceA_nonneg_of_T_le
      n a T Y q hn ha hT hT1 hY hq hq1
  by_cases hM : 0 < uniformFaceACurrentM n T q
  · have hK := uniformFaceACurrentK_pos n T q hn (by linarith) hq.le hq1
    have hcore := uniformFaceACore_nonneg_of_current_poly_of_grad
      n a T Y q (by linarith) ha hY hM hK hreturn hgrad1 hcertPos
    apply uniformSharpFaceA_nonneg_of_num n a T Y q hn ha hT hY hq
    have hm2 : 0 ≤ uniformCornerM2Num n a T Y q := by
      unfold uniformCornerM2Num
      have hn1 : 0 ≤ n - 1 := by linarith
      have hTq : 0 ≤ T * q := by positivity
      have hcross : 0 ≤ 2 * (n - 1) * (T * q) := by positivity
      have hmain : 0 ≤ n * T^2 * q := by positivity
      have hay : 0 ≤ n * a * Y := by positivity
      nlinarith
    rw [uniformFaceANum_factor]
    positivity
  · exact uniformSharpFaceA_nonneg_of_currentM_nonpos_complete
      n a T Y q hn ha hT (by linarith) hY hq (le_of_not_gt hM)

/-- The full mixture-coordinate induction step after eliminating the corner,
interior KKT point, and nonpositive-current-slope return branch. -/
theorem excursionReducedGap_mixture_coordinates_nonneg_of_remaining_certificates
    (n a T Y p q C D : ℝ)
    (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hp : 0 < p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hC : (n+1)*(n*p*Y^2/(n-1))^2 ≤ n*(p*Y)*C)
    (hD : (n+1)*(n*q*T^2/(n-1))^2 ≤ n*(q*T)*D)
    (hcertPos : ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      uniformFaceACurrentGradPoly n T q w < 0 →
      0 ≤ uniformFaceACurrentPoly n T q w)
    (hfaceB : 0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformSharpFaceB n a T Y q) :
    0 ≤ excursionReducedGap n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) C (q*T) (n*q*T^2/(n-1)) D := by
  apply excursionReducedGap_mixture_coordinates_nonneg_of_uniform_faces
    n a T Y p q C D hn ha ha1 hT hY hp hp1 hq hq1 hC hD
  · intro hgrad hreturn
    exact uniformSharpFaceA_nonneg_of_returnSide_of_positive_certificate
      n a T Y q hn ha ha1 hT hY hq hq1 hgrad hreturn hcertPos
  · exact hfaceB

end SSP.K3AllStages
