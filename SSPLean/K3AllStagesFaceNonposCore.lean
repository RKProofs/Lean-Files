import SSPLean.K3AllStagesFaceNonposCurrent
set_option autoImplicit false
namespace SSP.K3AllStages
open SSP.K3S4Renewal SSP.K3S4KKT
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- Exact Bernstein expansion of the no-return edge of the sharp corner. -/
theorem uniformSharpGap_at_a_zero_identity
    (n T Y q : ℝ) (_hn0 : n ≠ 0) (hn1 : n-1 ≠ 0)
    (_hnp1 : n+1 ≠ 0) (_hT : T ≠ 0) (hY : Y ≠ 0) (_hq : q ≠ 0) :
    (n-1)^4*uniformSharpGap n 0 T Y q =
      uniformCornerA0 (n-4) T q := by
  unfold uniformSharpGap sharpGap sharpThird excursionReducedGap stageGap
  unfold geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4
  unfold uniformCornerA0 uniformCornerQ0B0 uniformCornerA0B1 uniformCornerA0B2
  field_simp [hn1, hY]
  ring

theorem uniformSharpGap_at_a_zero_nonneg
    (n T Y q : ℝ) (hn : 4 ≤ n) (hT : 0 < T) (hY : 0 < Y)
    (hq : 0 < q) (hq1 : q ≤ 1) : 0 ≤ uniformSharpGap n 0 T Y q := by
  have hq0 := uniformCornerA0_nonneg (n-4) T q (by linarith) hT.le hq.le hq1
  have hid := uniformSharpGap_at_a_zero_identity n T Y q
    (by linarith) (by linarith) (by linarith) hT.ne' hY.ne' hq.ne'
  have hn1p : 0 < n-1 := by linarith
  have hscale : 0 < (n-1)^4 := by positivity
  have hscaled : 0 ≤ (n-1)^4*uniformSharpGap n 0 T Y q := by
    rw [hid]
    exact hq0
  exact (mul_nonneg_iff_of_pos_left hscale).mp hscaled

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The return mixture weight disappears completely from the normalized
sharp-corner gap. -/
theorem sharpGap_mixture_coordinates
    (n a T Y p q : ℝ) (_hn0 : n ≠ 0) (hn1 : n-1 ≠ 0)
    (_hnp1 : n+1 ≠ 0) (_hT : T ≠ 0) (hY : Y ≠ 0)
    (hp : p ≠ 0) (_hq : q ≠ 0) (hsum : p*Y+a ≠ 0)
    (hsum1 : Y+a ≠ 0) :
    sharpGap n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) =
      uniformSharpGap n a T Y q := by
  unfold uniformSharpGap sharpGap sharpThird excursionReducedGap stageGap
  unfold geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4
  field_simp [hn1, hY, hp, hsum, hsum1]
  ring

theorem uniformSideFactor_pos
    (n a T Y q : ℝ) (hn : 2 ≤ n) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hY : 0 ≤ Y) (hq : 0 ≤ q) :
    0 < uniformSideFactor n a T Y q := by
  unfold uniformSideFactor
  have hTq : 0 ≤ T*q := mul_nonneg hT hq
  have hmain : 0 ≤ n*T^2*q := by positivity
  have hcross : 0 ≤ 2*n*T*q-2*T*q := by
    have hn1 : 0 ≤ n-1 := by linarith
    have : 0 ≤ 2*(n-1)*(T*q) := by positivity
    nlinarith
  have hay : 0 ≤ n*a*Y := by positivity
  nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem sharpGradA_mixture_coordinates
    (n a T Y p q : ℝ) (hn0 : n ≠ 0) (hn1 : n-1 ≠ 0) (hnp1 : n+1 ≠ 0)
    (_hT : T ≠ 0) (hY : Y ≠ 0) (hp : p ≠ 0) (_hq : q ≠ 0)
    (hsum : p*Y+a ≠ 0) :
    sharpGradA n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) =
      2*a*uniformGradA n a T Y q/(Y*p*(n-1)^2) := by
  unfold sharpGradA sharpThird excursionGradA excursionHAA
  unfold excursionReducedGap stageGap hessianCore
  unfold geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4 uniformGradA
  have hsq : a*Y*p*2+a^2+Y^2*p^2 ≠ 0 := by
    convert pow_ne_zero 2 hsum using 1
    all_goals ring
  field_simp [hn0, hn1, hnp1, hY, hp, hsum, hsq]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem sharpGradB_mixture_coordinates
    (n a T Y p q : ℝ) (hn0 : n ≠ 0) (hn1 : n-1 ≠ 0) (hnp1 : n+1 ≠ 0)
    (hT : T ≠ 0) (hY : Y ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hsum : p*Y+a ≠ 0) :
    sharpGradB n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) =
      -2*uniformGradB n a T Y q/(n-1)^2 := by
  unfold sharpGradB sharpThird excursionGradB excursionHBB
  unfold excursionReducedGap stageGap hessianCore
  unfold geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4 uniformGradB
  have hsq : a*Y*p*2+a^2+Y^2*p^2 ≠ 0 := by
    convert pow_ne_zero 2 hsum using 1
    all_goals ring
  field_simp [hn0, hn1, hnp1, hT, hY, hp, hq, hsum, hsq]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem excursionHAA_mixture_coordinates
    (n a T Y p q : ℝ) (hn0 : n ≠ 0) (hn1 : n-1 ≠ 0) (hnp1 : n+1 ≠ 0)
    (hY : Y ≠ 0) (hp : p ≠ 0) (hsum : p*Y+a ≠ 0) :
    excursionHAA n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) =
      2*a*uniformHAA n a T Y q/(Y^3*n*p^2*(n+1)) := by
  unfold excursionHAA hessianCore uniformHAA
  have hsq : a*Y*p*2+a^2+Y^2*p^2 ≠ 0 := by
    convert pow_ne_zero 2 hsum using 1
    all_goals ring
  field_simp [hn0, hn1, hnp1, hY, hp, hsum, hsq]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem excursionHBB_mixture_coordinates
    (n a T Y p q : ℝ) (hn0 : n ≠ 0) (hn1 : n-1 ≠ 0) (hnp1 : n+1 ≠ 0)
    (hT : T ≠ 0) (hY : Y ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hsum : p*Y+a ≠ 0) :
    excursionHBB n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) =
      2*uniformHBB n a T Y q/(T^2*n*q*(n+1)) := by
  unfold excursionHBB hessianCore uniformHBB
  have hsq : a*Y*p*2+a^2+Y^2*p^2 ≠ 0 := by
    convert pow_ne_zero 2 hsum using 1
    all_goals ring
  field_simp [hn0, hn1, hnp1, hT, hY, hp, hq, hsum, hsq]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The normalized return-face discriminant has only the positive factor
`p⁻²` left from the return mixture weight. -/
theorem sharpFaceA_mixture_coordinates
    (n a T Y p q : ℝ) (hn0 : n ≠ 0) (hn1 : n-1 ≠ 0)
    (hnp1 : n+1 ≠ 0) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hsum : p*Y+a ≠ 0)
    (hsum1 : Y+a ≠ 0) :
    p^2*sharpFaceA n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) =
      uniformSharpFaceA n a T Y q := by
  have hgap1 := sharpGap_mixture_coordinates n a T Y 1 q hn0 hn1 hnp1
    hT hY (by norm_num) hq (by simpa using hsum1) hsum1
  have hgrad1 := sharpGradA_mixture_coordinates n a T Y 1 q hn0 hn1 hnp1
    hT hY (by norm_num) hq (by simpa using hsum1)
  have hhaa1 := excursionHAA_mixture_coordinates n a T Y 1 q hn0 hn1 hnp1
    hY (by norm_num) (by simpa using hsum1)
  norm_num at hgap1 hgrad1 hhaa1
  unfold uniformSharpFaceA sharpFaceA
  rw [sharpGap_mixture_coordinates n a T Y p q hn0 hn1 hnp1 hT hY hp hq hsum hsum1,
    sharpGradA_mixture_coordinates n a T Y p q hn0 hn1 hnp1 hT hY hp hq hsum,
    excursionHAA_mixture_coordinates n a T Y p q hn0 hn1 hnp1 hY hp hsum,
    hgap1, hgrad1, hhaa1]
  field_simp [hn0, hn1, hnp1, hY, hp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- Denominator-clearing identity connecting the return-face discriminant to
its compact polynomial numerator. -/
theorem uniformSharpFaceA_num_identity
    (n a T Y q : ℝ) (hn0 : n ≠ 0) (hn1 : n-1 ≠ 0)
    (hnp1 : n+1 ≠ 0) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hq : q ≠ 0) (hsum : Y+a ≠ 0) :
    Y^3*n*(n+1)*(n-1)^4*uniformSharpFaceA n a T Y q =
      4*a*uniformFaceANum n a T Y q := by
  have hgap1 := sharpGap_mixture_coordinates n a T Y 1 q hn0 hn1 hnp1
    hT hY (by norm_num) hq (by simpa using hsum) hsum
  have hgrad1 := sharpGradA_mixture_coordinates n a T Y 1 q hn0 hn1 hnp1
    hT hY (by norm_num) hq (by simpa using hsum)
  have hhaa1 := excursionHAA_mixture_coordinates n a T Y 1 q hn0 hn1 hnp1
    hY (by norm_num) (by simpa using hsum)
  norm_num at hgap1 hgrad1 hhaa1
  unfold uniformSharpFaceA sharpFaceA
  rw [hgap1, hgrad1, hhaa1]
  have hgap := uniformSharpGap_eq_cornerPoly n a T Y q
    hn0 hn1 hnp1 hT hY hq hsum
  unfold uniformFaceANum
  field_simp [hn0, hn1, hnp1, hY]
  rw [← hgap]
  ring

/-- Positivity of the polynomial numerator implies the normalized return-face
certificate in the genuine interior. -/
theorem uniformSharpFaceA_nonneg_of_num
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q)
    (hnum : 0 ≤ uniformFaceANum n a T Y q) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  have hid := uniformSharpFaceA_num_identity n a T Y q
    (by linarith) (by linarith) (by linarith) hT.ne' hY.ne' hq.ne'
    (by positivity)
  have hnpos : 0 < n := by linarith
  have hn1pos : 0 < n-1 := by linarith
  have hnp1pos : 0 < n+1 := by linarith
  have hscale : 0 < Y^3*n*(n+1)*(n-1)^4 := by positivity
  have hrhs : 0 ≤ 4*a*uniformFaceANum n a T Y q := by positivity
  rw [← hid] at hrhs
  exact (mul_nonneg_iff_of_pos_left hscale).mp hrhs

/-- On the unbounded half with positive return slope, the conditional
return-face proof is reduced to a polynomial certificate on `0 ≤ w ≤ 1` at
the current mixture weight. -/
theorem uniformSharpFaceA_nonneg_of_current_scaled
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hT1 : n-1 ≤ T) (hY : 0 < Y)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hM : 0 < uniformFaceACurrentM n T q)
    (hreturn : uniformReturnSide n a T Y q ≤ 0)
    (hcert : ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      0 ≤ uniformFaceACurrentScaled n T q w) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  have hn0 : 0 < n := by linarith
  have hK := uniformFaceACurrentK_pos n T q hn hT1 hq.le hq1
  have hcore := uniformFaceACore_nonneg_of_current_scaled
    n a T Y q hn0 ha hY hM hK hreturn hcert
  apply uniformSharpFaceA_nonneg_of_num n a T Y q hn ha hT hY hq
  have hm2 : 0 ≤ uniformCornerM2Num n a T Y q := by
    unfold uniformCornerM2Num
    have hn1 : 0 ≤ n-1 := by linarith
    have hTq : 0 ≤ T*q := by positivity
    have hcross : 0 ≤ 2*(n-1)*(T*q) := by positivity
    have hmain : 0 ≤ n*T^2*q := by positivity
    have hay : 0 ≤ n*a*Y := by positivity
    nlinarith
  rw [uniformFaceANum_factor]
  positivity

/-- On the unbounded half with nonpositive current return slope, the
surplus/root box certificate proves the normalized return-face inequality. -/
theorem uniformSharpFaceA_nonneg_of_currentM_nonpos
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hT1 : n-1 ≤ T) (hY : 0 < Y)
    (hq : 0 < q) (hM : uniformFaceACurrentM n T q ≤ 0)
    (hcert : ∀ m s v X : ℝ, 0 ≤ m → 0 ≤ s → 0 ≤ v → v ≤ 1 →
      0 ≤ X → 0 ≤ uniformFaceANonposScaled m s v X) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  have hcore := uniformFaceACore_nonneg_of_currentM_nonpos
    n (a*Y) T q hn (by positivity) hT1 hq hM hcert
  have hnum := uniformFaceANum_nonneg_of_core
    n a T Y q hn ha.le hT.le hY.le hq.le hcore
  exact uniformSharpFaceA_nonneg_of_num n a T Y q hn ha hT hY hq hnum

/-- The nonpositive-current-slope return face is now complete whenever
`aY ≤ 1`; no external polynomial certificate is needed in this range. -/
theorem uniformSharpFaceA_nonneg_of_currentM_nonpos_of_mul_le_one
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hT1 : n-1 ≤ T) (hY : 0 < Y)
    (hq : 0 < q) (hM : uniformFaceACurrentM n T q ≤ 0)
    (haY1 : a*Y ≤ 1) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  have hcore := uniformFaceACore_nonneg_of_currentM_nonpos_of_X_le_one
    n (a*Y) T q hn (by positivity) haY1 hT1 hq hM
  have hnum := uniformFaceANum_nonneg_of_core
    n a T Y q hn ha.le hT.le hY.le hq.le hcore
  exact uniformSharpFaceA_nonneg_of_num n a T Y q hn ha hT hY hq hnum

/-- The two current-slope polynomial certificates together discharge the
return face on `T ≥ n-1`; the return-side hypothesis is needed only in the
positive-slope branch. -/
theorem uniformSharpFaceA_nonneg_of_current_certificates
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hT1 : n-1 ≤ T) (hY : 0 < Y)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hreturn : uniformReturnSide n a T Y q ≤ 0)
    (hcertPos : ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      0 ≤ uniformFaceACurrentScaled n T q w)
    (hcertNonpos : ∀ m s v X : ℝ,
      0 ≤ m → 0 ≤ s → 0 ≤ v → v ≤ 1 → 0 ≤ X →
      0 ≤ uniformFaceANonposScaled m s v X) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  by_cases hM : 0 < uniformFaceACurrentM n T q
  · exact uniformSharpFaceA_nonneg_of_current_scaled
      n a T Y q hn ha hT hT1 hY hq hq1 hM hreturn hcertPos
  · exact uniformSharpFaceA_nonneg_of_currentM_nonpos
      n a T Y q hn ha hT hT1 hY hq (le_of_not_gt hM) hcertNonpos

/-- Consequently the normalized return-face KKT certificate has only the
full-terminal-mixture endpoint `q = 1` left to prove. -/
theorem uniformSharpFaceA_nonneg_of_q_one
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (h3 : 0 ≤ uniformFaceAQB3 n (a*Y) T) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  apply uniformSharpFaceA_nonneg_of_num n a T Y q hn ha hT hY hq
  exact uniformFaceANum_nonneg_of_q_one n a T Y q hn ha.le hT.le hY.le
    hq.le hq1 h3

/-- The return-face KKT discriminant is completely discharged on the compact
half `T ≤ n-1`. -/
theorem uniformSharpFaceA_nonneg_of_T_le
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hT1 : T ≤ n-1) (hY : 0 < Y)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  apply uniformSharpFaceA_nonneg_of_q_one n a T Y q hn ha hT hY hq hq1
  exact uniformFaceAQB3_nonneg_of_T_le n (a*Y) T hn (by positivity) hT.le hT1

/-- On the unbounded half, the active return-side condition at the terminal
Bernstein endpoint supplies exactly the upper bound needed by the return-face
numerator. -/
theorem uniformSharpFaceA_nonneg_of_T_ge_of_returnSide_at_one
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hT1 : n-1 ≤ T) (hY : 0 < Y)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hreturn : uniformReturnSide n a T Y 1 ≤ 0) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  apply uniformSharpFaceA_nonneg_of_q_one n a T Y q hn ha hT hY hq hq1
  exact uniformFaceAQB3_nonneg_of_T_ge_of_returnSide_nonpos
    n a T Y hn ha hT1 hY hreturn

/-- Complete return-face certificate once its endpoint return-side condition
is available.  On the compact half that condition is not needed. -/
theorem uniformSharpFaceA_nonneg_of_returnSide_at_one
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hreturn : uniformReturnSide n a T Y 1 ≤ 0) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  by_cases hT1 : T ≤ n-1
  · exact uniformSharpFaceA_nonneg_of_T_le
      n a T Y q hn ha hT hT1 hY hq hq1
  · exact uniformSharpFaceA_nonneg_of_T_ge_of_returnSide_at_one
      n a T Y q hn ha hT (by linarith) hY hq hq1 hreturn

/-- The complete conditional return-face certificate in the branch where the
return-side interpolation decreases toward `q = 1`. -/
theorem uniformSharpFaceA_nonneg_of_returnSide_of_slope_nonpos
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hreturn : uniformReturnSide n a T Y q ≤ 0)
    (hslope : uniformReturnEndpointSlope n a T Y ≤ 0) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  apply uniformSharpFaceA_nonneg_of_returnSide_at_one
    n a T Y q hn ha hT hY hq hq1
  exact uniformReturnSide_one_nonpos_of_slope_nonpos
    n a T Y q hT.le hq1 hreturn hslope

/-- Complete return-face implication from the two current-`q` polynomial
certificates.  The compact half is already unconditional. -/
theorem uniformSharpFaceA_nonneg_of_returnSide_of_current_certificates
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hreturn : uniformReturnSide n a T Y q ≤ 0)
    (hcertPos : ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      0 ≤ uniformFaceACurrentScaled n T q w)
    (hcertNonpos : ∀ m s v X : ℝ,
      0 ≤ m → 0 ≤ s → 0 ≤ v → v ≤ 1 → 0 ≤ X →
      0 ≤ uniformFaceANonposScaled m s v X) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  by_cases hT1 : T ≤ n-1
  · exact uniformSharpFaceA_nonneg_of_T_le
      n a T Y q hn ha hT hT1 hY hq hq1
  · exact uniformSharpFaceA_nonneg_of_current_certificates
      n a T Y q hn ha hT (by linarith) hY hq hq1 hreturn
      hcertPos hcertNonpos


end SSP.K3AllStages
