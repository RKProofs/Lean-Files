import SSPLean.K3AllStagesFaceNonposEndpointC0
import SSPLean.K3AllStagesFaceNonposEndpointC1
import SSPLean.K3AllStagesFaceNonposEndpointC2
import SSPLean.K3AllStagesFaceNonposEndpointC3
set_option autoImplicit false
namespace SSP.K3AllStages
open SSP.K3S4Renewal SSP.K3S4KKT
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformFaceANonposXC2_bernstein_v (m s v : ℝ) :
    uniformFaceANonposXC2 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun w => uniformFaceANonposXC2 m s w))
        (uniformCubicSampleB1 (fun w => uniformFaceANonposXC2 m s w))
        (uniformCubicSampleB2 (fun w => uniformFaceANonposXC2 m s w))
        (uniformCubicSampleB3 (fun w => uniformFaceANonposXC2 m s w)) v := by
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposXC2 uniformFaceACoreXC2
  unfold uniformFaceANonposQ cornerBern3
  simp only [FaceCoreProduct_eq]
  unfold FaceCoreProduct
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceANonposXC2_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposXC2 m s v := by
  rw [uniformFaceANonposXC2_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    simp only [uniformCubicSampleB0, uniformCubicSampleB1,
      uniformCubicSampleB2, uniformCubicSampleB3]
    simp only [NonposXC2_sample, NonposCompactPolynomial_eq m s _ _ hm hs]
    unfold NonposCompactPolynomial
    ring_nf
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceANonposXC3_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ uniformFaceANonposXC3 m s v := by
  rw [NonposXC3_sample]
  simp only [NonposCompactPolynomial_eq m s _ _ hm hs]
  unfold NonposCompactPolynomial
  ring_nf
  positivity

noncomputable def uniformFaceANonposDeriv
    (m s v R : ℝ) : ℝ :=
  uniformFaceANonposXC1 m s v
    +2*uniformFaceANonposXC2 m s v*R
    +3*uniformFaceANonposXC3 m s v*R^2

/-- Once the surplus/root cubic has nonnegative value and derivative at a
nonnegative point `R`, its nonnegative quadratic and cubic coefficients make
it nonnegative on the entire ray `X ≥ R`. -/
theorem uniformFaceANonposScaled_nonneg_of_base
    (m s v R X : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hR : 0 ≤ R) (hRX : R ≤ X)
    (hvalue : 0 ≤ uniformFaceANonposScaled m s v R)
    (hderiv : 0 ≤ uniformFaceANonposDeriv m s v R) :
    0 ≤ uniformFaceANonposScaled m s v X := by
  have hdiff : 0 ≤ X-R := sub_nonneg.mpr hRX
  have hc2 := uniformFaceANonposXC2_nonneg m s v hm hs hv hv1
  have hc3 := uniformFaceANonposXC3_nonneg m s v hm hs
  have hXR : 0 ≤ X+2*R := by linarith
  have hlin := mul_nonneg hdiff hderiv
  have hquad := mul_nonneg hdiff (mul_nonneg hdiff
    (add_nonneg hc2 (mul_nonneg hc3 hXR)))
  rw [uniformFaceANonposScaled_power]
  rw [uniformFaceANonposScaled_power] at hvalue
  unfold uniformFaceANonposDeriv at hderiv
  nlinarith

/-- A single endpoint-slope inequality suffices on the far tail.  Its four
`v`-Bernstein coefficients are coefficientwise nonnegative; they are kept as
the remaining factored certificate rather than expanded in this large file. -/
theorem uniformFaceANonposScaled_nonneg_of_tailSlope
    (m s v X : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hPX : uniformFaceANonposP m/8 ≤ X)
    (hslope : 0 ≤ uniformFaceANonposXC1 m s v
      +(uniformFaceANonposP m/8)*uniformFaceANonposXC2 m s v) :
    0 ≤ uniformFaceANonposScaled m s v X := by
  have hP : 0 ≤ uniformFaceANonposP m := by
    unfold uniformFaceANonposP
    positivity
  have hX : 0 ≤ X := le_trans (by positivity) hPX
  have hc0 : 0 ≤ uniformFaceANonposXC0 m s v := by
    have h0 := uniformFaceANonposScaled_nonneg_of_X_le_one
      m s v 0 hm hs hv hv1 (by norm_num) (by norm_num)
    rw [uniformFaceANonposScaled_power] at h0
    norm_num at h0
    exact h0
  have hc2 := uniformFaceANonposXC2_nonneg m s v hm hs hv hv1
  have hc3 := uniformFaceANonposXC3_nonneg m s v hm hs
  have hgap : 0 ≤ X-uniformFaceANonposP m/8 := sub_nonneg.mpr hPX
  have hlinear := mul_nonneg hX hslope
  have hquadratic := mul_nonneg (mul_nonneg hX hgap) hc2
  have hcubic := mul_nonneg (mul_nonneg (sq_nonneg X) hX) hc3
  rw [uniformFaceANonposScaled_power]
  nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem uniformFaceACurrentM_nonpos_shift_identity (m s q : ℝ)
    (hm6 : m+6 ≠ 0) :
    uniformFaceACurrentM (m+4) (uniformFaceANonposT m s) q =
      -(m+6)*s+q*(m+3)*(m+7)*(m+8)*uniformFaceANonposT m s := by
  unfold uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP
  unfold uniformFaceACurrentM uniformReturnM
  field_simp [hm6]
  ring

/-- Every point in the `M(q) ≤ 0` branch has the surplus/root
parameterization used by `uniformFaceANonposScaled`. -/
theorem uniformFaceACurrentM_nonpos_parameterization
    (m z q : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) (hq : 0 < q)
    (hM : uniformFaceACurrentM (m+4) (m+3+z) q ≤ 0) :
    ∃ s v : ℝ, 0 ≤ s ∧ 0 ≤ v ∧ v ≤ 1 ∧
      z = uniformFaceANonposZ m s ∧ q = uniformFaceANonposQ m s v := by
  have hm6 : 0 < m+6 := by linarith
  let s := z-uniformFaceANonposP m/(m+6)
  have hs : 0 ≤ s := by
    dsimp [s]
    rw [sub_nonneg, div_le_iff₀ hm6]
    simpa [uniformFaceANonposP, mul_comm] using
      uniformFaceACurrentM_nonpos_surplus_bound m z q hm hz hq.le hM
  have hzid : z = uniformFaceANonposZ m s := by
    dsimp [s]
    unfold uniformFaceANonposZ
    ring
  have hTid : m+3+z = uniformFaceANonposT m s := by
    rw [hzid]
    rfl
  have hshift := uniformFaceACurrentM_nonpos_shift_identity m s q hm6.ne'
  rw [hTid] at hM
  rw [hshift] at hM
  have hTp : 0 < uniformFaceANonposT m s := by
    rw [← hTid]
    linarith
  have hD : 0 < (m+3)*(m+7)*(m+8)*uniformFaceANonposT m s := by
    positivity
  have hspos : 0 < s := by
    by_contra hs0
    have : s = 0 := le_antisymm (le_of_not_gt hs0) hs
    rw [this] at hM
    norm_num at hM
    have hpos : 0 < q*(m+3)*(m+7)*(m+8)*uniformFaceANonposT m s := by
      simpa only [mul_assoc] using mul_pos hq hD
    rw [this] at hpos
    exact (not_le_of_gt hpos) hM
  let v := q*((m+3)*(m+7)*(m+8)*uniformFaceANonposT m s)/((m+6)*s)
  have hden : 0 < (m+6)*s := by positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hbound : q*((m+3)*(m+7)*(m+8)*uniformFaceANonposT m s) ≤
      (m+6)*s := by nlinarith [hM]
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one hden]
    exact hbound
  refine ⟨s, v, hs, hv, hv1, hzid, ?_⟩
  unfold uniformFaceANonposQ
  dsimp [v]
  field_simp [hden.ne', hD.ne', hTp.ne']

theorem uniformFaceANonposScale_pos (m : ℝ) (hm : 0 ≤ m) :
    0 < uniformFaceANonposScale m := by
  unfold uniformFaceANonposScale
  positivity

/-- A box certificate for the surplus/root polynomial proves the original
return-face core throughout the nonpositive-current-slope branch. -/
theorem uniformFaceACore_nonneg_of_currentM_nonpos
    (n X T q : ℝ) (hn : 4 ≤ n) (hX : 0 ≤ X)
    (hT1 : n-1 ≤ T) (hq : 0 < q)
    (hM : uniformFaceACurrentM n T q ≤ 0)
    (hcert : ∀ m s v X : ℝ, 0 ≤ m → 0 ≤ s → 0 ≤ v → v ≤ 1 →
      0 ≤ X → 0 ≤ uniformFaceANonposScaled m s v X) :
    0 ≤ uniformFaceACore n X T q := by
  let m := n-4
  let z := T-(n-1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : m+3+z = T := by dsimp [m, z]; ring
  have hM' : uniformFaceACurrentM (m+4) (m+3+z) q ≤ 0 := by
    simpa only [hnid, hTid] using hM
  obtain ⟨s, v, hs, hv, hv1, hzid, hqid⟩ :=
    uniformFaceACurrentM_nonpos_parameterization m z q hm hz hq hM'
  have hTs : uniformFaceANonposT m s = T := by
    rw [← hTid, hzid]
    rfl
  have hscaled := hcert m s v X hm hs hv hv1 hX
  unfold uniformFaceANonposScaled at hscaled
  rw [hnid, hTs, ← hqid] at hscaled
  have hscale := uniformFaceANonposScale_pos m hm
  exact (mul_nonneg_iff_of_pos_left hscale).mp hscaled

/-- The nonpositive-current-slope branch is unconditional when the face
coordinate lies in the compact range `0 ≤ X ≤ 1`. -/
theorem uniformFaceACore_nonneg_of_currentM_nonpos_of_X_le_one
    (n X T q : ℝ) (hn : 4 ≤ n) (hX : 0 ≤ X) (hX1 : X ≤ 1)
    (hT1 : n-1 ≤ T) (hq : 0 < q)
    (hM : uniformFaceACurrentM n T q ≤ 0) :
    0 ≤ uniformFaceACore n X T q := by
  let m := n-4
  let z := T-(n-1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : m+3+z = T := by dsimp [m, z]; ring
  have hM' : uniformFaceACurrentM (m+4) (m+3+z) q ≤ 0 := by
    simpa only [hnid, hTid] using hM
  obtain ⟨s, v, hs, hv, hv1, hzid, hqid⟩ :=
    uniformFaceACurrentM_nonpos_parameterization m z q hm hz hq hM'
  have hTs : uniformFaceANonposT m s = T := by
    rw [← hTid, hzid]
    rfl
  have hscaled := uniformFaceANonposScaled_nonneg_of_X_le_one
    m s v X hm hs hv hv1 hX hX1
  unfold uniformFaceANonposScaled at hscaled
  rw [hnid, hTs, ← hqid] at hscaled
  have hscale := uniformFaceANonposScale_pos m hm
  exact (mul_nonneg_iff_of_pos_left hscale).mp hscaled

/-- Nonnegativity of the reduced cubic implies nonnegativity of the full
return-face numerator after restoring its discarded moment factor. -/
theorem uniformFaceANum_nonneg_of_core
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a)
    (hT : 0 ≤ T) (hY : 0 ≤ Y) (hq : 0 ≤ q)
    (hcore : 0 ≤ uniformFaceACore n (a*Y) T q) :
    0 ≤ uniformFaceANum n a T Y q := by
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

theorem uniformFaceACurrent_bound_of_returnSide_nonpos
    (n a T Y q : ℝ)
    (hreturn : uniformReturnSide n a T Y q ≤ 0) :
    n*(a*Y)*uniformFaceACurrentM n T q ≤
      uniformFaceACurrentK n T q := by
  rw [uniformReturnSide_eq_current] at hreturn
  linarith

theorem uniformFaceACurrent_ratio_mem_unit
    (n a T Y q : ℝ) (hn : 0 < n) (ha : 0 < a) (hY : 0 < Y)
    (hM : 0 < uniformFaceACurrentM n T q)
    (hK : 0 < uniformFaceACurrentK n T q)
    (hreturn : uniformReturnSide n a T Y q ≤ 0) :
    0 ≤ n*(a*Y)*uniformFaceACurrentM n T q /
        uniformFaceACurrentK n T q ∧
      n*(a*Y)*uniformFaceACurrentM n T q /
        uniformFaceACurrentK n T q ≤ 1 := by
  constructor
  · positivity
  · rw [div_le_one hK]
    exact uniformFaceACurrent_bound_of_returnSide_nonpos
      n a T Y q hreturn

/-- Denominator-cleared return-face core after parametrizing the current
active return interval by `0 ≤ w ≤ 1`. -/
noncomputable def uniformFaceACurrentScaled
    (n T q w : ℝ) : ℝ :=
  n^3*(uniformFaceACurrentM n T q)^3*
    uniformFaceACore n
      (w*uniformFaceACurrentK n T q /
        (n*uniformFaceACurrentM n T q)) T q

/-- A polynomial certificate for `uniformFaceACurrentScaled` on the unit
interval implies nonnegativity of the original core in the positive-slope
branch. -/
theorem uniformFaceACore_nonneg_of_current_scaled
    (n a T Y q : ℝ) (hn : 0 < n) (ha : 0 < a) (hY : 0 < Y)
    (hM : 0 < uniformFaceACurrentM n T q)
    (hK : 0 < uniformFaceACurrentK n T q)
    (hreturn : uniformReturnSide n a T Y q ≤ 0)
    (hcert : ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      0 ≤ uniformFaceACurrentScaled n T q w) :
    0 ≤ uniformFaceACore n (a*Y) T q := by
  let w := n*(a*Y)*uniformFaceACurrentM n T q /
    uniformFaceACurrentK n T q
  obtain ⟨hw, hw1⟩ := uniformFaceACurrent_ratio_mem_unit
    n a T Y q hn ha hY hM hK hreturn
  have hscaled := hcert w hw hw1
  have hXid : w*uniformFaceACurrentK n T q /
      (n*uniformFaceACurrentM n T q) = a*Y := by
    dsimp [w]
    field_simp [hn.ne', hM.ne', hK.ne']
  unfold uniformFaceACurrentScaled at hscaled
  rw [hXid] at hscaled
  have hscale : 0 < n^3*(uniformFaceACurrentM n T q)^3 := by positivity
  exact (mul_nonneg_iff_of_pos_left hscale).mp hscaled

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformFaceAEndpointScaled_bernstein (m z w : ℝ)
    (hM : uniformFaceALargeM m z ≠ 0) :
    uniformFaceAEndpointScaled m z w =
      cornerBern3 (uniformFaceAEndpointB0 m z) (uniformFaceAEndpointB1 m z)
        (uniformFaceAEndpointB2 m z) (uniformFaceAEndpointB3 m z) w := by
  unfold uniformFaceAEndpointB0 uniformFaceAEndpointB1
  unfold uniformFaceAEndpointB2 uniformFaceAEndpointB3
  simp only [EndpointReducedCompact_eq m z _ hM]
  unfold EndpointReducedCompact cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceAEndpoint_coefficients_nonneg
    (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 ≤ uniformFaceAEndpointB0 m z ∧
    0 ≤ uniformFaceAEndpointB1 m z ∧
    0 ≤ uniformFaceAEndpointB2 m z ∧
    0 ≤ uniformFaceAEndpointB3 m z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [EndpointReducedB0_eq m z (uniformFaceALargeM_pos m z hm hz).ne',
      EndpointFactoredPositive0_eq]
    have hM := uniformFaceALargeM_pos m z hm hz
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (EndpointFactoredPositive0_nonneg m z hm hz)
  · rw [EndpointReducedB1_eq m z (uniformFaceALargeM_pos m z hm hz).ne',
      EndpointFactoredPositive1_eq]
    have hM := uniformFaceALargeM_pos m z hm hz
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (EndpointFactoredPositive1_nonneg m z hm hz)
  · rw [EndpointReducedB2_eq m z (uniformFaceALargeM_pos m z hm hz).ne',
      EndpointFactoredPositive2_eq]
    have hM := uniformFaceALargeM_pos m z hm hz
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (EndpointFactoredPositive2_nonneg m z hm hz)
  · rw [EndpointReducedB3_eq m z (uniformFaceALargeM_pos m z hm hz).ne',
      EndpointFactoredPositive3_eq]
    have hM := uniformFaceALargeM_pos m z hm hz
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (EndpointFactoredPositive3_nonneg m z hm hz)

/-- On `T ≥ n-1`, the final return-face endpoint is nonnegative whenever
the return-side KKT condition is active. -/
theorem uniformFaceAQB3_nonneg_of_T_ge_of_returnSide_nonpos
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (hT : n-1 ≤ T)
    (hY : 0 < Y) (hreturn : uniformReturnSide n a T Y 1 ≤ 0) :
    0 ≤ uniformFaceAQB3 n (a*Y) T := by
  let m := n-4
  let z := T-(n-1)
  let X := a*Y
  let M := uniformFaceALargeM m z
  let K := uniformFaceALargeK m z
  let w := n*X*M/K
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hX : 0 < X := by dsimp [X]; positivity
  have hM : 0 < M := by
    dsimp [M]
    exact uniformFaceALargeM_pos m z hm hz
  have hK : 0 < K := by
    dsimp [K]
    exact uniformFaceALargeK_pos m z hm hz
  have hn0 : 0 < n := by linarith
  have hbound : n*X*M ≤ K := by
    have hid : uniformReturnSide n a T Y 1 = n*X*M-K := by
      dsimp [m, z, X, M, K]
      unfold uniformFaceALargeM uniformFaceALargeK
      unfold uniformReturnSide uniformReturnM uniformReturnK
      ring
    rw [hid] at hreturn
    linarith
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : w ≤ 1 := by
    dsimp [w]
    rw [div_le_one hK]
    exact hbound
  have hcoeff := uniformFaceAEndpoint_coefficients_nonneg m z hm hz
  obtain ⟨h0, h1, h2, h3⟩ := hcoeff
  have hscaled : 0 ≤ uniformFaceAEndpointScaled m z w := by
    rw [uniformFaceAEndpointScaled_bernstein m z w hM.ne']
    exact cornerBern3_nonneg _ _ _ _ _ h0 h1 h2 h3 hw hw1
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : m+3+z = T := by dsimp [m, z]; ring
  have hXid : w*K/((m+4)*M) = X := by
    dsimp [w]
    field_simp [hK.ne', hM.ne', hn0.ne']
    exact hnid.symm
  unfold uniformFaceAEndpointScaled at hscaled
  rw [hXid, hnid, hTid] at hscaled
  have hscale : 0 < n^3*M^3 := by positivity
  exact (mul_nonneg_iff_of_pos_left hscale).mp hscaled

/-- Slope of the affine interpolation from the current terminal mixture
parameter `q` to its Bernstein endpoint `q = 1`. -/
noncomputable def uniformReturnEndpointSlope (n a T Y : ℝ) : ℝ :=
  -T^2*n^2-2*T^2*n-T*n^4-4*T*n^3-9*T*n^2-2*T*n+16*T
    +Y*a*n^4+6*Y*a*n^3+5*Y*a*n^2-12*Y*a*n
    +2*n^4+10*n^3-6*n^2-26*n+20

theorem uniformReturnSide_one_sub (n a T Y q : ℝ) :
    uniformReturnSide n a T Y 1-uniformReturnSide n a T Y q =
      T*(1-q)*uniformReturnEndpointSlope n a T Y := by
  unfold uniformReturnSide uniformReturnEndpointSlope
  unfold uniformReturnM uniformReturnK
  ring

/-- A nonpositive endpoint slope transfers the active return-side condition
from the current mixture weight to `q = 1`. -/
theorem uniformReturnSide_one_nonpos_of_slope_nonpos
    (n a T Y q : ℝ) (hT : 0 ≤ T) (hq1 : q ≤ 1)
    (hreturn : uniformReturnSide n a T Y q ≤ 0)
    (hslope : uniformReturnEndpointSlope n a T Y ≤ 0) :
    uniformReturnSide n a T Y 1 ≤ 0 := by
  have hfac : 0 ≤ T*(1-q) := by positivity
  have hdiff :
      uniformReturnSide n a T Y 1-uniformReturnSide n a T Y q ≤ 0 := by
    rw [uniformReturnSide_one_sub]
    exact mul_nonpos_of_nonneg_of_nonpos hfac hslope
  linarith

/-- The return-face numerator is reduced to its `q = 1` Bernstein endpoint;
the other three coefficients are nonnegative uniformly. -/
theorem uniformFaceANum_nonneg_of_q_one
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a)
    (hT : 0 ≤ T) (hY : 0 ≤ Y) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (h3 : 0 ≤ uniformFaceAQB3 n (a*Y) T) :
    0 ≤ uniformFaceANum n a T Y q := by
  apply uniformFaceANum_nonneg_of_q_bernstein n a T Y q hn ha hT hY hq hq1
  · exact uniformFaceAQB1_nonneg n (a*Y) T hn (by positivity) hT
  · exact uniformFaceAQB2_nonneg n (a*Y) T hn (by positivity) hT
  · exact h3


end SSP.K3AllStages
