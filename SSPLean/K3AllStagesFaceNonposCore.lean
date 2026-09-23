import SSPLean.K3AllStagesFaceBasic

set_option autoImplicit false

namespace SSP.K3AllStages

open SSP.K3S4Renewal
open SSP.K3S4KKT

/-! In the nonpositive-current-slope branch, retain the positive common
denominator which appears after the surplus substitution.  This makes the
projective `X`-Bernstein coefficients coefficientwise nonnegative. -/

noncomputable def uniformFaceACoreXC0 (n T q : ℝ) : ℝ :=
  uniformFaceACore n 0 T q

noncomputable def uniformFaceACoreXC1 (n T q : ℝ) : ℝ :=
  (-11*uniformFaceACore n 0 T q+18*uniformFaceACore n 1 T q
    -9*uniformFaceACore n 2 T q+2*uniformFaceACore n 3 T q)/6

noncomputable def uniformFaceACoreXC2 (n T q : ℝ) : ℝ :=
  (2*uniformFaceACore n 0 T q-5*uniformFaceACore n 1 T q
    +4*uniformFaceACore n 2 T q-uniformFaceACore n 3 T q)/2

noncomputable def uniformFaceACoreXC3 (n T q : ℝ) : ℝ :=
  (-uniformFaceACore n 0 T q+3*uniformFaceACore n 1 T q
    -3*uniformFaceACore n 2 T q+uniformFaceACore n 3 T q)/6

noncomputable def uniformFaceACoreHom (n T q x : ℝ) : ℝ :=
  uniformFaceACoreXC0 n T q*(1-x)^3
    +uniformFaceACoreXC1 n T q*x*(1-x)^2
    +uniformFaceACoreXC2 n T q*x^2*(1-x)
    +uniformFaceACoreXC3 n T q*x^3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformFaceACoreHom_projective (n X T q : ℝ)
    (hX1 : 1+X ≠ 0) :
    uniformFaceACore n X T q =
      (1+X)^3*uniformFaceACoreHom n T q (X/(1+X)) := by
  unfold uniformFaceACoreHom uniformFaceACoreXC0 uniformFaceACoreXC1
  unfold uniformFaceACoreXC2 uniformFaceACoreXC3 uniformFaceACore
  field_simp [hX1]
  ring_nf

noncomputable def uniformFaceANonposP (m : ℝ) : ℝ :=
  2*m^3+35*m^2+191*m+312

noncomputable def uniformFaceANonposZ (m s : ℝ) : ℝ :=
  uniformFaceANonposP m/(m+6)+s

noncomputable def uniformFaceANonposT (m s : ℝ) : ℝ :=
  m+3+uniformFaceANonposZ m s

noncomputable def uniformFaceANonposQ (m s v : ℝ) : ℝ :=
  v*(m+6)*s /
    ((m+3)*(m+7)*(m+8)*uniformFaceANonposT m s)

noncomputable def uniformFaceANonposScale (m : ℝ) : ℝ :=
  (m+3)^2*(m+6)*(m+7)^3*(m+8)^3

noncomputable def uniformFaceANonposScaled (m s v X : ℝ) : ℝ :=
  uniformFaceANonposScale m*
    uniformFaceACore (m+4) X (uniformFaceANonposT m s)
      (uniformFaceANonposQ m s v)

noncomputable def uniformFaceANonposXB0 (m s v : ℝ) : ℝ :=
  uniformFaceANonposScaled m s v 0

noncomputable def uniformFaceANonposXB1 (m s v : ℝ) : ℝ :=
  -(5/6)*uniformFaceANonposScaled m s v 0
    +(1/3)*uniformFaceANonposScaled m s v 1
    +3*uniformFaceANonposScaled m s v (1/3)
    -(3/2)*uniformFaceANonposScaled m s v (2/3)

noncomputable def uniformFaceANonposXB2 (m s v : ℝ) : ℝ :=
  (1/3)*uniformFaceANonposScaled m s v 0
    -(5/6)*uniformFaceANonposScaled m s v 1
    -(3/2)*uniformFaceANonposScaled m s v (1/3)
    +3*uniformFaceANonposScaled m s v (2/3)

noncomputable def uniformFaceANonposXB3 (m s v : ℝ) : ℝ :=
  uniformFaceANonposScaled m s v 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem uniformFaceANonposScaled_bernstein_X (m s v X : ℝ) :
    uniformFaceANonposScaled m s v X =
      cornerBern3 (uniformFaceANonposXB0 m s v)
        (uniformFaceANonposXB1 m s v) (uniformFaceANonposXB2 m s v)
        (uniformFaceANonposXB3 m s v) X := by
  unfold uniformFaceANonposXB0 uniformFaceANonposXB1
  unfold uniformFaceANonposXB2 uniformFaceANonposXB3
  unfold uniformFaceANonposScaled uniformFaceACore cornerBern3
  ring

noncomputable def uniformCubicSampleB0 (f : ℝ → ℝ) : ℝ := f 0

noncomputable def uniformCubicSampleB1 (f : ℝ → ℝ) : ℝ :=
  -(5/6)*f 0+(1/3)*f 1+3*f (1/3)-(3/2)*f (2/3)

noncomputable def uniformCubicSampleB2 (f : ℝ → ℝ) : ℝ :=
  (1/3)*f 0-(5/6)*f 1-(3/2)*f (1/3)+3*f (2/3)

noncomputable def uniformCubicSampleB3 (f : ℝ → ℝ) : ℝ := f 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformFaceANonposXB0_bernstein_v (m s v : ℝ) :
    uniformFaceANonposXB0 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposXB0 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposXB0 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposXB0 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposXB0 m s u)) v := by
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposXB0 uniformFaceANonposScaled
  unfold uniformFaceANonposQ uniformFaceACore cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformFaceANonposXB1_bernstein_v (m s v : ℝ) :
    uniformFaceANonposXB1 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposXB1 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposXB1 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposXB1 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposXB1 m s u)) v := by
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposXB1 uniformFaceANonposScaled
  unfold uniformFaceANonposQ uniformFaceACore cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformFaceANonposXB2_bernstein_v (m s v : ℝ) :
    uniformFaceANonposXB2 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposXB2 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposXB2 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposXB2 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposXB2 m s u)) v := by
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposXB2 uniformFaceANonposScaled
  unfold uniformFaceANonposQ uniformFaceACore cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformFaceANonposXB3_bernstein_v (m s v : ℝ) :
    uniformFaceANonposXB3 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposXB3 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposXB3 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposXB3 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposXB3 m s u)) v := by
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposXB3 uniformFaceANonposScaled
  unfold uniformFaceANonposQ uniformFaceACore cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposXB0_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposXB0 m s v := by
  rw [uniformFaceANonposXB0_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    simp only [uniformCubicSampleB0, uniformCubicSampleB1,
      uniformCubicSampleB2, uniformCubicSampleB3]
    unfold uniformFaceANonposXB0 uniformFaceANonposScaled
    unfold uniformFaceANonposScale uniformFaceANonposQ
    unfold uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP
    unfold uniformFaceACore
    field_simp
    ring_nf
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposXB1_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposXB1 m s v := by
  rw [uniformFaceANonposXB1_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    simp only [uniformCubicSampleB0, uniformCubicSampleB1,
      uniformCubicSampleB2, uniformCubicSampleB3]
    unfold uniformFaceANonposXB1 uniformFaceANonposScaled
    unfold uniformFaceANonposScale uniformFaceANonposQ
    unfold uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP
    unfold uniformFaceACore
    field_simp
    ring_nf
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposXB2_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposXB2 m s v := by
  rw [uniformFaceANonposXB2_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    simp only [uniformCubicSampleB0, uniformCubicSampleB1,
      uniformCubicSampleB2, uniformCubicSampleB3]
    unfold uniformFaceANonposXB2 uniformFaceANonposScaled
    unfold uniformFaceANonposScale uniformFaceANonposQ
    unfold uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP
    unfold uniformFaceACore
    field_simp
    ring_nf
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposXB3_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposXB3 m s v := by
  rw [uniformFaceANonposXB3_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    simp only [uniformCubicSampleB0, uniformCubicSampleB1,
      uniformCubicSampleB2, uniformCubicSampleB3]
    unfold uniformFaceANonposXB3 uniformFaceANonposScaled
    unfold uniformFaceANonposScale uniformFaceANonposQ
    unfold uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP
    unfold uniformFaceACore
    field_simp
    ring_nf
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem uniformFaceANonposScaled_nonneg_of_X_le_one
    (m s v X : ℝ)
    (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hX : 0 ≤ X) (hX1 : X ≤ 1) :
    0 ≤ uniformFaceANonposScaled m s v X := by
  rw [uniformFaceANonposScaled_bernstein_X]
  exact cornerBern3_nonneg _ _ _ _ _
    (uniformFaceANonposXB0_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposXB1_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposXB2_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposXB3_nonneg m s v hm hs hv hv1)
    hX hX1

/-! On the far unbounded tail, use the ordinary power coefficients.  The
quadratic and cubic coefficients are nonnegative, so positivity of the value
and derivative at one sufficiently large point propagates to the right. -/

noncomputable def uniformFaceANonposXC0 (m s v : ℝ) : ℝ :=
  uniformFaceANonposScale m *
    uniformFaceACoreXC0 (m+4) (uniformFaceANonposT m s)
      (uniformFaceANonposQ m s v)

noncomputable def uniformFaceANonposXC1 (m s v : ℝ) : ℝ :=
  uniformFaceANonposScale m *
    uniformFaceACoreXC1 (m+4) (uniformFaceANonposT m s)
      (uniformFaceANonposQ m s v)

noncomputable def uniformFaceANonposXC2 (m s v : ℝ) : ℝ :=
  uniformFaceANonposScale m *
    uniformFaceACoreXC2 (m+4) (uniformFaceANonposT m s)
      (uniformFaceANonposQ m s v)

noncomputable def uniformFaceANonposXC3 (m s v : ℝ) : ℝ :=
  uniformFaceANonposScale m *
    uniformFaceACoreXC3 (m+4) (uniformFaceANonposT m s)
      (uniformFaceANonposQ m s v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem uniformFaceANonposScaled_power (m s v X : ℝ) :
    uniformFaceANonposScaled m s v X =
      uniformFaceANonposXC0 m s v + uniformFaceANonposXC1 m s v*X
        +uniformFaceANonposXC2 m s v*X^2
        +uniformFaceANonposXC3 m s v*X^3 := by
  unfold uniformFaceANonposXC0 uniformFaceANonposXC1
  unfold uniformFaceANonposXC2 uniformFaceANonposXC3
  unfold uniformFaceACoreXC0 uniformFaceACoreXC1
  unfold uniformFaceACoreXC2 uniformFaceACoreXC3
  unfold uniformFaceANonposScaled uniformFaceACore
  ring

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
  unfold uniformFaceANonposQ uniformFaceACore cornerBern3
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
    unfold uniformFaceANonposXC2 uniformFaceACoreXC2
    unfold uniformFaceANonposScale uniformFaceANonposQ
    unfold uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP
    unfold uniformFaceACore
    field_simp
    ring_nf
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceANonposXC3_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ uniformFaceANonposXC3 m s v := by
  unfold uniformFaceANonposXC3 uniformFaceACoreXC3
  unfold uniformFaceANonposScale uniformFaceANonposQ
  unfold uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP
  unfold uniformFaceACore
  field_simp
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

/-- Denominator-cleared return-face endpoint after parametrizing the interval
cut out by the return-side condition with `0 ≤ w ≤ 1`. -/
noncomputable def uniformFaceAEndpointScaled (m z w : ℝ) : ℝ :=
  (m+4)^3*(uniformFaceALargeM m z)^3*
    uniformFaceAQB3 (m+4)
      (w*uniformFaceALargeK m z/((m+4)*uniformFaceALargeM m z))
      (m+3+z)

noncomputable def uniformFaceAEndpointB0 (m z : ℝ) : ℝ :=
  uniformFaceAEndpointScaled m z 0

noncomputable def uniformFaceAEndpointB1 (m z : ℝ) : ℝ :=
  -(5/6)*uniformFaceAEndpointScaled m z 0
    +(1/3)*uniformFaceAEndpointScaled m z 1
    +3*uniformFaceAEndpointScaled m z (1/3)
    -(3/2)*uniformFaceAEndpointScaled m z (2/3)

noncomputable def uniformFaceAEndpointB2 (m z : ℝ) : ℝ :=
  (1/3)*uniformFaceAEndpointScaled m z 0
    -(5/6)*uniformFaceAEndpointScaled m z 1
    -(3/2)*uniformFaceAEndpointScaled m z (1/3)
    +3*uniformFaceAEndpointScaled m z (2/3)

noncomputable def uniformFaceAEndpointB3 (m z : ℝ) : ℝ :=
  uniformFaceAEndpointScaled m z 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformFaceAEndpointScaled_bernstein (m z w : ℝ)
    (hM : uniformFaceALargeM m z ≠ 0) :
    uniformFaceAEndpointScaled m z w =
      cornerBern3 (uniformFaceAEndpointB0 m z) (uniformFaceAEndpointB1 m z)
        (uniformFaceAEndpointB2 m z) (uniformFaceAEndpointB3 m z) w := by
  unfold uniformFaceAEndpointB0 uniformFaceAEndpointB1
  unfold uniformFaceAEndpointB2 uniformFaceAEndpointB3
  unfold uniformFaceAEndpointScaled uniformFaceAQB3 uniformFaceACore cornerBern3
  field_simp [hM]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceAEndpoint_coefficients_nonneg
    (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 ≤ uniformFaceAEndpointB0 m z ∧
    0 ≤ uniformFaceAEndpointB1 m z ∧
    0 ≤ uniformFaceAEndpointB2 m z ∧
    0 ≤ uniformFaceAEndpointB3 m z := by
  have hM := uniformFaceALargeM_pos m z hm hz
  unfold uniformFaceAEndpointB0 uniformFaceAEndpointB1
  unfold uniformFaceAEndpointB2 uniformFaceAEndpointB3
  unfold uniformFaceAEndpointScaled uniformFaceAQB3 uniformFaceACore
  constructor
  · field_simp [hM.ne']
    unfold uniformFaceALargeM uniformFaceALargeK uniformReturnM uniformReturnK
    ring_nf
    positivity
  constructor
  · field_simp [hM.ne']
    unfold uniformFaceALargeM uniformFaceALargeK uniformReturnM uniformReturnK
    ring_nf
    positivity
  constructor <;> field_simp [hM.ne']
  · unfold uniformFaceALargeM uniformFaceALargeK uniformReturnM uniformReturnK
    ring_nf
    positivity
  · unfold uniformFaceALargeM uniformFaceALargeK uniformReturnM uniformReturnK
    ring_nf
    positivity

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
