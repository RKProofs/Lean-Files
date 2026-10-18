import SSPLean.K3AllStagesTerminalFaceCompact
set_option autoImplicit false
namespace SSP.K3AllStages
/-! ### Normalized coordinates for the large terminal-scale range

For `T = t + 1` and `x = a*Y`, both endpoint gradients become quadratic
in `x`.  More importantly, their difference is independent of `a` and is
linear in `x`.  These identities isolate the polynomial inequality needed
by the remaining large-scale middle-coefficient certificate. -/

noncomputable def uniformLargeGrad0Poly
    (m a t x : ℝ) : ℝ :=
  x^2*(m^3 + 16*m^2 + 83*m + 140)
    + a*x*(-m^3*t + 3*m^3 - 16*m^2*t + 42*m^2
      - 84*m*t + 174*m - 144*t + 216)
    - a*(2*m^3*t + 30*m^2*t + 144*m*t + 18*m + 216*t + 54)

noncomputable def uniformLargeGrad1Poly
    (m a t x : ℝ) : ℝ :=
  x^2*(m^3 + 16*m^2 + 83*m + 140)
    + a*x*(2*m^3*t + 6*m^3 + 26*m^2*t + 84*m^2
      + 99*m*t + 357*m + 108*t + 468)
    + a*(-m^3*t^2 - 2*m^3*t + m^3 - 14*m^2*t^2
      - 28*m^2*t + 16*m^2 - m*t^3 - 72*m*t^2 - 159*m*t
      + 38*m - 4*t^3 - 120*t^2 - 282*t - 4)

noncomputable def uniformLargeGradSlopeCoeff (m : ℝ) : ℝ :=
  3*m^3 + 42*m^2 + 183*m + 252

noncomputable def uniformLargeGradSlopeThreshold
    (m t : ℝ) : ℝ :=
  m^3*t - m^3 + 14*m^2*t - 16*m^2 + m*t^2 + 71*m*t
    - 56*m + 4*t^2 + 116*t - 50

noncomputable def uniformLargeGradSlopePoly
    (m t x : ℝ) : ℝ :=
  uniformLargeGradSlopeCoeff m*x - uniformLargeGradSlopeThreshold m t

noncomputable def uniformLargeGrad0TimeCoeff
    (m x : ℝ) : ℝ :=
  (m+6)^2*(m*x+2*m+4*x+6)

theorem uniformLargeGrad0_time_shift
    (m a t x : ℝ) :
    uniformLargeGrad0Poly m a t x =
      uniformLargeGrad0Poly m a (1/2) x
        - a*uniformLargeGrad0TimeCoeff m x*(t-1/2) := by
  unfold uniformLargeGrad0Poly uniformLargeGrad0TimeCoeff
  ring

theorem uniformLargeGrad0TimeCoeff_pos
    (m x : ℝ) (hm : 0 ≤ m) (hx : 0 ≤ x) :
    0 < uniformLargeGrad0TimeCoeff m x := by
  unfold uniformLargeGrad0TimeCoeff
  positivity

theorem uniformLargeGrad0_time_budget
    (m a t x : ℝ) (_hm : 0 ≤ m) (_ha : 0 < a)
    (_hx : 0 ≤ x) (_ht : 1/2 ≤ t)
    (hgrad : 0 ≤ uniformLargeGrad0Poly m a t x) :
    a*uniformLargeGrad0TimeCoeff m x*(t-1/2) ≤
      uniformLargeGrad0Poly m a (1/2) x := by
  rw [uniformLargeGrad0_time_shift] at hgrad
  linarith

theorem uniformLargeGrad0_time_shift_eight
    (m a t x : ℝ) :
    uniformLargeGrad0Poly m a t x =
      uniformLargeGrad0Poly m a 8 x
        - a*uniformLargeGrad0TimeCoeff m x*(t-8) := by
  unfold uniformLargeGrad0Poly uniformLargeGrad0TimeCoeff
  ring

theorem uniformLargeGrad0_time_budget_eight
    (m a t x : ℝ) (_ht : 8 ≤ t)
    (hgrad : 0 ≤ uniformLargeGrad0Poly m a t x) :
    a*uniformLargeGrad0TimeCoeff m x*(t-8) ≤
      uniformLargeGrad0Poly m a 8 x := by
  rw [uniformLargeGrad0_time_shift_eight] at hgrad
  linarith

theorem uniformGradB0_large_coordinates
    (m a t Y : ℝ) :
    a*uniformGradB0 (m+4) a (t+1) Y =
      uniformLargeGrad0Poly m a t (a*Y) := by
  unfold uniformGradB0 uniformGradB uniformLargeGrad0Poly
  ring

theorem uniformGradB1_large_coordinates
    (m a t Y : ℝ) :
    a*uniformGradB1 (m+4) a (t+1) Y =
      uniformLargeGrad1Poly m a t (a*Y) := by
  unfold uniformGradB1 uniformGradB uniformLargeGrad1Poly
  ring

theorem uniformGradB_slope_large_coordinates
    (m a t Y : ℝ) :
    uniformGradB1 (m+4) a (t+1) Y
        - uniformGradB0 (m+4) a (t+1) Y =
      (t+1)*uniformLargeGradSlopePoly m t (a*Y) := by
  unfold uniformGradB0 uniformGradB1 uniformGradB
  unfold uniformLargeGradSlopePoly uniformLargeGradSlopeCoeff
  unfold uniformLargeGradSlopeThreshold
  ring

theorem uniformLargeGradSlopeCoeff_pos
    (m : ℝ) (hm : 0 ≤ m) :
    0 < uniformLargeGradSlopeCoeff m := by
  unfold uniformLargeGradSlopeCoeff
  positivity

theorem uniformLargeGradSlope_threshold_lt
    (m a t Y : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t)
    (hslope : uniformGradB0 (m+4) a (t+1) Y <
      uniformGradB1 (m+4) a (t+1) Y) :
    0 < uniformLargeGradSlopeCoeff m ∧
      uniformLargeGradSlopeThreshold m t <
        uniformLargeGradSlopeCoeff m*(a*Y) := by
  constructor
  · exact uniformLargeGradSlopeCoeff_pos m hm
  rw [← sub_pos] at hslope
  rw [uniformGradB_slope_large_coordinates] at hslope
  have ht1 : 0 < t+1 := by linarith
  have hpoly : 0 < uniformLargeGradSlopePoly m t (a*Y) := by
    rcases mul_pos_iff.mp hslope with hpos | hneg
    · exact hpos.2
    · linarith [hneg.1]
  unfold uniformLargeGradSlopePoly at hpoly
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalMidX0 (n t x : ℝ) : ℝ :=
  n*x^3*(n + 1)*(n + 2)*(2*n^3*t + 6*n^3 + 6*n^2*t + 18*n^2 + n*t^2 + 2*n*t + 2*n*x + n - 8*t - 24)/2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalMidX1 (n t x : ℝ) : ℝ :=
  -n*x^2*(n - 1)*(n + 1)*(n^3*t^2 + n^3*t*x - 4*n^3*t + 5*n^3*x - 9*n^3 + 7*n^2*t^2 + 7*n^2*t*x + 2*n^2*t + 35*n^2*x - 5*n^2 + 8*n*t^2 + 10*n*t*x + 22*n*t + 50*n*x + 26*n + 12*t + 4)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalMidX2 (n t x : ℝ) : ℝ :=
  (n - 1)*(3*n^5*t^2*x^2 + 4*n^5*t^2*x + 2*n^5*t^2 + 6*n^5*t*x^2 + 26*n^5*t*x + 16*n^5*t + 6*n^5*x^3 + 15*n^5*x^2 + 46*n^5*x + 26*n^5 + 12*n^4*t^2*x^2 - 4*n^4*t^2*x - 10*n^4*t^2 + 6*n^4*t*x^2 - 26*n^4*t*x - 44*n^4*t + 24*n^4*x^3 - 6*n^4*x^2 - 46*n^4*x - 58*n^4 + 15*n^3*t^2*x^2 - 10*n^3*t^2*x - 6*n^3*t^2 + 12*n^3*t*x^2 - 74*n^3*t*x - 36*n^3*t + 24*n^3*x^3 - 39*n^3*x^2 - 136*n^3*x - 54*n^3 + 10*n^2*t^2*x + 34*n^2*t^2 + 36*n^2*t*x^2 + 110*n^2*t*x + 164*n^2*t + 60*n^2*x^2 + 220*n^2*x + 226*n^2 - 20*n*t^2 - 36*n*t*x - 124*n*t - 84*n*x - 188*n + 24*t + 48)

noncomputable def TerminalMidPolynomial (n s t x : ℝ) : ℝ :=
  TerminalMidX0 n t x*s^0+TerminalMidX1 n t x*s^1+TerminalMidX2 n t x*s^2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalMidPolynomial_eq (n s t x : ℝ) (hs : s ≠ 0) :
    s^2*uniformFaceBCoreB1 n s (t+1) (x/s) = TerminalMidPolynomial n s t x := by
  unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
  unfold TerminalMidPolynomial TerminalMidX0 TerminalMidX1 TerminalMidX2
  field_simp [hs]
  ring

noncomputable def uniformLargeMidSample
    (m s t x : ℝ) : ℝ :=
  s^2 * uniformFaceBCoreB1 (m+4) s (t+1) (x/s)

theorem TerminalMidSample_eq (m s t x : ℝ) (hs : s ≠ 0) :
    uniformLargeMidSample m s t x = TerminalMidPolynomial (m+4) s t x := by
  exact TerminalMidPolynomial_eq (m+4) s t x hs

noncomputable def uniformLargeMidB0 (m t x : ℝ) : ℝ :=
  3*uniformLargeMidSample m 1 t x
    - 3*uniformLargeMidSample m 2 t x
    + uniformLargeMidSample m 3 t x

noncomputable def uniformLargeMidB1 (m t x : ℝ) : ℝ :=
  (19*uniformLargeMidSample m 1 t x
    - 16*uniformLargeMidSample m 2 t x
    + 5*uniformLargeMidSample m 3 t x) / 8

noncomputable def uniformLargeMidB2 (m t x : ℝ) : ℝ :=
  (11*uniformLargeMidSample m 1 t x
    - 7*uniformLargeMidSample m 2 t x
    + 2*uniformLargeMidSample m 3 t x) / 6

noncomputable def uniformLargeMidB3 (m t x : ℝ) : ℝ :=
  (11*uniformLargeMidSample m 1 t x
    - 4*uniformLargeMidSample m 2 t x
    + uniformLargeMidSample m 3 t x) / 8

noncomputable def uniformLargeMidB4 (m t x : ℝ) : ℝ :=
  uniformLargeMidSample m 1 t x

noncomputable def uniformLargeMidA1 (m t x : ℝ) : ℝ :=
  (7*uniformLargeMidSample m 1 t x
    - 4*uniformLargeMidSample m 2 t x
    + uniformLargeMidSample m 3 t x) / 4

noncomputable def sampledBern2C0 (f1 f2 f3 : ℝ) : ℝ :=
  3*f1-3*f2+f3

noncomputable def sampledBern2C1 (f1 f2 f3 : ℝ) : ℝ :=
  (7*f1-4*f2+f3)/4

noncomputable def sampledBern2C2 (f1 _f2 _f3 : ℝ) : ℝ := f1

theorem cornerBern2_nonneg_of_det
    (c0 c1 c2 z : ℝ) (hc0 : 0 ≤ c0) (hc2 : 0 ≤ c2)
    (hdet : 0 ≤ c0*c2-c1^2) :
    0 ≤ cornerBern2 c0 c1 c2 z := by
  by_cases hz : c0 = 0
  · have hc1 : c1 = 0 := by
      rw [hz] at hdet
      nlinarith [sq_nonneg c1]
    subst c0
    subst c1
    simpa [cornerBern2] using mul_nonneg hc2 (sq_nonneg z)
  · have hc0pos : 0 < c0 := lt_of_le_of_ne hc0 (Ne.symm hz)
    have hid : 4*c0*cornerBern2 c0 c1 c2 z =
        (2*c0*(1-z)+2*c1*z)^2 + 4*z^2*(c0*c2-c1^2) := by
      unfold cornerBern2
      ring
    have hscaled : 0 ≤ 4*c0*cornerBern2 c0 c1 c2 z := by
      rw [hid]
      positivity
    exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*c0)).mp hscaled

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformLargeMid_bernstein_a
    (m a t x : ℝ) (ha : a ≠ 0) :
    a^2*uniformFaceBCoreB1 (m+4) a (t+1) (x/a) =
      cornerBern4 (uniformLargeMidB0 m t x) (uniformLargeMidB1 m t x)
        (uniformLargeMidB2 m t x) (uniformLargeMidB3 m t x)
        (uniformLargeMidB4 m t x) a := by
  unfold uniformLargeMidB0 uniformLargeMidB1 uniformLargeMidB2
  unfold uniformLargeMidB3 uniformLargeMidB4 uniformLargeMidSample
  unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
  unfold cornerBern4
  field_simp [ha]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformLargeMidB0_nonneg
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidB0 m t x := by
  unfold uniformLargeMidB0
  simp only [TerminalMidSample_eq _ 1 _ _ (by norm_num),
    TerminalMidSample_eq _ 2 _ _ (by norm_num),
    TerminalMidSample_eq _ 3 _ _ (by norm_num)]
  unfold TerminalMidPolynomial TerminalMidX0 TerminalMidX1 TerminalMidX2
  ring_nf
  positivity

noncomputable def uniformLargeMidB1Quotient
    (m t x : ℝ) : ℝ :=
  (m+5)*(m+6)*
    (9*m^5*t + 21*m^5 + 222*m^4*t + 510*m^4
      + 6*m^3*t^2 + 2164*m^3*t + 12*m^3*x + 4910*m^3
      + 84*m^2*t^2 + 10358*m^2*t + 168*m^2*x + 23258*m^2
      + 370*m*t^2 + 24155*m*t + 732*m*x + 53629*m
      + 520*t^2 + 21884*t + 1008*x + 47932) /
    (36*(m+3)^2*(m+7)^2)

noncomputable def uniformLargeMidB1Remainder
    (m t x : ℝ) : ℝ :=
  uniformLargeMidB1 m t x
    - x^2*uniformLargeMidB1Quotient m t x*
      uniformLargeGradSlopePoly m t x

theorem uniformLargeMidB1Quotient_nonneg
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidB1Quotient m t x := by
  unfold uniformLargeMidB1Quotient
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeMidB1Remainder_nonneg
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (_hx : 0 ≤ x) :
    0 ≤ uniformLargeMidB1Remainder m t x := by
  let q1 := m^7*t*(48*m^2-12*m*t+15*t^2)
  let q2 := m^6*t*(1896*m^2-257*m*t+516*t^2)
  let q3 := m^5*t*(33097*m^2-818*m*t+7580*t^2)
  have hq1inner : 0 ≤ 48*m^2-12*m*t+15*t^2 := by
    nlinarith [sq_nonneg (96*m-12*t)]
  have hq2inner : 0 ≤ 1896*m^2-257*m*t+516*t^2 := by
    nlinarith [sq_nonneg (3792*m-257*t)]
  have hq3inner : 0 ≤ 33097*m^2-818*m*t+7580*t^2 := by
    nlinarith [sq_nonneg (66194*m-818*t)]
  have hq1 : 0 ≤ q1 := by dsimp [q1]; positivity
  have hq2 : 0 ≤ q2 := by dsimp [q2]; positivity
  have hq3 : 0 ≤ q3 := by dsimp [q3]; positivity
  let block := x^2*(m+5)*(q1+q2+q3)/(36*(m+3)^2*(m+7)^2)
  have hblock : 0 ≤ block := by dsimp [block]; positivity
  let remainder := uniformLargeMidB1Remainder m t x - block
  have hrest : 0 ≤ remainder := by
    dsimp [remainder, block, q1, q2, q3]
    unfold uniformLargeMidB1Remainder uniformLargeMidB1Quotient
    unfold uniformLargeMidB1
    unfold uniformLargeGradSlopePoly uniformLargeGradSlopeCoeff
    unfold uniformLargeGradSlopeThreshold
    simp only [TerminalMidSample_eq _ 1 _ _ (by norm_num),
      TerminalMidSample_eq _ 2 _ _ (by norm_num),
      TerminalMidSample_eq _ 3 _ _ (by norm_num)]
    unfold TerminalMidPolynomial TerminalMidX0 TerminalMidX1 TerminalMidX2
    have hm3 : m+3 ≠ 0 := by positivity
    have hm7 : m+7 ≠ 0 := by positivity
    field_simp [hm3, hm7]
    ring_nf
    positivity
  dsimp [remainder] at hrest
  linarith

theorem uniformLargeMidB1_nonneg_of_threshold
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (hx : 0 ≤ x)
    (hthreshold : uniformLargeGradSlopeThreshold m t ≤
      uniformLargeGradSlopeCoeff m*x) :
    0 ≤ uniformLargeMidB1 m t x := by
  have hslope : 0 ≤ uniformLargeGradSlopePoly m t x := by
    unfold uniformLargeGradSlopePoly
    linarith
  have hQ := uniformLargeMidB1Quotient_nonneg m t x hm ht hx
  have hR := uniformLargeMidB1Remainder_nonneg m t x hm ht hx
  have hid : uniformLargeMidB1 m t x =
      x^2*uniformLargeMidB1Quotient m t x*
          uniformLargeGradSlopePoly m t x
        + uniformLargeMidB1Remainder m t x := by
    unfold uniformLargeMidB1Remainder
    ring
  rw [hid]
  positivity

end SSP.K3AllStages
