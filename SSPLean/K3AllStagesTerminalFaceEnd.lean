import SSPLean.K3AllStagesTerminalFaceMidRanges
set_option autoImplicit false
namespace SSP.K3AllStages
noncomputable def uniformLargeEndSample
    (m s t x : ℝ) : ℝ :=
  s^2 * uniformFaceBCoreB2 (m+4) s (t+1) (x/s)

noncomputable def uniformLargeEndB0 (m t x : ℝ) : ℝ :=
  3*uniformLargeEndSample m 1 t x
    - 3*uniformLargeEndSample m 2 t x
    + uniformLargeEndSample m 3 t x

noncomputable def uniformLargeEndB1 (m t x : ℝ) : ℝ :=
  (7*uniformLargeEndSample m 1 t x
    - 4*uniformLargeEndSample m 2 t x
    + uniformLargeEndSample m 3 t x) / 4

noncomputable def uniformLargeEndB2 (m t x : ℝ) : ℝ :=
  uniformLargeEndSample m 1 t x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformLargeEnd_bernstein_a
    (m a t x : ℝ) (ha : a ≠ 0) :
    a^2*uniformFaceBCoreB2 (m+4) a (t+1) (x/a) =
      cornerBern2 (uniformLargeEndB0 m t x)
        (uniformLargeEndB1 m t x) (uniformLargeEndB2 m t x) a := by
  unfold uniformLargeEndB0 uniformLargeEndB1 uniformLargeEndB2
  unfold uniformLargeEndSample
  unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
  unfold uniformFaceBCoreQ2 cornerBern2
  field_simp [ha]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeEndB0_mono
    (m t x y : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    uniformLargeEndB0 m t x ≤ uniformLargeEndB0 m t y := by
  let d := y-x
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hy : y = x+d := by dsimp [d]; ring
  suffices 0 ≤ uniformLargeEndB0 m t y - uniformLargeEndB0 m t x by
    linarith
  rw [hy]
  unfold uniformLargeEndB0 uniformLargeEndSample
  unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
  unfold uniformFaceBCoreQ2
  ring_nf
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeEndB1_mono
    (m t x y : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    uniformLargeEndB1 m t x ≤ uniformLargeEndB1 m t y := by
  let d := y-x
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hy : y = x+d := by dsimp [d]; ring
  suffices 0 ≤ uniformLargeEndB1 m t y - uniformLargeEndB1 m t x by
    linarith
  rw [hy]
  unfold uniformLargeEndB1 uniformLargeEndSample
  unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
  unfold uniformFaceBCoreQ2
  ring_nf
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeEndB2_mono
    (m t x y : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    uniformLargeEndB2 m t x ≤ uniformLargeEndB2 m t y := by
  let A := m^2 + 9*m + 20
  let B := -2*m^3 - 14*m^2 - 12*m + 40
  let C := 4*m^4 + 56*m^3 + 295*m^2 + 711*m + 668
  have hA : 0 < A := by dsimp [A]; positivity
  have hdisc : 0 ≤ 4*A*C-B^2 := by
    have hid : 4*A*C-B^2 =
        4*(m+3)*(m+5)*
          (3*m^4 + 54*m^3 + 341*m^2 + 904*m + 864) := by
      dsimp [A, B, C]
      ring
    rw [hid]
    positivity
  have hquad : 0 ≤ A*t^2+B*t+C := by
    have hid : 4*A*(A*t^2+B*t+C) =
        (2*A*t+B)^2+(4*A*C-B^2) := by ring
    have hscaled : 0 ≤ 4*A*(A*t^2+B*t+C) := by
      rw [hid]
      positivity
    exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*A)).mp hscaled
  let S := A*t^2+B*t+C
  let d := y-x
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hy : y = x+d := by dsimp [d]; ring
  rw [hy]
  let block := (m+4)*(m+6)*S*((x+d)^3-x^3)
  have hblock : 0 ≤ block := by
    dsimp [block, S]
    have hcubicid : (x+d)^3-x^3 = d*(3*x^2+3*x*d+d^2) := by ring
    have hcubic : 0 ≤ (x+d)^3-x^3 := by
      rw [hcubicid]
      positivity
    positivity
  let remainder := uniformLargeEndB2 m t (x+d)
    - uniformLargeEndB2 m t x - block
  have hrem : 0 ≤ remainder := by
    dsimp [remainder, block, S, A, B, C]
    unfold uniformLargeEndB2 uniformLargeEndSample
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring_nf
    positivity
  dsimp [remainder] at hrem
  linarith

theorem uniformLargeEnd_mono
    (m a t x y : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (ha1 : a ≤ 1)
    (ht : 0 ≤ t) (hx : 0 ≤ x) (hxy : x ≤ y) :
    a^2*uniformFaceBCoreB2 (m+4) a (t+1) (x/a) ≤
      a^2*uniformFaceBCoreB2 (m+4) a (t+1) (y/a) := by
  rw [uniformLargeEnd_bernstein_a m a t x ha.ne']
  rw [uniformLargeEnd_bernstein_a m a t y ha.ne']
  have h0 := uniformLargeEndB0_mono m t x y hm ht hx hxy
  have h1 := uniformLargeEndB1_mono m t x y hm ht hx hxy
  have h2 := uniformLargeEndB2_mono m t x y hm ht hx hxy
  unfold cornerBern2
  have ha0 := ha.le
  have h1a : 0 ≤ 1-a := sub_nonneg.mpr ha1
  nlinarith [mul_le_mul_of_nonneg_left h0 (sq_nonneg (1-a)),
    mul_le_mul_of_nonneg_left h1
      (mul_nonneg (by positivity : 0 ≤ 2*a) h1a),
    mul_le_mul_of_nonneg_left h2 (sq_nonneg a)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeEnd_at_zero_nonneg_of_grad
    (m a t : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (ha1 : a ≤ 1)
    (ht : 0 ≤ t) (hgrad : 0 ≤ uniformLargeGrad1Poly m a t 0) :
    0 ≤ a^2*uniformFaceBCoreB2 (m+4) a (t+1) 0 := by
  let Cgrad :=
    -m^3*t^2 - 2*m^3*t + m^3
      - 14*m^2*t^2 - 28*m^2*t + 16*m^2
      - m*t^3 - 72*m*t^2 - 159*m*t + 38*m
      - 4*t^3 - 120*t^2 - 282*t - 4
  have hgradid : uniformLargeGrad1Poly m a t 0 = a*Cgrad := by
    dsimp [Cgrad]
    unfold uniformLargeGrad1Poly
    ring
  rw [hgradid] at hgrad
  have hCgrad : 0 ≤ Cgrad :=
    (mul_nonneg_iff_of_pos_left ha).mp hgrad
  have ht_half : t ≤ 1/2 := by
    by_contra hnot
    have hu : 0 ≤ t-1/2 := by linarith
    let u := t-1/2
    have htid : t = u+1/2 := by dsimp [u]; ring
    have hneg : Cgrad < 0 := by
      let R := 8*m^3*u^2 + 24*m^3*u + 2*m^3
        + 112*m^2*u^2 + 336*m^2*u + 12*m^2
        + 8*m*u^3 + 588*m*u^2 + 1854*m*u + 477*m
        + 32*u^3 + 1008*u^2 + 3240*u + 1404
      have hR : 0 < R := by dsimp [R]; positivity
      have hid : Cgrad = -R/8 := by
        dsimp [Cgrad, R]
        rw [htid]
        ring
      rw [hid]
      linarith
    linarith
  have htprod : 0 ≤ t*(1/2-t) := by positivity
  have htsq : t^2 ≤ t/2 := by nlinarith
  let D := m^2*t^2 - 4*m^2*t - 11*m^2
    + 15*m*t^2 - 6*m*t - 57*m + 44*t^2 + 34*t - 64
  have hcoef2 : t^2-4*t-11 ≤ 0 := by nlinarith
  have hcoef1 : 15*t^2-6*t-57 ≤ 0 := by nlinarith
  have hcoef0 : 44*t^2+34*t-64 ≤ 0 := by nlinarith
  have hterm2 : m^2*(t^2-4*t-11) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg m) hcoef2
  have hterm1 : m*(15*t^2-6*t-57) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hm hcoef1
  have hD : D ≤ 0 := by
    dsimp [D]
    nlinarith
  have h0 : 0 ≤ uniformLargeEndB0 m t 0 := by
    unfold uniformLargeEndB0 uniformLargeEndSample
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring_nf
    positivity
  have h1 : 0 ≤ uniformLargeEndB1 m t 0 := by
    unfold uniformLargeEndB1 uniformLargeEndSample
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring_nf
    positivity
  have h2id : uniformLargeEndB2 m t 0 =
      -(m+3)^2*(m+6)
        *(m*t^2+4*m*t+5*m+4*t^2+14*t+16)*D := by
    dsimp [D]
    unfold uniformLargeEndB2 uniformLargeEndSample
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    norm_num
    ring
  have h2 : 0 ≤ uniformLargeEndB2 m t 0 := by
    rw [h2id]
    have hminusD : 0 ≤ -D := by linarith
    have hid : -(m+3)^2*(m+6)
        *(m*t^2+4*m*t+5*m+4*t^2+14*t+16)*D =
        (m+3)^2*(m+6)
          *(m*t^2+4*m*t+5*m+4*t^2+14*t+16)*(-D) := by ring
    rw [hid]
    positivity
  have hid := uniformLargeEnd_bernstein_a m a t 0 ha.ne'
  norm_num at hid
  rw [hid]
  unfold cornerBern2
  have ha0 := ha.le
  have h1a : 0 ≤ 1-a := sub_nonneg.mpr ha1
  positivity

theorem uniformFaceBCoreB2_nonneg_of_large_grad1
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 1 ≤ T) (hY : 0 < Y)
    (hgrad : 0 < uniformGradB1 n a T Y) :
    0 ≤ uniformFaceBCoreB2 n a T Y := by
  let m := n-4
  let t := T-1
  let x := a*Y
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hx : 0 < x := by dsimp [x]; positivity
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : t+1 = T := by dsimp [t]; ring
  rw [← hnid, ← hTid] at hgrad ⊢
  have hpolyx : 0 < uniformLargeGrad1Poly m a t x := by
    rw [← uniformGradB1_large_coordinates m a t Y]
    simpa [x] using mul_pos ha hgrad
  have hxa : x/a = Y := by
    dsimp [x]
    field_simp
  have hscaled :
      0 ≤ a^2*uniformFaceBCoreB2 (m+4) a (t+1) (x/a) := by
    by_cases hpoly0 : 0 ≤ uniformLargeGrad1Poly m a t 0
    · have hbase := uniformLargeEnd_at_zero_nonneg_of_grad
        m a t hm ha ha1 ht hpoly0
      have hmono := uniformLargeEnd_mono
        m a t 0 x hm ha ha1 ht (by norm_num) hx.le
      norm_num at hmono
      linarith
    · have hpoly0neg : uniformLargeGrad1Poly m a t 0 < 0 :=
        lt_of_not_ge hpoly0
      let f : ℝ → ℝ := fun z => uniformLargeGrad1Poly m a t z
      have hf : Continuous f := by
        dsimp [f]
        unfold uniformLargeGrad1Poly
        fun_prop
      have hzeroIcc : (0 : ℝ) ∈ Set.Icc (f 0) (f x) := by
        constructor
        · dsimp [f]
          linarith
        · dsimp [f]
          linarith
      have hzeroImage :=
        intermediate_value_Icc hx.le hf.continuousOn hzeroIcc
      rcases hzeroImage with ⟨xstar, hxstarIcc, hroot⟩
      have hxstarpos : 0 < xstar := by
        rcases hxstarIcc with ⟨hxstar0, _⟩
        by_contra hnot
        have hxstarzero : xstar = 0 := by linarith
        subst xstar
        dsimp [f] at hroot
        linarith
      have hxstarx : xstar ≤ x := hxstarIcc.2
      have haxstar : a*(xstar/a) = xstar := by field_simp
      have hcoord := uniformGradB1_large_coordinates m a t (xstar/a)
      rw [haxstar] at hcoord
      dsimp [f] at hroot
      have hgrad1zero :
          uniformGradB1 (m+4) a (t+1) (xstar/a) = 0 := by
        have hmulzero :
            a*uniformGradB1 (m+4) a (t+1) (xstar/a) = 0 :=
          hcoord.trans hroot
        exact (mul_eq_zero.mp hmulzero).resolve_left ha.ne'
      have hactivezero :
          uniformGradB (m+4) a (t+1) (xstar/a) 1 = 0 := by
        simpa [uniformGradB1] using hgrad1zero
      have hboundary := uniformFaceBCore_nonneg_at_grad_zero
        (m+4) a (t+1) (xstar/a) 1 (by linarith) ha ha1
        (by linarith) (by positivity) (by norm_num) (by norm_num)
        hactivezero
      have hendstar :
          0 ≤ uniformFaceBCoreB2 (m+4) a (t+1) (xstar/a) := by
        simpa [uniformFaceBCore, uniformFaceBCoreB2] using hboundary
      have hmonostar := uniformLargeEnd_mono
        m a t xstar x hm ha ha1 ht hxstarpos.le hxstarx
      nlinarith [mul_nonneg (sq_nonneg a) hendstar]
  rw [hxa] at hscaled
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos ha)).mp hscaled

/-- Final reduction after the compact scale range has been discharged.  The
remaining certificates are needed only for `T ≥ 1`. -/
theorem uniformSharpFaceB_nonneg_of_large_endpoint_certificates
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hmid0 : 1 ≤ T → 0 ≤ uniformGradB0 n a T Y →
      0 ≤ uniformFaceBCoreB1 n a T Y)
    (hmidslope : 1 ≤ T →
      uniformGradB0 n a T Y < uniformGradB1 n a T Y →
      0 ≤ uniformFaceBCoreB1 n a T Y)
    (hend : 1 ≤ T → 0 < uniformGradB1 n a T Y →
      0 ≤ uniformFaceBCoreB2 n a T Y) :
    0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformSharpFaceB n a T Y q := by
  intro hgrad _hterminal
  by_cases hT1 : T ≤ 1
  · exact uniformSharpFaceB_nonneg_of_T_le_one
      n a T Y q hn ha ha1 hT hT1 hY hq hq1
  · have hTlarge : 1 ≤ T := le_of_not_ge hT1
    apply uniformSharpFaceB_nonneg_of_core n a T Y q hn ha hT hY hq
    exact uniformFaceBCore_nonneg_of_endpoint_certificates
      n a T Y q hn ha ha1 hT hY hq hq1 hgrad
      (hmid0 hTlarge) (hmidslope hTlarge) (hend hTlarge)

/-- After the normalized large-slope calculation, only the nonnegative-left-
gradient and positive-right-gradient endpoint implications remain. -/
theorem uniformSharpFaceB_nonneg_of_two_large_endpoint_certificates
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hmid0 : 1 ≤ T → 0 ≤ uniformGradB0 n a T Y →
      0 ≤ uniformFaceBCoreB1 n a T Y)
    (hend : 1 ≤ T → 0 < uniformGradB1 n a T Y →
      0 ≤ uniformFaceBCoreB2 n a T Y) :
    0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformSharpFaceB n a T Y q := by
  apply uniformSharpFaceB_nonneg_of_large_endpoint_certificates
    n a T Y q hn ha ha1 hT hY hq hq1 hmid0
  · intro hTlarge hslope
    exact uniformFaceBCoreB1_nonneg_of_large_slope
      n a T Y hn ha ha1 hTlarge hY.le hslope
  · exact hend

/-- The right endpoint is now unconditional; only the large-scale
nonnegative-left-gradient middle coefficient remains to be certified. -/
theorem uniformSharpFaceB_nonneg_of_large_mid0_certificate
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hmid0 : 1 ≤ T → 0 ≤ uniformGradB0 n a T Y →
      0 ≤ uniformFaceBCoreB1 n a T Y) :
    0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformSharpFaceB n a T Y q := by
  apply uniformSharpFaceB_nonneg_of_two_large_endpoint_certificates
    n a T Y q hn ha ha1 hT hY hq hq1 hmid0
  intro hTlarge hgrad1
  exact uniformFaceBCoreB2_nonneg_of_large_grad1
    n a T Y hn ha ha1 hTlarge hY hgrad1

/-- The final unresolved certificate can be restricted to `T ≥ 3/2`. -/
theorem uniformSharpFaceB_nonneg_of_large_mid0_above_three_halves
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hmid0 : 3/2 ≤ T → 0 ≤ uniformGradB0 n a T Y →
      0 ≤ uniformFaceBCoreB1 n a T Y) :
    0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformSharpFaceB n a T Y q := by
  apply uniformSharpFaceB_nonneg_of_large_mid0_certificate
    n a T Y q hn ha ha1 hT hY hq hq1
  intro hTlarge hgrad0
  by_cases hT32 : T ≤ 3/2
  · exact uniformFaceBCoreB1_nonneg_of_T_le_three_halves
      n a T Y hn ha ha1 hTlarge hT32 hY.le
  · exact hmid0 (le_of_not_ge hT32) hgrad0

/-- Equivalently, after the larger compact strip is used, the final
certificate is needed only for `T ≥ 2`. -/
theorem uniformSharpFaceB_nonneg_of_large_mid0_above_two
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hmid0 : 2 ≤ T → 0 ≤ uniformGradB0 n a T Y →
      0 ≤ uniformFaceBCoreB1 n a T Y) :
    0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformSharpFaceB n a T Y q := by
  apply uniformSharpFaceB_nonneg_of_large_mid0_certificate
    n a T Y q hn ha ha1 hT hY hq hq1
  intro hTlarge hgrad0
  by_cases hT2 : T ≤ 2
  · exact uniformFaceBCoreB1_nonneg_of_T_le_two
      n a T Y hn ha ha1 hTlarge hT2 hY.le
  · exact hmid0 (le_of_not_ge hT2) hgrad0

/-- Using the positive-semidefinite Bernstein certificate, the final
large-scale implication is needed only for `T ≥ 9`. -/
theorem uniformSharpFaceB_nonneg_of_large_mid0_above_nine
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hmid0 : 9 ≤ T → 0 ≤ uniformGradB0 n a T Y →
      0 ≤ uniformFaceBCoreB1 n a T Y) :
    0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformSharpFaceB n a T Y q := by
  apply uniformSharpFaceB_nonneg_of_large_mid0_certificate
    n a T Y q hn ha ha1 hT hY hq hq1
  intro hTlarge hgrad0
  by_cases hT9 : T ≤ 9
  · exact uniformFaceBCoreB1_nonneg_of_T_le_nine
      n a T Y hn ha hTlarge hT9 hY.le
  · exact hmid0 (le_of_not_ge hT9) hgrad0


end SSP.K3AllStages
