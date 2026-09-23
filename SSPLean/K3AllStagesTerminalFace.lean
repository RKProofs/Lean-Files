import SSPLean.K3AllStagesPositiveSlope
import SSPLean.K3AllStagesTerminalFaceRemainingCert

/-!
# Terminal-face reduction for the uniform `k = 3` induction

The terminal-face numerator has a positive common factor and a core which is
only quadratic in the terminal mixture parameter `q`.  This module exposes
that factorization and its three Bernstein coefficients.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

noncomputable def uniformFaceBCoreQ0 (n a _T Y : ℝ) : ℝ :=
  (n + 2) *
    (Y^4*a^2*n^3 + Y^4*a^2*n^2 + 6*Y^3*a^3*n^5
      + 6*Y^3*a^3*n^4 - 12*Y^3*a^3*n^3 - 4*Y^3*a^2*n^5
      - 20*Y^3*a^2*n^4 + 4*Y^3*a^2*n^3 + 20*Y^3*a^2*n^2
      + 2*Y^3*a*n^5 + 8*Y^3*a*n^4 + 6*Y^3*a*n^3
      - 8*Y^3*a*n^2 - 8*Y^3*a*n + 12*Y^2*a^2*n^5
      - 36*Y^2*a^2*n^4 + 36*Y^2*a^2*n^3 - 12*Y^2*a^2*n^2
      + 4*Y^2*a*n^5 - 8*Y^2*a*n^4 + 8*Y^2*a*n^2
      - 4*Y^2*a*n + 24*Y*a*n^5 - 96*Y*a*n^4 + 144*Y*a*n^3
      - 96*Y*a*n^2 + 24*Y*a*n + 12*n^5 - 60*n^4 + 120*n^3
      - 120*n^2 + 60*n - 12)

noncomputable def uniformFaceBCoreQ1 (n a T Y : ℝ) : ℝ :=
  T *
    (T*Y^3*a*n^4 + 3*T*Y^3*a*n^3 + 2*T*Y^3*a*n^2
      + 6*T*Y^2*a^2*n^6 + 18*T*Y^2*a^2*n^5 + 6*T*Y^2*a^2*n^4
      - 30*T*Y^2*a^2*n^3 - 2*T*Y^2*a*n^6 - 14*T*Y^2*a*n^5
      - 14*T*Y^2*a*n^4 + 14*T*Y^2*a*n^3 + 16*T*Y^2*a*n^2
      + 8*T*Y*a*n^6 - 16*T*Y*a*n^5 - 12*T*Y*a*n^4
      + 40*T*Y*a*n^3 - 20*T*Y*a*n^2 + 4*T*n^6 - 24*T*n^5
      + 8*T*n^4 + 80*T*n^3 - 108*T*n^2 + 40*T*n
      - 2*Y^3*a^2*n^6 - 14*Y^3*a^2*n^5 - 18*Y^3*a^2*n^4
      + 14*Y^3*a^2*n^3 + 20*Y^3*a^2*n^2 + 2*Y^3*a*n^6
      + 12*Y^3*a*n^5 + 22*Y^3*a*n^4 + 4*Y^3*a*n^3
      - 24*Y^3*a*n^2 - 16*Y^3*a*n - 36*Y^2*a^2*n^5
      + 108*Y^2*a^2*n^3 - 72*Y^2*a^2*n^2 + 12*Y^2*a*n^6
      + 24*Y^2*a*n^5 - 24*Y^2*a*n^4 - 48*Y^2*a*n^3
      + 12*Y^2*a*n^2 + 24*Y^2*a*n + 36*Y*a*n^6 - 72*Y*a*n^5
      - 72*Y*a*n^4 + 288*Y*a*n^3 - 252*Y*a*n^2 + 72*Y*a*n
      + 24*n^6 - 72*n^5 + 240*n^3 - 360*n^2 + 216*n - 48)

noncomputable def uniformFaceBCoreQ2 (n a T Y : ℝ) : ℝ :=
  -T^2 * (n - 1) *
    (-6*T^2*Y*a*n^3 + T^2*n^5 + 8*T^2*n^4 + 5*T^2*n^3
      - 14*T^2*n^2 - 4*T*Y^2*a*n^3 - 4*T*Y^2*a*n^2
      - 6*T*Y*a*n^5 + 6*T*Y*a*n^3 - 4*T*n^5 + 20*T*n^4
      + 12*T*n^3 - 68*T*n^2 + 40*T*n + 9*Y^2*a^2*n^5
      + 36*Y^2*a^2*n^4 + 9*Y^2*a^2*n^3 - 54*Y^2*a^2*n^2
      - 8*Y^2*a*n^5 - 32*Y^2*a*n^4 - 24*Y^2*a*n^3
      + 32*Y^2*a*n^2 + 32*Y^2*a*n - 12*Y*a*n^5
      + 12*Y*a*n^4 + 36*Y*a*n^3 - 60*Y*a*n^2 + 24*Y*a*n
      - 12*n^5 + 24*n^4 + 24*n^3 - 96*n^2 + 84*n - 24)

noncomputable def uniformFaceBCore (n a T Y q : ℝ) : ℝ :=
  uniformFaceBCoreQ0 n a T Y + q * uniformFaceBCoreQ1 n a T Y
    + q^2 * uniformFaceBCoreQ2 n a T Y

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformFaceBNum_factor (n a T Y q : ℝ) :
    uniformFaceBNum n a T Y q =
      (n + 2) * uniformSideFactor n a T Y q *
        uniformFaceBCore n a T Y q := by
  unfold uniformFaceBNum uniformCornerPoly uniformFaceBCore
  unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1 uniformFaceBCoreQ2
  unfold uniformHBB uniformGradB uniformSideFactor
  unfold uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num
  ring

noncomputable def uniformFaceBCoreB0 (n a T Y : ℝ) : ℝ :=
  uniformFaceBCoreQ0 n a T Y

noncomputable def uniformFaceBCoreB1 (n a T Y : ℝ) : ℝ :=
  uniformFaceBCoreQ0 n a T Y + uniformFaceBCoreQ1 n a T Y / 2

noncomputable def uniformFaceBCoreB2 (n a T Y : ℝ) : ℝ :=
  uniformFaceBCoreQ0 n a T Y + uniformFaceBCoreQ1 n a T Y
    + uniformFaceBCoreQ2 n a T Y

noncomputable def uniformFaceBCoreB0A0 (m : ℝ) : ℝ :=
  12 * (m + 3)^5 * (m + 6)

noncomputable def uniformFaceBCoreB0A1 (m Y : ℝ) : ℝ :=
  2 * (m + 3) * (m + 6) / 3 *
    (Y^3*m^4 + 21*Y^3*m^3 + 164*Y^3*m^2 + 564*Y^3*m
      + 720*Y^3 + 2*Y^2*m^4 + 30*Y^2*m^3 + 166*Y^2*m^2
      + 402*Y^2*m + 360*Y^2 + 12*Y*m^4 + 156*Y*m^3
      + 756*Y*m^2 + 1620*Y*m + 1296*Y + 18*m^4 + 216*m^3
      + 972*m^2 + 1944*m + 1458)

noncomputable def uniformFaceBCoreB0A2 (m Y : ℝ) : ℝ :=
  (m + 6) / 3 *
    (Y^4*m^3 + 13*Y^4*m^2 + 56*Y^4*m + 80*Y^4
      - 4*Y^3*m^4 - 48*Y^3*m^3 - 188*Y^3*m^2 - 240*Y^3*m
      + 20*Y^2*m^5 + 348*Y^2*m^4 + 2404*Y^2*m^3
      + 8244*Y^2*m^2 + 14040*Y^2*m + 9504*Y^2
      + 48*Y*m^5 + 768*Y*m^4 + 4896*Y*m^3 + 15552*Y*m^2
      + 24624*Y*m + 15552*Y + 36*m^5 + 540*m^4 + 3240*m^3
      + 9720*m^2 + 14580*m + 8748)

noncomputable def uniformFaceBCoreB0A3 (m Y : ℝ) : ℝ :=
  (m + 6) *
    (Y^4*m^3 + 13*Y^4*m^2 + 56*Y^4*m + 80*Y^4
      + 4*Y^3*m^5 + 74*Y^3*m^4 + 542*Y^3*m^3 + 1972*Y^3*m^2
      + 3576*Y^3*m + 2592*Y^3 + 16*Y^2*m^5 + 276*Y^2*m^4
      + 1892*Y^2*m^3 + 6444*Y^2*m^2 + 10908*Y^2*m + 7344*Y^2
      + 24*Y*m^5 + 384*Y*m^4 + 2448*Y*m^3 + 7776*Y*m^2
      + 12312*Y*m + 7776*Y + 12*m^5 + 180*m^4 + 1080*m^3
      + 3240*m^2 + 4860*m + 2916)

theorem uniformFaceBCoreB0_bernstein_a (m a T Y : ℝ) :
    uniformFaceBCoreB0 (m + 4) a T Y =
      cornerBern3 (uniformFaceBCoreB0A0 m)
        (uniformFaceBCoreB0A1 m Y) (uniformFaceBCoreB0A2 m Y)
        (uniformFaceBCoreB0A3 m Y) a := by
  unfold uniformFaceBCoreB0 uniformFaceBCoreQ0
  unfold uniformFaceBCoreB0A0 uniformFaceBCoreB0A1
  unfold uniformFaceBCoreB0A2 uniformFaceBCoreB0A3 cornerBern3
  ring

private theorem uniformFaceBCoreB0A2_nonneg
    (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB0A2 m Y := by
  let A := (m + 4)^2 * (m + 5)
  let B := 4*m*(m + 3)*(m + 4)*(m + 5)
  let C := 4*(m + 3)^3*(m + 4)*(5*m + 22)
  have hA : 0 < A := by dsimp [A]; positivity
  have hdisc : 0 ≤ 4*A*C-B^2 := by
    have hid : 4*A*C-B^2 =
        32*(m + 3)^2*(m + 4)^2*(m + 5)*
          (2*m^3 + 26*m^2 + 107*m + 132) := by
      dsimp [A, B, C]
      ring
    rw [hid]
    positivity
  have hquad : 0 ≤ A*Y^2-B*Y+C := by
    have hid : 4*A*(A*Y^2-B*Y+C) =
        (2*A*Y-B)^2+(4*A*C-B^2) := by ring
    have hscaled : 0 ≤ 4*A*(A*Y^2-B*Y+C) := by
      rw [hid]
      positivity
    exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*A)).mp hscaled
  unfold uniformFaceBCoreB0A2
  have hdecomp :
      Y^4*m^3 + 13*Y^4*m^2 + 56*Y^4*m + 80*Y^4
        - 4*Y^3*m^4 - 48*Y^3*m^3 - 188*Y^3*m^2 - 240*Y^3*m
        + 20*Y^2*m^5 + 348*Y^2*m^4 + 2404*Y^2*m^3
        + 8244*Y^2*m^2 + 14040*Y^2*m + 9504*Y^2
        + 48*Y*m^5 + 768*Y*m^4 + 4896*Y*m^3 + 15552*Y*m^2
        + 24624*Y*m + 15552*Y + 36*m^5 + 540*m^4 + 3240*m^3
        + 9720*m^2 + 14580*m + 8748 =
      Y^2*(A*Y^2-B*Y+C)
        + 48*Y*m^5 + 768*Y*m^4 + 4896*Y*m^3 + 15552*Y*m^2
        + 24624*Y*m + 15552*Y + 36*m^5 + 540*m^4 + 3240*m^3
        + 9720*m^2 + 14580*m + 8748 := by
    dsimp [A, B, C]
    ring
  rw [hdecomp]
  positivity

theorem uniformFaceBCoreB0_nonneg
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB0 n a T Y := by
  let m := n - 4
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hnid : m + 4 = n := by dsimp [m]; ring
  rw [← hnid, uniformFaceBCoreB0_bernstein_a]
  apply cornerBern3_nonneg <;> try assumption
  · unfold uniformFaceBCoreB0A0
    positivity
  · unfold uniformFaceBCoreB0A1
    positivity
  · exact uniformFaceBCoreB0A2_nonneg m Y hm hY
  · unfold uniformFaceBCoreB0A3
    positivity

theorem uniformFaceBCore_bernstein_q (n a T Y q : ℝ) :
    uniformFaceBCore n a T Y q =
      uniformFaceBCoreB0 n a T Y * (1 - q)^2
        + 2 * uniformFaceBCoreB1 n a T Y * q * (1 - q)
        + uniformFaceBCoreB2 n a T Y * q^2 := by
  unfold uniformFaceBCore uniformFaceBCoreB0 uniformFaceBCoreB1
  unfold uniformFaceBCoreB2
  ring

theorem uniformFaceBCore_nonneg_of_bernstein
    (n a T Y q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (h0 : 0 ≤ uniformFaceBCoreB0 n a T Y)
    (h1 : 0 ≤ uniformFaceBCoreB1 n a T Y)
    (h2 : 0 ≤ uniformFaceBCoreB2 n a T Y) :
    0 ≤ uniformFaceBCore n a T Y q := by
  rw [uniformFaceBCore_bernstein_q]
  positivity

theorem uniformSharpFaceB_nonneg_of_core
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q)
    (hcore : 0 ≤ uniformFaceBCore n a T Y q) :
    0 ≤ uniformSharpFaceB n a T Y q := by
  apply uniformSharpFaceB_nonneg_of_num n a T Y q hn hT hY hq
    (by positivity)
  rw [uniformFaceBNum_factor]
  have hside := uniformSideFactor_pos n a T Y q (by linarith)
    ha.le hT.le hY.le hq.le
  positivity

/-- The terminal-face implication is now reduced to the three coefficients
of a quadratic Bernstein polynomial in `q`. -/
theorem uniformSharpFaceB_nonneg_of_bernstein_coefficients
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (h0 : 0 ≤ uniformFaceBCoreB0 n a T Y)
    (h1 : 0 ≤ uniformFaceBCoreB1 n a T Y)
    (h2 : 0 ≤ uniformFaceBCoreB2 n a T Y) :
    0 ≤ uniformSharpFaceB n a T Y q := by
  apply uniformSharpFaceB_nonneg_of_core n a T Y q hn ha hT hY hq
  exact uniformFaceBCore_nonneg_of_bernstein
    n a T Y q hq.le hq1 h0 h1 h2

/-- Conditional form matching the remaining induction hypothesis. -/
theorem uniformSharpFaceB_nonneg_of_bernstein_certificate
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hcoeff : 0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformFaceBCoreB0 n a T Y ∧
      0 ≤ uniformFaceBCoreB1 n a T Y ∧
      0 ≤ uniformFaceBCoreB2 n a T Y) :
    0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformSharpFaceB n a T Y q := by
  intro hgrad hterminal
  obtain ⟨h0, h1, h2⟩ := hcoeff hgrad hterminal
  exact uniformSharpFaceB_nonneg_of_bernstein_coefficients
    n a T Y q hn ha hT hY hq hq1 h0 h1 h2

/-- A sufficient terminal-face reduction after discharging the `q = 0`
Bernstein coefficient unconditionally. -/
theorem uniformSharpFaceB_nonneg_of_remaining_bernstein_certificates
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hcoeff : 0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformFaceBCoreB1 n a T Y ∧
      0 ≤ uniformFaceBCoreB2 n a T Y) :
    0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformSharpFaceB n a T Y q := by
  intro hgrad hterminal
  obtain ⟨h1, h2⟩ := hcoeff hgrad hterminal
  apply uniformSharpFaceB_nonneg_of_bernstein_coefficients
    n a T Y q hn ha hT hY hq hq1
  · exact uniformFaceBCoreB0_nonneg n a T Y hn ha.le ha1 hY.le
  · exact h1
  · exact h2

/-! ### Affine-gradient reduction in the terminal mixture weight

The coefficientwise Bernstein approach above is stronger than necessary (and
its final coefficient need not be nonnegative).  The useful structure is that
the active gradient is affine in `q`, while the face core is quadratic.  This
is the same moving-endpoint argument used in the four-stage calculation. -/

noncomputable def uniformGradB0 (n a T Y : ℝ) : ℝ :=
  uniformGradB n a T Y 0

noncomputable def uniformGradB1 (n a T Y : ℝ) : ℝ :=
  uniformGradB n a T Y 1

theorem uniformGradB_bernstein_q (n a T Y q : ℝ) :
    uniformGradB n a T Y q =
      (1-q) * uniformGradB0 n a T Y + q * uniformGradB1 n a T Y := by
  unfold uniformGradB0 uniformGradB1 uniformGradB
  ring

theorem uniformGradB_endpoint_dichotomy
    (n a T Y q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hgrad : 0 < uniformGradB n a T Y q) :
    0 < uniformGradB0 n a T Y ∨ 0 < uniformGradB1 n a T Y := by
  rw [uniformGradB_bernstein_q] at hgrad
  by_contra hnot
  push Not at hnot
  have hleft : (1-q) * uniformGradB0 n a T Y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq1) hnot.1
  have hright : q * uniformGradB1 n a T Y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hq hnot.2
  linarith

/-- At a zero of the active terminal gradient, the face numerator is the
positive terminal Hessian factor times the already-proved corner numerator. -/
theorem uniformFaceBCore_nonneg_at_grad_zero
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hgrad : uniformGradB n a T Y q = 0) :
    0 ≤ uniformFaceBCore n a T Y q := by
  have hcorner : 0 ≤ uniformCornerPoly n a T Y q := by
    apply uniformCornerPoly_nonneg_of_q_one n a T Y q hn ha.le ha1
      hT.le hY.le hq.le hq1
    exact uniformCornerQOne_nonneg n a T Y hn ha.le ha1 hT.le hY.le
  have hH : 0 < uniformHBB n a T Y q := by
    let m := n - 4
    have hm : 0 ≤ m := by dsimp [m]; linarith
    have hnid : m + 4 = n := by dsimp [m]; ring
    rw [← hnid]
    unfold uniformHBB
    ring_nf
    positivity
  have hnum : 0 ≤ uniformFaceBNum n a T Y q := by
    unfold uniformFaceBNum
    rw [hgrad]
    simpa using mul_nonneg hH.le hcorner
  rw [uniformFaceBNum_factor] at hnum
  have hside := uniformSideFactor_pos n a T Y q (by linarith)
    ha.le hT.le hY.le hq.le
  have hscale : 0 < (n + 2) * uniformSideFactor n a T Y q := by
    positivity
  exact (mul_nonneg_iff_of_pos_left hscale).mp hnum

/-- Restrict the quadratic face core to an initial `q`-segment. -/
theorem uniformFaceBCore_initial_segment_nonneg
    (n a T Y q qstar : ℝ)
    (hq : 0 ≤ q) (hqqstar : q ≤ qstar) (hqstar1 : qstar ≤ 1)
    (h0 : 0 ≤ uniformFaceBCoreB0 n a T Y)
    (h1 : 0 ≤ uniformFaceBCoreB1 n a T Y)
    (hboundary : 0 ≤ uniformFaceBCore n a T Y qstar) :
    0 ≤ uniformFaceBCore n a T Y q := by
  have hqstar : 0 ≤ qstar := le_trans hq hqqstar
  by_cases hz : qstar = 0
  · have hqz : q = 0 := by linarith
    subst q
    simpa [uniformFaceBCore, uniformFaceBCoreB0]
  · have hqstarpos : 0 < qstar := lt_of_le_of_ne hqstar (Ne.symm hz)
    have hmid : 0 ≤
        (1-qstar) * uniformFaceBCoreB0 n a T Y
          + qstar * uniformFaceBCoreB1 n a T Y := by
      positivity
    have hid : qstar^2 * uniformFaceBCore n a T Y q =
        uniformFaceBCoreB0 n a T Y * (qstar-q)^2
          + 2 * ((1-qstar) * uniformFaceBCoreB0 n a T Y
            + qstar * uniformFaceBCoreB1 n a T Y) * q * (qstar-q)
          + uniformFaceBCore n a T Y qstar * q^2 := by
      rw [uniformFaceBCore_bernstein_q, uniformFaceBCore_bernstein_q]
      ring
    have hscaled : 0 ≤ qstar^2 * uniformFaceBCore n a T Y q := by
      rw [hid]
      positivity
    exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos hqstarpos)).mp hscaled

/-- The exact moving-endpoint reduction.  Only two genuine polynomial facts
remain: positivity of the middle coefficient in the two indicated gradient
regimes, and positivity of the `q = 1` endpoint when its gradient is positive. -/
theorem uniformFaceBCore_nonneg_of_endpoint_certificates
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hgrad : 0 < uniformGradB n a T Y q)
    (hmid0 : 0 ≤ uniformGradB0 n a T Y →
      0 ≤ uniformFaceBCoreB1 n a T Y)
    (hmidslope : uniformGradB0 n a T Y < uniformGradB1 n a T Y →
      0 ≤ uniformFaceBCoreB1 n a T Y)
    (hend : 0 < uniformGradB1 n a T Y →
      0 ≤ uniformFaceBCoreB2 n a T Y) :
    0 ≤ uniformFaceBCore n a T Y q := by
  have h0 := uniformFaceBCoreB0_nonneg n a T Y hn ha.le ha1 hY.le
  by_cases hG0 : 0 ≤ uniformGradB0 n a T Y
  · have hmid := hmid0 hG0
    by_cases hG1 : 0 < uniformGradB1 n a T Y
    · exact uniformFaceBCore_nonneg_of_bernstein n a T Y q hq.le hq1
        h0 hmid (hend hG1)
    · have hG1' : uniformGradB1 n a T Y ≤ 0 := le_of_not_gt hG1
      have hG0' : 0 < uniformGradB0 n a T Y := by
        rw [uniformGradB_bernstein_q] at hgrad
        by_contra hnot
        have hG0nonpos : uniformGradB0 n a T Y ≤ 0 := le_of_not_gt hnot
        have hleft : (1-q) * uniformGradB0 n a T Y ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq1) hG0nonpos
        have hright : q * uniformGradB1 n a T Y ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hq.le hG1'
        linarith
      let qstar := uniformGradB0 n a T Y /
        (uniformGradB0 n a T Y - uniformGradB1 n a T Y)
      have hden : 0 < uniformGradB0 n a T Y - uniformGradB1 n a T Y := by
        linarith
      have hqstar : 0 < qstar := by dsimp [qstar]; positivity
      have hqstar1 : qstar ≤ 1 := by
        dsimp [qstar]
        rw [div_le_one hden]
        linarith
      have hqqstar : q ≤ qstar := by
        rw [uniformGradB_bernstein_q] at hgrad
        dsimp [qstar]
        rw [le_div_iff₀ hden]
        nlinarith
      have hGstar : uniformGradB n a T Y qstar = 0 := by
        rw [uniformGradB_bernstein_q]
        dsimp [qstar]
        field_simp [hden.ne']
        ring
      have hboundary := uniformFaceBCore_nonneg_at_grad_zero
        n a T Y qstar hn ha ha1 hT hY hqstar hqstar1 hGstar
      exact uniformFaceBCore_initial_segment_nonneg
        n a T Y q qstar hq.le hqqstar hqstar1 h0 hmid hboundary
  · have hG0' : uniformGradB0 n a T Y < 0 := lt_of_not_ge hG0
    have hG1 := (uniformGradB_endpoint_dichotomy n a T Y q hq.le hq1 hgrad)
      |>.resolve_left (not_lt_of_ge hG0'.le)
    exact uniformFaceBCore_nonneg_of_bernstein n a T Y q hq.le hq1
      h0 (hmidslope (by linarith)) (hend hG1)

/-! ### The compact terminal-scale range -/

private noncomputable def sampledBern3C1 (f0 f1 f2 f3 : ℝ) : ℝ :=
  (7*f0 + 18*f1 - 9*f2 + 2*f3) / 18

private noncomputable def sampledBern3C2 (f0 f1 f2 f3 : ℝ) : ℝ :=
  (2*f0 + 21*f1 - 6*f2 + f3) / 18

private noncomputable def uniformFaceBCoreB1TC1 (n a Y : ℝ) : ℝ :=
  (uniformFaceBCoreB1 n a 0 Y + 4*uniformFaceBCoreB1 n a 1 Y
    - uniformFaceBCoreB1 n a 2 Y) / 4

private theorem uniformFaceBCoreB1TC1_bernstein_a (m a Y : ℝ) :
    uniformFaceBCoreB1TC1 (m+4) a Y =
      cornerBern3 (uniformFaceBCoreB1TC1 (m+4) 0 Y)
        (sampledBern3C1 (uniformFaceBCoreB1TC1 (m+4) 0 Y)
          (uniformFaceBCoreB1TC1 (m+4) 1 Y)
          (uniformFaceBCoreB1TC1 (m+4) 2 Y)
          (uniformFaceBCoreB1TC1 (m+4) 3 Y))
        (sampledBern3C2 (uniformFaceBCoreB1TC1 (m+4) 0 Y)
          (uniformFaceBCoreB1TC1 (m+4) 1 Y)
          (uniformFaceBCoreB1TC1 (m+4) 2 Y)
          (uniformFaceBCoreB1TC1 (m+4) 3 Y))
        (uniformFaceBCoreB1TC1 (m+4) 1 Y) a := by
  unfold uniformFaceBCoreB1TC1 sampledBern3C1 sampledBern3C2
  unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1 cornerBern3
  ring

private theorem uniformFaceBCoreB1TC1_nonneg
    (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1TC1 (m+4) a Y := by
  rw [uniformFaceBCoreB1TC1_bernstein_a]
  apply cornerBern3_nonneg <;> try assumption
  · unfold uniformFaceBCoreB1TC1 uniformFaceBCoreB1
    unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  · unfold sampledBern3C1 uniformFaceBCoreB1TC1 uniformFaceBCoreB1
    unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  · unfold sampledBern3C2 uniformFaceBCoreB1TC1 uniformFaceBCoreB1
    unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  · unfold uniformFaceBCoreB1TC1 uniformFaceBCoreB1
    unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity

private theorem uniformFaceBCoreB1_bernstein_T (n a T Y : ℝ) :
    uniformFaceBCoreB1 n a T Y =
      cornerBern2 (uniformFaceBCoreB1 n a 0 Y)
        (uniformFaceBCoreB1TC1 n a Y)
        (uniformFaceBCoreB1 n a 1 Y) T := by
  unfold uniformFaceBCoreB1TC1 uniformFaceBCoreB1
  unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1 cornerBern2
  ring

private theorem uniformFaceBCoreB1_at_T_one_nonneg
    (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1 (m+4) a 1 Y := by
  have hid : uniformFaceBCoreB1 (m+4) a 1 Y =
      cornerBern3 (uniformFaceBCoreB1 (m+4) 0 1 Y)
        (sampledBern3C1 (uniformFaceBCoreB1 (m+4) 0 1 Y)
          (uniformFaceBCoreB1 (m+4) 1 1 Y)
          (uniformFaceBCoreB1 (m+4) 2 1 Y)
          (uniformFaceBCoreB1 (m+4) 3 1 Y))
        (sampledBern3C2 (uniformFaceBCoreB1 (m+4) 0 1 Y)
          (uniformFaceBCoreB1 (m+4) 1 1 Y)
          (uniformFaceBCoreB1 (m+4) 2 1 Y)
          (uniformFaceBCoreB1 (m+4) 3 1 Y))
        (uniformFaceBCoreB1 (m+4) 1 1 Y) a := by
    unfold sampledBern3C1 sampledBern3C2 cornerBern3
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring
  rw [hid]
  apply cornerBern3_nonneg <;> try assumption
  · unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  · unfold sampledBern3C1 uniformFaceBCoreB1
    unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  · unfold sampledBern3C2 uniformFaceBCoreB1
    unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  · unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity

theorem uniformFaceBCoreB1_nonneg_of_T_le_one
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1 n a T Y := by
  let m := n-4
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  rw [← hnid, uniformFaceBCoreB1_bernstein_T]
  apply cornerBern2_nonneg <;> try assumption
  · have hzero : uniformFaceBCoreB1 (m+4) a 0 Y =
        uniformFaceBCoreB0 (m+4) a 0 Y := by
      unfold uniformFaceBCoreB1 uniformFaceBCoreB0
      unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1
      ring
    rw [hzero]
    exact uniformFaceBCoreB0_nonneg (m+4) a 0 Y (by linarith) ha ha1 hY
  · exact uniformFaceBCoreB1TC1_nonneg m a Y hm ha ha1 hY
  · exact uniformFaceBCoreB1_at_T_one_nonneg m a Y hm ha ha1 hY

private noncomputable def sampledBern4C1 (f0 f1 f2 f3 f4 : ℝ) : ℝ :=
  (23*f0 + 48*f1 - 36*f2 + 16*f3 - 3*f4) / 48

private noncomputable def sampledBern4C2 (f0 f1 f2 f3 f4 : ℝ) : ℝ :=
  (29*f0 + 184*f1 - 102*f2 + 40*f3 - 7*f4) / 144

private noncomputable def sampledBern4C3 (f0 f1 f2 f3 f4 : ℝ) : ℝ :=
  (3*f0 + 58*f1 - 18*f2 + 6*f3 - f4) / 48

private noncomputable def uniformFaceBCoreB2TC1 (n a Y : ℝ) : ℝ :=
  sampledBern4C1 (uniformFaceBCoreB2 n a 0 Y)
    (uniformFaceBCoreB2 n a 1 Y) (uniformFaceBCoreB2 n a 2 Y)
    (uniformFaceBCoreB2 n a 3 Y) (uniformFaceBCoreB2 n a 4 Y)

private noncomputable def uniformFaceBCoreB2TC2 (n a Y : ℝ) : ℝ :=
  sampledBern4C2 (uniformFaceBCoreB2 n a 0 Y)
    (uniformFaceBCoreB2 n a 1 Y) (uniformFaceBCoreB2 n a 2 Y)
    (uniformFaceBCoreB2 n a 3 Y) (uniformFaceBCoreB2 n a 4 Y)

private noncomputable def uniformFaceBCoreB2TC3 (n a Y : ℝ) : ℝ :=
  sampledBern4C3 (uniformFaceBCoreB2 n a 0 Y)
    (uniformFaceBCoreB2 n a 1 Y) (uniformFaceBCoreB2 n a 2 Y)
    (uniformFaceBCoreB2 n a 3 Y) (uniformFaceBCoreB2 n a 4 Y)

private theorem uniformFaceBCoreB2_bernstein_T (n a T Y : ℝ) :
    uniformFaceBCoreB2 n a T Y =
      cornerBern4 (uniformFaceBCoreB2 n a 0 Y)
        (uniformFaceBCoreB2TC1 n a Y) (uniformFaceBCoreB2TC2 n a Y)
        (uniformFaceBCoreB2TC3 n a Y) (uniformFaceBCoreB2 n a 1 Y) T := by
  unfold uniformFaceBCoreB2TC1 uniformFaceBCoreB2TC2
  unfold uniformFaceBCoreB2TC3 sampledBern4C1 sampledBern4C2 sampledBern4C3
  unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
  unfold uniformFaceBCoreQ2 cornerBern4
  ring

private theorem uniformFaceBCoreB2TC1_eq_B1TC1 (n a Y : ℝ) :
    uniformFaceBCoreB2TC1 n a Y = uniformFaceBCoreB1TC1 n a Y := by
  unfold uniformFaceBCoreB2TC1 uniformFaceBCoreB1TC1 sampledBern4C1
  unfold uniformFaceBCoreB2 uniformFaceBCoreB1
  unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1 uniformFaceBCoreQ2
  ring

set_option maxHeartbeats 3000000 in
private theorem uniformFaceBCoreB2TC2_nonneg
    (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB2TC2 (m+4) a Y := by
  have hid : uniformFaceBCoreB2TC2 (m+4) a Y =
      cornerBern3 (uniformFaceBCoreB2TC2 (m+4) 0 Y)
        (sampledBern3C1 (uniformFaceBCoreB2TC2 (m+4) 0 Y)
          (uniformFaceBCoreB2TC2 (m+4) 1 Y)
          (uniformFaceBCoreB2TC2 (m+4) 2 Y)
          (uniformFaceBCoreB2TC2 (m+4) 3 Y))
        (sampledBern3C2 (uniformFaceBCoreB2TC2 (m+4) 0 Y)
          (uniformFaceBCoreB2TC2 (m+4) 1 Y)
          (uniformFaceBCoreB2TC2 (m+4) 2 Y)
          (uniformFaceBCoreB2TC2 (m+4) 3 Y))
        (uniformFaceBCoreB2TC2 (m+4) 1 Y) a := by
    unfold uniformFaceBCoreB2TC2 sampledBern4C2
    unfold sampledBern3C1 sampledBern3C2 cornerBern3
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring
  rw [hid]
  apply cornerBern3_nonneg <;> try assumption
  · unfold uniformFaceBCoreB2TC2 sampledBern4C2
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring_nf
    positivity
  · unfold sampledBern3C1 uniformFaceBCoreB2TC2 sampledBern4C2
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring_nf
    positivity
  · unfold sampledBern3C2 uniformFaceBCoreB2TC2 sampledBern4C2
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring_nf
    positivity
  · unfold uniformFaceBCoreB2TC2 sampledBern4C2
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring_nf
    positivity

set_option maxHeartbeats 3000000 in
private theorem uniformFaceBCoreB2TC3_nonneg
    (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB2TC3 (m+4) a Y := by
  have hid : uniformFaceBCoreB2TC3 (m+4) a Y =
      cornerBern3 (uniformFaceBCoreB2TC3 (m+4) 0 Y)
        (sampledBern3C1 (uniformFaceBCoreB2TC3 (m+4) 0 Y)
          (uniformFaceBCoreB2TC3 (m+4) 1 Y)
          (uniformFaceBCoreB2TC3 (m+4) 2 Y)
          (uniformFaceBCoreB2TC3 (m+4) 3 Y))
        (sampledBern3C2 (uniformFaceBCoreB2TC3 (m+4) 0 Y)
          (uniformFaceBCoreB2TC3 (m+4) 1 Y)
          (uniformFaceBCoreB2TC3 (m+4) 2 Y)
          (uniformFaceBCoreB2TC3 (m+4) 3 Y))
        (uniformFaceBCoreB2TC3 (m+4) 1 Y) a := by
    unfold uniformFaceBCoreB2TC3 sampledBern4C3
    unfold sampledBern3C1 sampledBern3C2 cornerBern3
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring
  rw [hid]
  apply cornerBern3_nonneg <;> try assumption
  · unfold uniformFaceBCoreB2TC3 sampledBern4C3
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring_nf
    positivity
  · unfold sampledBern3C1 uniformFaceBCoreB2TC3 sampledBern4C3
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring_nf
    positivity
  · unfold sampledBern3C2 uniformFaceBCoreB2TC3 sampledBern4C3
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring_nf
    positivity
  · unfold uniformFaceBCoreB2TC3 sampledBern4C3
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring_nf
    positivity

set_option maxHeartbeats 3000000 in
private theorem uniformFaceBCoreB2_at_T_one_nonneg
    (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB2 (m+4) a 1 Y := by
  have hid : uniformFaceBCoreB2 (m+4) a 1 Y =
      cornerBern3 (uniformFaceBCoreB2 (m+4) 0 1 Y)
        (sampledBern3C1 (uniformFaceBCoreB2 (m+4) 0 1 Y)
          (uniformFaceBCoreB2 (m+4) 1 1 Y)
          (uniformFaceBCoreB2 (m+4) 2 1 Y)
          (uniformFaceBCoreB2 (m+4) 3 1 Y))
        (sampledBern3C2 (uniformFaceBCoreB2 (m+4) 0 1 Y)
          (uniformFaceBCoreB2 (m+4) 1 1 Y)
          (uniformFaceBCoreB2 (m+4) 2 1 Y)
          (uniformFaceBCoreB2 (m+4) 3 1 Y))
        (uniformFaceBCoreB2 (m+4) 1 1 Y) a := by
    unfold sampledBern3C1 sampledBern3C2 cornerBern3
    unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring
  rw [hid]
  apply cornerBern3_nonneg <;> try assumption
  · unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring_nf
    positivity
  · unfold sampledBern3C1 uniformFaceBCoreB2
    unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1 uniformFaceBCoreQ2
    ring_nf
    positivity
  · unfold sampledBern3C2 uniformFaceBCoreB2
    unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1 uniformFaceBCoreQ2
    ring_nf
    positivity
  · unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold uniformFaceBCoreQ2
    ring_nf
    positivity

theorem uniformFaceBCoreB2_nonneg_of_T_le_one
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB2 n a T Y := by
  let m := n-4
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  rw [← hnid, uniformFaceBCoreB2_bernstein_T]
  apply cornerBern4_nonneg <;> try assumption
  · have hzero : uniformFaceBCoreB2 (m+4) a 0 Y =
        uniformFaceBCoreB0 (m+4) a 0 Y := by
      unfold uniformFaceBCoreB2 uniformFaceBCoreB0
      unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1 uniformFaceBCoreQ2
      ring
    rw [hzero]
    exact uniformFaceBCoreB0_nonneg (m+4) a 0 Y (by linarith) ha ha1 hY
  · rw [uniformFaceBCoreB2TC1_eq_B1TC1]
    exact uniformFaceBCoreB1TC1_nonneg m a Y hm ha ha1 hY
  · exact uniformFaceBCoreB2TC2_nonneg m a Y hm ha ha1 hY
  · exact uniformFaceBCoreB2TC3_nonneg m a Y hm ha ha1 hY
  · exact uniformFaceBCoreB2_at_T_one_nonneg m a Y hm ha ha1 hY

theorem uniformFaceBCore_nonneg_of_T_le_one
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hY : 0 ≤ Y)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ uniformFaceBCore n a T Y q := by
  apply uniformFaceBCore_nonneg_of_bernstein n a T Y q hq hq1
  · exact uniformFaceBCoreB0_nonneg n a T Y hn ha ha1 hY
  · exact uniformFaceBCoreB1_nonneg_of_T_le_one n a T Y hn ha ha1 hT hT1 hY
  · exact uniformFaceBCoreB2_nonneg_of_T_le_one n a T Y hn ha ha1 hT hT1 hY

/-- The entire compact terminal-scale range is unconditional. -/
theorem uniformSharpFaceB_nonneg_of_T_le_one
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (hY : 0 < Y)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    0 ≤ uniformSharpFaceB n a T Y q := by
  apply uniformSharpFaceB_nonneg_of_core n a T Y q hn ha hT hY hq
  exact uniformFaceBCore_nonneg_of_T_le_one
    n a T Y q hn ha.le ha1 hT.le hT1 hY.le hq.le hq1

/-! ### Normalized coordinates for the large terminal-scale range

For `T = t + 1` and `x = a*Y`, both endpoint gradients become quadratic
in `x`.  More importantly, their difference is independent of `a` and is
linear in `x`.  These identities isolate the polynomial inequality needed
by the remaining large-scale middle-coefficient certificate. -/

private noncomputable def uniformLargeGrad0Poly
    (m a t x : ℝ) : ℝ :=
  x^2*(m^3 + 16*m^2 + 83*m + 140)
    + a*x*(-m^3*t + 3*m^3 - 16*m^2*t + 42*m^2
      - 84*m*t + 174*m - 144*t + 216)
    - a*(2*m^3*t + 30*m^2*t + 144*m*t + 18*m + 216*t + 54)

private noncomputable def uniformLargeGrad1Poly
    (m a t x : ℝ) : ℝ :=
  x^2*(m^3 + 16*m^2 + 83*m + 140)
    + a*x*(2*m^3*t + 6*m^3 + 26*m^2*t + 84*m^2
      + 99*m*t + 357*m + 108*t + 468)
    + a*(-m^3*t^2 - 2*m^3*t + m^3 - 14*m^2*t^2
      - 28*m^2*t + 16*m^2 - m*t^3 - 72*m*t^2 - 159*m*t
      + 38*m - 4*t^3 - 120*t^2 - 282*t - 4)

private noncomputable def uniformLargeGradSlopeCoeff (m : ℝ) : ℝ :=
  3*m^3 + 42*m^2 + 183*m + 252

private noncomputable def uniformLargeGradSlopeThreshold
    (m t : ℝ) : ℝ :=
  m^3*t - m^3 + 14*m^2*t - 16*m^2 + m*t^2 + 71*m*t
    - 56*m + 4*t^2 + 116*t - 50

private noncomputable def uniformLargeGradSlopePoly
    (m t x : ℝ) : ℝ :=
  uniformLargeGradSlopeCoeff m*x - uniformLargeGradSlopeThreshold m t

private noncomputable def uniformLargeGrad0TimeCoeff
    (m x : ℝ) : ℝ :=
  (m+6)^2*(m*x+2*m+4*x+6)

private theorem uniformLargeGrad0_time_shift
    (m a t x : ℝ) :
    uniformLargeGrad0Poly m a t x =
      uniformLargeGrad0Poly m a (1/2) x
        - a*uniformLargeGrad0TimeCoeff m x*(t-1/2) := by
  unfold uniformLargeGrad0Poly uniformLargeGrad0TimeCoeff
  ring

private theorem uniformLargeGrad0TimeCoeff_pos
    (m x : ℝ) (hm : 0 ≤ m) (hx : 0 ≤ x) :
    0 < uniformLargeGrad0TimeCoeff m x := by
  unfold uniformLargeGrad0TimeCoeff
  positivity

private theorem uniformLargeGrad0_time_budget
    (m a t x : ℝ) (_hm : 0 ≤ m) (_ha : 0 < a)
    (_hx : 0 ≤ x) (_ht : 1/2 ≤ t)
    (hgrad : 0 ≤ uniformLargeGrad0Poly m a t x) :
    a*uniformLargeGrad0TimeCoeff m x*(t-1/2) ≤
      uniformLargeGrad0Poly m a (1/2) x := by
  rw [uniformLargeGrad0_time_shift] at hgrad
  linarith

private theorem uniformLargeGrad0_time_shift_eight
    (m a t x : ℝ) :
    uniformLargeGrad0Poly m a t x =
      uniformLargeGrad0Poly m a 8 x
        - a*uniformLargeGrad0TimeCoeff m x*(t-8) := by
  unfold uniformLargeGrad0Poly uniformLargeGrad0TimeCoeff
  ring

private theorem uniformLargeGrad0_time_budget_eight
    (m a t x : ℝ) (_ht : 8 ≤ t)
    (hgrad : 0 ≤ uniformLargeGrad0Poly m a t x) :
    a*uniformLargeGrad0TimeCoeff m x*(t-8) ≤
      uniformLargeGrad0Poly m a 8 x := by
  rw [uniformLargeGrad0_time_shift_eight] at hgrad
  linarith

private theorem uniformGradB0_large_coordinates
    (m a t Y : ℝ) :
    a*uniformGradB0 (m+4) a (t+1) Y =
      uniformLargeGrad0Poly m a t (a*Y) := by
  unfold uniformGradB0 uniformGradB uniformLargeGrad0Poly
  ring

private theorem uniformGradB1_large_coordinates
    (m a t Y : ℝ) :
    a*uniformGradB1 (m+4) a (t+1) Y =
      uniformLargeGrad1Poly m a t (a*Y) := by
  unfold uniformGradB1 uniformGradB uniformLargeGrad1Poly
  ring

private theorem uniformGradB_slope_large_coordinates
    (m a t Y : ℝ) :
    uniformGradB1 (m+4) a (t+1) Y
        - uniformGradB0 (m+4) a (t+1) Y =
      (t+1)*uniformLargeGradSlopePoly m t (a*Y) := by
  unfold uniformGradB0 uniformGradB1 uniformGradB
  unfold uniformLargeGradSlopePoly uniformLargeGradSlopeCoeff
  unfold uniformLargeGradSlopeThreshold
  ring

private theorem uniformLargeGradSlopeCoeff_pos
    (m : ℝ) (hm : 0 ≤ m) :
    0 < uniformLargeGradSlopeCoeff m := by
  unfold uniformLargeGradSlopeCoeff
  positivity

private theorem uniformLargeGradSlope_threshold_lt
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

private noncomputable def uniformLargeMidSample
    (m s t x : ℝ) : ℝ :=
  s^2 * uniformFaceBCoreB1 (m+4) s (t+1) (x/s)

private noncomputable def uniformLargeMidB0 (m t x : ℝ) : ℝ :=
  3*uniformLargeMidSample m 1 t x
    - 3*uniformLargeMidSample m 2 t x
    + uniformLargeMidSample m 3 t x

private noncomputable def uniformLargeMidB1 (m t x : ℝ) : ℝ :=
  (19*uniformLargeMidSample m 1 t x
    - 16*uniformLargeMidSample m 2 t x
    + 5*uniformLargeMidSample m 3 t x) / 8

private noncomputable def uniformLargeMidB2 (m t x : ℝ) : ℝ :=
  (11*uniformLargeMidSample m 1 t x
    - 7*uniformLargeMidSample m 2 t x
    + 2*uniformLargeMidSample m 3 t x) / 6

private noncomputable def uniformLargeMidB3 (m t x : ℝ) : ℝ :=
  (11*uniformLargeMidSample m 1 t x
    - 4*uniformLargeMidSample m 2 t x
    + uniformLargeMidSample m 3 t x) / 8

private noncomputable def uniformLargeMidB4 (m t x : ℝ) : ℝ :=
  uniformLargeMidSample m 1 t x

private noncomputable def uniformLargeMidA1 (m t x : ℝ) : ℝ :=
  (7*uniformLargeMidSample m 1 t x
    - 4*uniformLargeMidSample m 2 t x
    + uniformLargeMidSample m 3 t x) / 4

private noncomputable def sampledBern2C0 (f1 f2 f3 : ℝ) : ℝ :=
  3*f1-3*f2+f3

private noncomputable def sampledBern2C1 (f1 f2 f3 : ℝ) : ℝ :=
  (7*f1-4*f2+f3)/4

private noncomputable def sampledBern2C2 (f1 _f2 _f3 : ℝ) : ℝ := f1

private theorem cornerBern2_nonneg_of_det
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
private theorem uniformLargeMid_bernstein_a
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
private theorem uniformLargeMidB0_nonneg
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidB0 m t x := by
  unfold uniformLargeMidB0 uniformLargeMidSample
  unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
  ring_nf
  positivity

private noncomputable def uniformLargeMidB1Quotient
    (m t x : ℝ) : ℝ :=
  (m+5)*(m+6)*
    (9*m^5*t + 21*m^5 + 222*m^4*t + 510*m^4
      + 6*m^3*t^2 + 2164*m^3*t + 12*m^3*x + 4910*m^3
      + 84*m^2*t^2 + 10358*m^2*t + 168*m^2*x + 23258*m^2
      + 370*m*t^2 + 24155*m*t + 732*m*x + 53629*m
      + 520*t^2 + 21884*t + 1008*x + 47932) /
    (36*(m+3)^2*(m+7)^2)

private noncomputable def uniformLargeMidB1Remainder
    (m t x : ℝ) : ℝ :=
  uniformLargeMidB1 m t x
    - x^2*uniformLargeMidB1Quotient m t x*
      uniformLargeGradSlopePoly m t x

private theorem uniformLargeMidB1Quotient_nonneg
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidB1Quotient m t x := by
  unfold uniformLargeMidB1Quotient
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformLargeMidB1Remainder_nonneg
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
    unfold uniformLargeMidB1 uniformLargeMidSample
    unfold uniformLargeGradSlopePoly uniformLargeGradSlopeCoeff
    unfold uniformLargeGradSlopeThreshold
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    have hm3 : m+3 ≠ 0 := by positivity
    have hm7 : m+7 ≠ 0 := by positivity
    field_simp [hm3, hm7]
    ring_nf
    positivity
  dsimp [remainder] at hrest
  linarith

private theorem uniformLargeMidB1_nonneg_of_threshold
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformLargeMidB2_nonneg_of_threshold
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (_hx : 0 ≤ x)
    (hthreshold : uniformLargeGradSlopeThreshold m t ≤
      uniformLargeGradSlopeCoeff m*x) :
    0 ≤ uniformLargeMidB2 m t x := by
  let u := uniformLargeGradSlopeCoeff m*x
    - uniformLargeGradSlopeThreshold m t
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hP := uniformLargeGradSlopeCoeff_pos m hm
  have hxid : x =
      (uniformLargeGradSlopeThreshold m t + u) /
        uniformLargeGradSlopeCoeff m := by
    dsimp [u]
    field_simp [hP.ne']
    ring
  rw [hxid]
  have hscaled : 0 ≤
      (uniformLargeGradSlopeCoeff m)^4 *
        uniformLargeMidB2 m t
          ((uniformLargeGradSlopeThreshold m t + u) /
            uniformLargeGradSlopeCoeff m) := by
    unfold uniformLargeMidB2 uniformLargeMidSample
    unfold uniformLargeGradSlopeCoeff uniformLargeGradSlopeThreshold
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    field_simp [hP.ne']
    ring_nf
    positivity
  exact (mul_nonneg_iff_of_pos_left (pow_pos hP 4)).mp hscaled

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformLargeMidB3_nonneg_of_threshold
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t)
    (hthreshold : uniformLargeGradSlopeThreshold m t ≤
      uniformLargeGradSlopeCoeff m*x) :
    0 ≤ uniformLargeMidB3 m t x := by
  let u := uniformLargeGradSlopeCoeff m*x
    - uniformLargeGradSlopeThreshold m t
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hP := uniformLargeGradSlopeCoeff_pos m hm
  have hxid : x =
      (uniformLargeGradSlopeThreshold m t + u) /
        uniformLargeGradSlopeCoeff m := by
    dsimp [u]
    field_simp [hP.ne']
    ring
  rw [hxid]
  have hscaled : 0 ≤
      (uniformLargeGradSlopeCoeff m)^4 *
        uniformLargeMidB3 m t
          ((uniformLargeGradSlopeThreshold m t + u) /
            uniformLargeGradSlopeCoeff m) := by
    unfold uniformLargeMidB3 uniformLargeMidSample
    unfold uniformLargeGradSlopeCoeff uniformLargeGradSlopeThreshold
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    field_simp [hP.ne']
    ring_nf
    positivity
  exact (mul_nonneg_iff_of_pos_left (pow_pos hP 4)).mp hscaled

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformLargeMidB4_nonneg_of_threshold
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t)
    (hthreshold : uniformLargeGradSlopeThreshold m t ≤
      uniformLargeGradSlopeCoeff m*x) :
    0 ≤ uniformLargeMidB4 m t x := by
  let u := uniformLargeGradSlopeCoeff m*x
    - uniformLargeGradSlopeThreshold m t
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hP := uniformLargeGradSlopeCoeff_pos m hm
  have hxid : x =
      (uniformLargeGradSlopeThreshold m t + u) /
        uniformLargeGradSlopeCoeff m := by
    dsimp [u]
    field_simp [hP.ne']
    ring
  rw [hxid]
  let A := 3*m^4 + 57*m^3 + 401*m^2 + 1239*m + 1420
  let B := -6*m^5 - 94*m^4 - 430*m^3 + 6*m^2 + 4212*m + 7160
  let C := 24*m^6 + 582*m^5 + 5731*m^4 + 29493*m^3
    + 84265*m^2 + 127749*m + 80908
  have hA : 0 < A := by dsimp [A]; positivity
  have hdisc : 0 ≤ 4*A*C-B^2 := by
    have hid : 4*A*C-B^2 =
        4*(m+3)^2*(m+5)*
          (63*m^7 + 2139*m^6 + 30506*m^5 + 236250*m^4
            + 1069159*m^3 + 2813659*m^2 + 3957920*m + 2268288) := by
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
  let remainder :=
    (uniformLargeGradSlopeCoeff m)^4 *
        uniformLargeMidB4 m t
          ((uniformLargeGradSlopeThreshold m t + u) /
            uniformLargeGradSlopeCoeff m)
      - u^3*(m+4)^2*(m+6)*S/2
  have hrem : 0 ≤ remainder := by
    dsimp [remainder, S, A, B, C]
    unfold uniformLargeMidB4 uniformLargeMidSample
    unfold uniformLargeGradSlopeCoeff uniformLargeGradSlopeThreshold
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    field_simp [hP.ne']
    ring_nf
    positivity
  have hscaled : 0 ≤
      (uniformLargeGradSlopeCoeff m)^4 *
        uniformLargeMidB4 m t
          ((uniformLargeGradSlopeThreshold m t + u) /
            uniformLargeGradSlopeCoeff m) := by
    have hblock : 0 ≤ u^3*(m+4)^2*(m+6)*S/2 := by
      dsimp [S]
      positivity
    dsimp [remainder] at hrem
    linarith
  exact (mul_nonneg_iff_of_pos_left (pow_pos hP 4)).mp hscaled

/-- In the large-scale slope regime, the middle endpoint certificate is
reduced to four normalized Bernstein coefficients.  The zeroth coefficient
is unconditional. -/
private theorem uniformFaceBCoreB1_nonneg_of_large_slope_coefficients
    (m a t Y : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (ha1 : a ≤ 1)
    (ht : 0 ≤ t) (hY : 0 ≤ Y)
    (hslope : uniformGradB0 (m+4) a (t+1) Y <
      uniformGradB1 (m+4) a (t+1) Y)
    :
    0 ≤ uniformFaceBCoreB1 (m+4) a (t+1) Y := by
  have hx : 0 ≤ a*Y := mul_nonneg ha.le hY
  have hthreshold :=
    (uniformLargeGradSlope_threshold_lt m a t Y hm ht hslope).2.le
  have h1 := uniformLargeMidB1_nonneg_of_threshold
    m t (a*Y) hm ht hx hthreshold
  have h2 := uniformLargeMidB2_nonneg_of_threshold
    m t (a*Y) hm ht hx hthreshold
  have h3 := uniformLargeMidB3_nonneg_of_threshold
    m t (a*Y) hm ht hthreshold
  have h4 := uniformLargeMidB4_nonneg_of_threshold
    m t (a*Y) hm ht hthreshold
  have hscaled : 0 ≤ a^2*uniformFaceBCoreB1 (m+4) a (t+1) Y := by
    rw [show Y = (a*Y)/a by field_simp [ha.ne']]
    rw [uniformLargeMid_bernstein_a m a t (a*Y) ha.ne']
    exact cornerBern4_nonneg _ _ _ _ _ a
      (uniformLargeMidB0_nonneg m t (a*Y) hm ht hx) h1 h2 h3 h4 ha.le ha1
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos ha)).mp hscaled

/-- The middle Bernstein coefficient is nonnegative in the large-scale
regime whenever the endpoint gradient increases across the terminal face. -/
theorem uniformFaceBCoreB1_nonneg_of_large_slope
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 1 ≤ T) (hY : 0 ≤ Y)
    (hslope : uniformGradB0 n a T Y < uniformGradB1 n a T Y) :
    0 ≤ uniformFaceBCoreB1 n a T Y := by
  let m := n-4
  let t := T-1
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : t+1 = T := by dsimp [t]; ring
  rw [← hnid, ← hTid] at hslope ⊢
  exact uniformFaceBCoreB1_nonneg_of_large_slope_coefficients
    m a t Y hm ha ha1 ht hY hslope

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformLargeMidB0_nonneg_of_t_le_one
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidB0 m t x := by
  let c0 := sampledBern2C0
    (uniformLargeMidB0 m 1 x) (uniformLargeMidB0 m 2 x)
      (uniformLargeMidB0 m 3 x)
  let c1 := sampledBern2C1
    (uniformLargeMidB0 m 1 x) (uniformLargeMidB0 m 2 x)
      (uniformLargeMidB0 m 3 x)
  let c2 := sampledBern2C2
    (uniformLargeMidB0 m 1 x) (uniformLargeMidB0 m 2 x)
      (uniformLargeMidB0 m 3 x)
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    unfold sampledBern2C0 uniformLargeMidB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc1 : 0 ≤ c1 := by
    dsimp [c1]
    unfold sampledBern2C1 uniformLargeMidB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    unfold sampledBern2C2 uniformLargeMidB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hid : uniformLargeMidB0 m t x = cornerBern2 c0 c1 c2 t := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    ring
  rw [hid]
  exact cornerBern2_nonneg c0 c1 c2 t hc0 hc1 hc2
    (by positivity) (by linarith)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformLargeMidA1_nonneg_of_t_le_one
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidA1 m t x := by
  let c0 := sampledBern2C0
    (uniformLargeMidA1 m 1 x) (uniformLargeMidA1 m 2 x)
      (uniformLargeMidA1 m 3 x)
  let c1 := sampledBern2C1
    (uniformLargeMidA1 m 1 x) (uniformLargeMidA1 m 2 x)
      (uniformLargeMidA1 m 3 x)
  let c2 := sampledBern2C2
    (uniformLargeMidA1 m 1 x) (uniformLargeMidA1 m 2 x)
      (uniformLargeMidA1 m 3 x)
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    unfold sampledBern2C0 uniformLargeMidA1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc1 : 0 ≤ c1 := by
    dsimp [c1]
    unfold sampledBern2C1 uniformLargeMidA1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    unfold sampledBern2C2 uniformLargeMidA1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hid : uniformLargeMidA1 m t x = cornerBern2 c0 c1 c2 t := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidA1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    ring
  rw [hid]
  exact cornerBern2_nonneg c0 c1 c2 t hc0 hc1 hc2
    (by positivity) (by linarith)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformLargeMidB4_nonneg_of_t_le_one
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidB4 m t x := by
  let c0 := sampledBern2C0
    (uniformLargeMidB4 m 1 x) (uniformLargeMidB4 m 2 x)
      (uniformLargeMidB4 m 3 x)
  let c1 := sampledBern2C1
    (uniformLargeMidB4 m 1 x) (uniformLargeMidB4 m 2 x)
      (uniformLargeMidB4 m 3 x)
  let c2 := sampledBern2C2
    (uniformLargeMidB4 m 1 x) (uniformLargeMidB4 m 2 x)
      (uniformLargeMidB4 m 3 x)
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    unfold sampledBern2C0 uniformLargeMidB4 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc1 : 0 ≤ c1 := by
    dsimp [c1]
    unfold sampledBern2C1 uniformLargeMidB4 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    unfold sampledBern2C2 uniformLargeMidB4 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hid : uniformLargeMidB4 m t x = cornerBern2 c0 c1 c2 t := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidB4 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    ring
  rw [hid]
  exact cornerBern2_nonneg c0 c1 c2 t hc0 hc1 hc2
    (by positivity) (by linarith)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceBCoreB1_nonneg_of_t_le_one
    (m a t Y : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (ha1 : a ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1 (m+4) a (t+1) Y := by
  have hx : 0 ≤ a*Y := mul_nonneg ha.le hY
  have haid : a^2*uniformFaceBCoreB1 (m+4) a (t+1) Y =
      cornerBern2 (uniformLargeMidB0 m t (a*Y))
        (uniformLargeMidA1 m t (a*Y))
        (uniformLargeMidB4 m t (a*Y)) a := by
    unfold uniformLargeMidB0 uniformLargeMidA1 uniformLargeMidB4
    unfold uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    field_simp [ha.ne']
    ring
  have hscaled : 0 ≤ a^2*uniformFaceBCoreB1 (m+4) a (t+1) Y := by
    rw [haid]
    exact cornerBern2_nonneg _ _ _ a
      (uniformLargeMidB0_nonneg_of_t_le_one m t (a*Y) hm ht ht1 hx)
      (uniformLargeMidA1_nonneg_of_t_le_one m t (a*Y) hm ht ht1 hx)
      (uniformLargeMidB4_nonneg_of_t_le_one m t (a*Y) hm ht ht1 hx)
      ha.le ha1
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos ha)).mp hscaled

theorem uniformFaceBCoreB1_nonneg_of_T_le_two
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 1 ≤ T) (hT2 : T ≤ 2) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1 n a T Y := by
  let m := n-4
  let t := T-1
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : t+1 = T := by dsimp [t]; ring
  rw [← hnid, ← hTid]
  exact uniformFaceBCoreB1_nonneg_of_t_le_one
    m a t Y hm ha ha1 ht ht1 hY

theorem uniformFaceBCoreB1_nonneg_of_T_le_three_halves
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 1 ≤ T) (hT32 : T ≤ 3/2) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1 n a T Y := by
  exact uniformFaceBCoreB1_nonneg_of_T_le_two
    n a T Y hn ha ha1 hT (by linarith) hY

private noncomputable def uniformLargeMidTimeB0 (m a x : ℝ) : ℝ :=
  3*uniformLargeMidSample m a 8 x
    - 3*uniformLargeMidSample m a 16 x
    + uniformLargeMidSample m a 24 x

private noncomputable def uniformLargeMidTimeB1 (m a x : ℝ) : ℝ :=
  (7*uniformLargeMidSample m a 8 x
    - 4*uniformLargeMidSample m a 16 x
    + uniformLargeMidSample m a 24 x) / 4

private noncomputable def uniformLargeMidTimeB2 (m a x : ℝ) : ℝ :=
  uniformLargeMidSample m a 8 x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformLargeMidTimeB0_nonneg
    (m a x : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidTimeB0 m a x := by
  let c0 := sampledBern2C0 (uniformLargeMidTimeB0 m 1 x)
    (uniformLargeMidTimeB0 m 2 x) (uniformLargeMidTimeB0 m 3 x)
  let c1 := sampledBern2C1 (uniformLargeMidTimeB0 m 1 x)
    (uniformLargeMidTimeB0 m 2 x) (uniformLargeMidTimeB0 m 3 x)
  let c2 := sampledBern2C2 (uniformLargeMidTimeB0 m 1 x)
    (uniformLargeMidTimeB0 m 2 x) (uniformLargeMidTimeB0 m 3 x)
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    unfold sampledBern2C0 uniformLargeMidTimeB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    unfold sampledBern2C2 uniformLargeMidTimeB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hdet : 0 ≤ c0*c2-c1^2 := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidTimeB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hid : uniformLargeMidTimeB0 m a x = cornerBern2 c0 c1 c2 a := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidTimeB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    field_simp [ha.ne']
    ring
  rw [hid]
  exact cornerBern2_nonneg_of_det c0 c1 c2 a hc0 hc2 hdet

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformLargeMidTimeB1_nonneg
    (m a x : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidTimeB1 m a x := by
  let c0 := sampledBern2C0 (uniformLargeMidTimeB1 m 1 x)
    (uniformLargeMidTimeB1 m 2 x) (uniformLargeMidTimeB1 m 3 x)
  let c1 := sampledBern2C1 (uniformLargeMidTimeB1 m 1 x)
    (uniformLargeMidTimeB1 m 2 x) (uniformLargeMidTimeB1 m 3 x)
  let c2 := sampledBern2C2 (uniformLargeMidTimeB1 m 1 x)
    (uniformLargeMidTimeB1 m 2 x) (uniformLargeMidTimeB1 m 3 x)
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    unfold sampledBern2C0 uniformLargeMidTimeB1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    unfold sampledBern2C2 uniformLargeMidTimeB1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hdet : 0 ≤ c0*c2-c1^2 := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidTimeB1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hid : uniformLargeMidTimeB1 m a x = cornerBern2 c0 c1 c2 a := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidTimeB1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    field_simp [ha.ne']
    ring
  rw [hid]
  exact cornerBern2_nonneg_of_det c0 c1 c2 a hc0 hc2 hdet

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformLargeMidTimeB2_nonneg
    (m a x : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidTimeB2 m a x := by
  let c0 := sampledBern2C0 (uniformLargeMidTimeB2 m 1 x)
    (uniformLargeMidTimeB2 m 2 x) (uniformLargeMidTimeB2 m 3 x)
  let c1 := sampledBern2C1 (uniformLargeMidTimeB2 m 1 x)
    (uniformLargeMidTimeB2 m 2 x) (uniformLargeMidTimeB2 m 3 x)
  let c2 := sampledBern2C2 (uniformLargeMidTimeB2 m 1 x)
    (uniformLargeMidTimeB2 m 2 x) (uniformLargeMidTimeB2 m 3 x)
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    unfold sampledBern2C0 uniformLargeMidTimeB2 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    unfold sampledBern2C2 uniformLargeMidTimeB2 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hdet : 0 ≤ c0*c2-c1^2 := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidTimeB2 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hid : uniformLargeMidTimeB2 m a x = cornerBern2 c0 c1 c2 a := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidTimeB2 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    field_simp [ha.ne']
    ring
  rw [hid]
  exact cornerBern2_nonneg_of_det c0 c1 c2 a hc0 hc2 hdet

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceBCoreB1_nonneg_of_t_le_eight
    (m a t Y : ℝ) (hm : 0 ≤ m) (ha : 0 < a)
    (ht : 0 ≤ t) (ht8 : t ≤ 8) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1 (m+4) a (t+1) Y := by
  have hx : 0 ≤ a*Y := mul_nonneg ha.le hY
  have hid : uniformLargeMidSample m a t (a*Y) =
      cornerBern2 (uniformLargeMidTimeB0 m a (a*Y))
        (uniformLargeMidTimeB1 m a (a*Y))
        (uniformLargeMidTimeB2 m a (a*Y)) (t/8) := by
    unfold uniformLargeMidTimeB0 uniformLargeMidTimeB1
    unfold uniformLargeMidTimeB2 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    field_simp [ha.ne']
    ring
  have hscaled : 0 ≤ uniformLargeMidSample m a t (a*Y) := by
    rw [hid]
    exact cornerBern2_nonneg _ _ _ (t/8)
      (uniformLargeMidTimeB0_nonneg m a (a*Y) hm ha hx)
      (uniformLargeMidTimeB1_nonneg m a (a*Y) hm ha hx)
      (uniformLargeMidTimeB2_nonneg m a (a*Y) hm ha hx)
      (by positivity) (by linarith)
  unfold uniformLargeMidSample at hscaled
  rw [show a*Y/a = Y by field_simp [ha.ne']] at hscaled
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos ha)).mp hscaled

theorem uniformFaceBCoreB1_nonneg_of_T_le_nine
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 1 ≤ T) (hT9 : T ≤ 9) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1 n a T Y := by
  let m := n-4
  let t := T-1
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht8 : t ≤ 8 := by dsimp [t]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : t+1 = T := by dsimp [t]; ring
  rw [← hnid, ← hTid]
  exact uniformFaceBCoreB1_nonneg_of_t_le_eight
    m a t Y hm ha ht ht8 hY

private noncomputable def uniformLargeEndSample
    (m s t x : ℝ) : ℝ :=
  s^2 * uniformFaceBCoreB2 (m+4) s (t+1) (x/s)

private noncomputable def uniformLargeEndB0 (m t x : ℝ) : ℝ :=
  3*uniformLargeEndSample m 1 t x
    - 3*uniformLargeEndSample m 2 t x
    + uniformLargeEndSample m 3 t x

private noncomputable def uniformLargeEndB1 (m t x : ℝ) : ℝ :=
  (7*uniformLargeEndSample m 1 t x
    - 4*uniformLargeEndSample m 2 t x
    + uniformLargeEndSample m 3 t x) / 4

private noncomputable def uniformLargeEndB2 (m t x : ℝ) : ℝ :=
  uniformLargeEndSample m 1 t x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem uniformLargeEnd_bernstein_a
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
private theorem uniformLargeEndB0_mono
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
private theorem uniformLargeEndB1_mono
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
private theorem uniformLargeEndB2_mono
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

private theorem uniformLargeEnd_mono
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
private theorem uniformLargeEnd_at_zero_nonneg_of_grad
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

/-! ### Completion of the final large-time middle certificate -/

private noncomputable def uniformLargeGradMaxTime
    (m a x : ℝ) : ℝ :=
  uniformLargeGrad0Poly m a 8 x /
    (a * uniformLargeGrad0TimeCoeff m x)

private noncomputable def uniformLargeMidTimeC0
    (m a x : ℝ) : ℝ :=
  uniformLargeMidSample m a 8 x

private noncomputable def uniformLargeMidTimeC1
    (m a x : ℝ) : ℝ :=
  uniformLargeMidSample m a 8 x
    + uniformLargeGradMaxTime m a x / 4 *
      (uniformLargeMidSample m a 9 x - uniformLargeMidSample m a 7 x)

private noncomputable def uniformLargeMidTimeC2
    (m a x : ℝ) : ℝ :=
  uniformLargeMidSample m a (8 + uniformLargeGradMaxTime m a x) x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem uniformLargeMidTime_endpoint_identity
    (m a x : ℝ) (ha : a ≠ 0)
    (hC : uniformLargeGrad0TimeCoeff m x ≠ 0) :
    2*a^2*uniformLargeGrad0TimeCoeff m x ^ 2 *
        uniformLargeMidTimeC2 m a x =
      uniformRemainingEndpointP m a x := by
  unfold uniformLargeMidTimeC2 uniformLargeGradMaxTime
  unfold uniformLargeGrad0Poly
  unfold uniformRemainingEndpointP
  unfold uniformLargeMidSample uniformFaceBCoreB1
  unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1
  field_simp [ha, hC]
  unfold uniformLargeGrad0TimeCoeff
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem uniformLargeMidTime_middle_identity
    (m a x : ℝ) (ha : a ≠ 0)
    (hC : uniformLargeGrad0TimeCoeff m x ≠ 0) :
    2*a*uniformLargeGrad0TimeCoeff m x *
        uniformLargeMidTimeC1 m a x =
      uniformRemainingTimeMidN m a x := by
  unfold uniformLargeMidTimeC1 uniformLargeGradMaxTime
  unfold uniformLargeGrad0Poly
  unfold uniformRemainingTimeMidN
  unfold uniformLargeMidSample uniformFaceBCoreB1
  unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1
  field_simp [ha, hC]
  unfold uniformLargeGrad0TimeCoeff
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem uniformLargeMidTime_det_identity
    (m a x : ℝ) (ha : a ≠ 0)
    (hC : uniformLargeGrad0TimeCoeff m x ≠ 0) :
    4*a^2*uniformLargeGrad0TimeCoeff m x ^ 2 *
        (uniformLargeMidTimeC0 m a x * uniformLargeMidTimeC2 m a x
          - uniformLargeMidTimeC1 m a x ^ 2) =
      uniformLargeGrad0Poly m a 8 x ^ 2 * (m+6) *
        uniformRemainingTimeDetJ m a x := by
  unfold uniformLargeMidTimeC0 uniformLargeMidTimeC1
  unfold uniformLargeMidTimeC2 uniformLargeGradMaxTime
  unfold uniformLargeGrad0Poly
  unfold uniformRemainingTimeDetJ
  unfold uniformLargeMidSample uniformFaceBCoreB1
  unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1
  field_simp [ha, hC]
  unfold uniformLargeGrad0TimeCoeff
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformLargeMid_time_bernstein
    (m a x w : ℝ) (ha : a ≠ 0)
    (hC : uniformLargeGrad0TimeCoeff m x ≠ 0) :
    uniformLargeMidSample m a
        (8 + w * uniformLargeGradMaxTime m a x) x =
      cornerBern2 (uniformLargeMidTimeC0 m a x)
        (uniformLargeMidTimeC1 m a x) (uniformLargeMidTimeC2 m a x) w := by
  unfold uniformLargeMidTimeC0 uniformLargeMidTimeC1
  unfold uniformLargeMidTimeC2 uniformLargeGradMaxTime
  unfold uniformLargeMidSample uniformFaceBCoreB1
  unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1 cornerBern2
  field_simp [ha, hC]
  unfold uniformLargeGrad0TimeCoeff uniformLargeGrad0Poly
  ring

private theorem uniformLargeMidTimeC2_nonneg
    (m a x : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (ha1 : a ≤ 1)
    (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidTimeC2 m a x := by
  have hP := uniformRemainingEndpointP_nonneg m a x hm ha.le ha1 hx
  have hid := uniformLargeMidTime_endpoint_identity m a x ha.ne'
    (ne_of_gt (uniformLargeGrad0TimeCoeff_pos m x hm hx))
  have hscale : 0 < 2*a^2*uniformLargeGrad0TimeCoeff m x ^ 2 := by
    have hC := uniformLargeGrad0TimeCoeff_pos m x hm hx
    positivity
  exact (mul_nonneg_iff_of_pos_left hscale).mp (by rw [hid]; exact hP)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformLargeMidSample_nonneg_of_t_ge_eight_grad
    (m a t x : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (ha1 : a ≤ 1)
    (ht : 8 ≤ t) (hx : 0 ≤ x)
    (hgrad : 0 ≤ uniformLargeGrad0Poly m a t x) :
    0 ≤ uniformLargeMidSample m a t x := by
  let C := uniformLargeGrad0TimeCoeff m x
  let h := uniformLargeGrad0Poly m a 8 x
  have hC : 0 < C := by
    dsimp [C]
    exact uniformLargeGrad0TimeCoeff_pos m x hm hx
  have hbudget : a*C*(t-8) ≤ h := by
    dsimp [C, h]
    exact uniformLargeGrad0_time_budget_eight m a t x ht hgrad
  have hh : 0 ≤ h := by
    have hleft : 0 ≤ a*C*(t-8) := by positivity
    exact le_trans hleft hbudget
  by_cases hh0 : h = 0
  · have ht8 : t = 8 := by
      have : a*C*(t-8) ≤ 0 := by simpa [hh0] using hbudget
      nlinarith [mul_pos ha hC]
    subst t
    exact uniformLargeMidTimeB2_nonneg m a x hm ha hx
  · have hhpos : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
    let u := uniformLargeGradMaxTime m a x
    have hu : 0 < u := by
      dsimp [u, uniformLargeGradMaxTime, h]
      positivity
    have huid : a*C*u = h := by
      change a*C*(h/(a*C)) = h
      field_simp [mul_ne_zero ha.ne' hC.ne']
    let w := (t-8)/u
    have hw : 0 ≤ w := by dsimp [w]; positivity
    have htu : t-8 ≤ u := by nlinarith [mul_pos ha hC]
    have hw1 : w ≤ 1 := by
      dsimp [w]
      exact (div_le_one hu).mpr htu
    have htid : t = 8+w*u := by
      dsimp [w]
      field_simp [hu.ne']
      ring
    have hc0 : 0 ≤ uniformLargeMidTimeC0 m a x := by
      unfold uniformLargeMidTimeC0
      exact uniformLargeMidTimeB2_nonneg m a x hm ha hx
    have hc2 := uniformLargeMidTimeC2_nonneg m a x hm ha ha1 hx
    have hbern : 0 ≤ cornerBern2 (uniformLargeMidTimeC0 m a x)
        (uniformLargeMidTimeC1 m a x) (uniformLargeMidTimeC2 m a x) w := by
      by_cases hc1 : 0 ≤ uniformLargeMidTimeC1 m a x
      · exact cornerBern2_nonneg _ _ _ w hc0 hc1 hc2 hw (by linarith)
      · have hc1neg : uniformLargeMidTimeC1 m a x < 0 := lt_of_not_ge hc1
        have hmidN : uniformRemainingTimeMidN m a x ≤ 0 := by
          have hid := uniformLargeMidTime_middle_identity m a x ha.ne' hC.ne'
          nlinarith [mul_pos ha hC]
        have hJ := uniformRemainingTimeDetJ_nonneg_of_mid_nonpos
          m a x hm ha.le ha1 hx hmidN
        have hdetScaled : 0 ≤
            4*a^2*C^2 *
              (uniformLargeMidTimeC0 m a x * uniformLargeMidTimeC2 m a x
                - uniformLargeMidTimeC1 m a x ^ 2) := by
          dsimp [C]
          rw [uniformLargeMidTime_det_identity m a x ha.ne' hC.ne']
          positivity
        have hscale : 0 < 4*a^2*C^2 := by positivity
        have hdet : 0 ≤ uniformLargeMidTimeC0 m a x *
            uniformLargeMidTimeC2 m a x - uniformLargeMidTimeC1 m a x ^ 2 :=
          (mul_nonneg_iff_of_pos_left hscale).mp hdetScaled
        exact cornerBern2_nonneg_of_det _ _ _ w hc0 hc2 hdet
    rw [htid, uniformLargeMid_time_bernstein m a x w ha.ne' hC.ne']
    exact hbern

/-- The last large-time middle coefficient follows from the left-gradient
time budget. -/
theorem uniformFaceBCoreB1_nonneg_of_T_ge_nine_grad0
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT9 : 9 ≤ T) (hY : 0 ≤ Y)
    (hgrad : 0 ≤ uniformGradB0 n a T Y) :
    0 ≤ uniformFaceBCoreB1 n a T Y := by
  let m := n-4
  let t := T-1
  let x := a*Y
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have ht : 8 ≤ t := by dsimp [t]; linarith
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : t+1 = T := by dsimp [t]; ring
  have hgradPoly : 0 ≤ uniformLargeGrad0Poly m a t x := by
    rw [← uniformGradB0_large_coordinates m a t Y]
    rw [hnid, hTid]
    positivity
  have hsample := uniformLargeMidSample_nonneg_of_t_ge_eight_grad
    m a t x hm ha ha1 ht hx hgradPoly
  unfold uniformLargeMidSample at hsample
  rw [show x/a = Y by dsimp [x]; field_simp [ha.ne']] at hsample
  rw [hnid, hTid] at hsample
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos ha)).mp hsample

/-- Unconditional terminal-face nonnegativity in the uniform `k = 3`
induction step. -/
theorem uniformSharpFaceB_nonneg
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1) :
    0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformSharpFaceB n a T Y q := by
  apply uniformSharpFaceB_nonneg_of_large_mid0_above_nine
    n a T Y q hn ha ha1 hT hY hq hq1
  intro hT9 hgrad0
  exact uniformFaceBCoreB1_nonneg_of_T_ge_nine_grad0
    n a T Y hn ha ha1 hT9 hY.le hgrad0

end SSP.K3AllStages
