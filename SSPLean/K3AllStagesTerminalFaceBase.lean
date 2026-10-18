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

theorem uniformFaceBCoreB0A2_nonneg
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


end SSP.K3AllStages
