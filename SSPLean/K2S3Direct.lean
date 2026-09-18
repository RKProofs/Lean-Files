import SSPLean.K2ConcreteInitial

/-!
# A direct semialgebraic route to the three-stage `k = 2` inequality

This file develops the missing `n = 3` instance of the renewal polynomial directly.  Once that
instance is available, the already formalized state-return decomposition reduces every
three-state transient model to the unconditional one- and two-state bounds, avoiding any
canonical-representation theorem.
-/

open Finset

set_option autoImplicit false

namespace SSP.K2AllStages

/-- At `n = 3`, the quadratic controlling the `r = 0` corner is nonnegative on
`0 ≤ b ≤ 1`, `0 ≤ y`. -/
theorem corner_quadratic_three_nonneg (y b : ℝ)
    (hy : 0 ≤ y) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ Acoef 3 y * b ^ 2 + Bcoef 3 y * b + Ccoef 3 y := by
  have hAfac : Acoef 3 y = (y + 1) ^ 2 * (3 * y ^ 2 - 6 * y - 5) := by
    unfold Acoef
    ring
  have hB : Bcoef 3 y = 18 - 18 * y ^ 2 := by
    unfold Bcoef
    ring
  have hC : Ccoef 3 y = 3 + 48 * y := by
    unfold Ccoef
    ring
  have hC0 : 0 ≤ Ccoef 3 y := by rw [hC]; positivity
  have hEnd : 0 ≤ Acoef 3 y + Bcoef 3 y + Ccoef 3 y :=
    endpoint_sum_nonneg 3 y (by norm_num) hy
  by_cases hA : Acoef 3 y ≤ 0
  · have hid : Acoef 3 y * b ^ 2 + Bcoef 3 y * b + Ccoef 3 y =
        (1 - b) * Ccoef 3 y + b * (Acoef 3 y + Bcoef 3 y + Ccoef 3 y) +
          (-Acoef 3 y) * b * (1 - b) := by ring
    rw [hid]
    have hbcomp : 0 ≤ 1 - b := sub_nonneg.mpr hb1
    have hfirst : 0 ≤ (1 - b) * Ccoef 3 y := mul_nonneg hbcomp hC0
    have hsecond : 0 ≤ b * (Acoef 3 y + Bcoef 3 y + Ccoef 3 y) :=
      mul_nonneg hb0 hEnd
    have hthird : 0 ≤ (-Acoef 3 y) * b * (1 - b) :=
      mul_nonneg (mul_nonneg (neg_nonneg.mpr hA) hb0) hbcomp
    linarith
  · have hApos : 0 < Acoef 3 y := lt_of_not_ge hA
    by_cases hy3 : y ≤ 3
    · have hquadpos : 0 < 3 * y ^ 2 - 6 * y - 5 := by
        have hsquare : 0 < (y + 1) ^ 2 := sq_pos_of_pos (by linarith)
        rw [hAfac] at hApos
        rcases (mul_pos_iff.mp hApos) with hpp | hnn
        · exact hpp.2
        · exact False.elim ((not_lt_of_ge hsquare.le) hnn.1)
      have hy2 : 2 < y := by
        by_contra hnot
        have hle : y ≤ 2 := le_of_not_gt hnot
        have hprod : 0 ≤ y * (2 - y) := mul_nonneg hy (sub_nonneg.mpr hle)
        nlinarith
      let t := y - 2
      have ht0 : 0 ≤ t := by dsimp [t]; linarith
      have ht1 : t ≤ 1 := by dsimp [t]; linarith
      have ht2 : t ^ 2 ≤ t := by
        have := mul_nonneg ht0 (sub_nonneg.mpr ht1)
        nlinarith
      have ht3 : t ^ 3 ≤ t ^ 2 := by
        have := mul_le_mul_of_nonneg_left ht1 (sq_nonneg t)
        nlinarith
      have hpoly : 3 * y ^ 3 - 3 * y ^ 2 - 20 * y + 4 ≤ 0 := by
        have hid : 3 * y ^ 3 - 3 * y ^ 2 - 20 * y + 4 =
            3 * t ^ 3 + 15 * t ^ 2 + 4 * t - 24 := by
          dsimp [t]
          ring
        rw [hid]
        nlinarith
      have hder : 2 * Acoef 3 y + Bcoef 3 y ≤ 0 := by
        have hid : 2 * Acoef 3 y + Bcoef 3 y =
            2 * (y + 1) * (3 * y ^ 3 - 3 * y ^ 2 - 20 * y + 4) := by
          unfold Acoef Bcoef
          ring
        rw [hid]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hpoly
      have hlin : Acoef 3 y * (b + 1) + Bcoef 3 y ≤ 0 := by
        have hAb : Acoef 3 y * (b + 1) ≤ Acoef 3 y * 2 := by
          exact mul_le_mul_of_nonneg_left (by linarith) hApos.le
        linarith
      have hid : Acoef 3 y * b ^ 2 + Bcoef 3 y * b + Ccoef 3 y =
          (Acoef 3 y + Bcoef 3 y + Ccoef 3 y) +
            (b - 1) * (Acoef 3 y * (b + 1) + Bcoef 3 y) := by ring
      rw [hid]
      exact add_nonneg hEnd (mul_nonneg_of_nonpos_of_nonpos (by linarith) hlin)
    · have hy3' : 3 ≤ y := le_of_not_ge hy3
      have hquad : 0 < 3 * y ^ 2 - 6 * y - 5 := by
        have hprod : 0 ≤ (y - 3) * (3 * y + 3) := by positivity
        nlinarith
      have hcubic : 0 < 6 * y ^ 3 - 15 * y ^ 2 - 4 * y - 4 := by
        let t := y - 3
        have ht : 0 ≤ t := by dsimp [t]; linarith
        have hid : 6 * y ^ 3 - 15 * y ^ 2 - 4 * y - 4 =
            6 * t ^ 3 + 39 * t ^ 2 + 68 * t + 11 := by
          dsimp [t]
          ring
        rw [hid]
        positivity
      have hdisc : Bcoef 3 y ^ 2 - 4 * Acoef 3 y * Ccoef 3 y < 0 := by
        have hid : Bcoef 3 y ^ 2 - 4 * Acoef 3 y * Ccoef 3 y =
            -96 * (y + 1) ^ 2 * (6 * y ^ 3 - 15 * y ^ 2 - 4 * y - 4) := by
          unfold Acoef Bcoef Ccoef
          ring
        rw [hid]
        have hsquare : 0 < (y + 1) ^ 2 := sq_pos_of_pos (by linarith)
        have hleft : -96 * (y + 1) ^ 2 < 0 :=
          mul_neg_of_neg_of_pos (by norm_num) hsquare
        exact mul_neg_of_neg_of_pos hleft hcubic
      have hsquare := sq_nonneg (2 * Acoef 3 y * b + Bcoef 3 y)
      have hid : 4 * Acoef 3 y *
          (Acoef 3 y * b ^ 2 + Bcoef 3 y * b + Ccoef 3 y) =
          (2 * Acoef 3 y * b + Bcoef 3 y) ^ 2 -
            (Bcoef 3 y ^ 2 - 4 * Acoef 3 y * Ccoef 3 y) := by ring
      have hprod : 0 < 4 * Acoef 3 y *
          (Acoef 3 y * b ^ 2 + Bcoef 3 y * b + Ccoef 3 y) := by
        rw [hid]
        linarith
      have hfourA : 0 < 4 * Acoef 3 y := mul_pos (by norm_num) hApos
      rcases (mul_pos_iff.mp hprod) with hpp | hnn
      · exact hpp.2.le
      · exact False.elim ((not_lt_of_ge hfourA.le) hnn.1)

/-- The normalized lower-corner polynomial is nonnegative at `n = 3`. -/
theorem corner_three_nonneg (r b z : ℝ)
    (hr0 : 0 ≤ r) (hrb : r ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z) :
    0 ≤ Phi 3 r b z := by
  have hb0 : 0 ≤ b := le_trans hr0 hrb
  rcases eq_or_lt_of_le hb0 with hbzero | hbpos
  · have hrzero : r = 0 := by linarith
    rw [← hbzero, hrzero]
    norm_num [Phi]
    positivity
  · let y := z / b
    have hy : 0 ≤ y := by dsimp [y]; positivity
    have hzby : b * y = z := by
      dsimp [y]
      field_simp [ne_of_gt hbpos]
    have hzero : 0 ≤ Phi 3 0 b z := by
      rw [← hzby, phi_at_zero_scaled]
      exact mul_nonneg (sq_nonneg b) (corner_quadratic_three_nonneg y b hy hb0 hb1)
    have hend : 0 ≤ Phi 3 b b z := by
      rw [phi_at_b]
      positivity
    have hchord := phi_chord 3 r b z
    have hrest : 0 ≤
        (b - r) * Phi 3 0 b z + r * Phi 3 b b z +
          (3 : ℝ) ^ 2 * (3 + 2) * b * (1 - b) ^ 2 * r * (b - r) := by
      positivity
    have hbPhi : 0 ≤ b * Phi 3 r b z := by linarith
    apply nonneg_of_mul_nonneg_left
    · simpa [mul_comm] using hbPhi
    · exact hbpos

theorem corner_three_pos_interior (r b z : ℝ)
    (hr0 : 0 < r) (hrb : r < b) (hb1 : b < 1) (hz : 0 ≤ z) :
    0 < Phi 3 r b z := by
  have hzero : 0 ≤ Phi 3 0 b z :=
    corner_three_nonneg 0 b z (by norm_num) (by linarith) hb1.le hz
  have hbval : 0 ≤ Phi 3 b b z :=
    corner_three_nonneg b b z (by linarith) le_rfl hb1.le hz
  have hch := phi_chord 3 r b z
  have hb0 : 0 < b := lt_trans hr0 hrb
  have hcorr : 0 < (3 : ℝ)^2*(3+2)*b*(1-b)^2*r*(b-r) := by positivity
  have hleft : 0 ≤ (b-r)*Phi 3 0 b z := mul_nonneg (by linarith) hzero
  have hright : 0 ≤ r*Phi 3 b b z := mul_nonneg hr0.le hbval
  have hbPhi : 0 < b*Phi 3 r b z := by nlinarith
  exact pos_of_mul_pos_right hbPhi hb0.le

/-! ## The alpha face and the interior stationary point -/

/-- The polynomial left after factoring the alpha-face discriminant at `n = 3`. -/
noncomputable def RAlphaThree (r b z : ℝ) : ℝ :=
  -4*b^4 + 36*b^3*r - 8*b^3*z + 72*b^2*r*z - 19*b^2*z^2
    - 45*b*r*z^2 - 9*b*z^3 + 9*r*z^3 + 6*z^4

theorem alpha_face_discriminant_three (r b z : ℝ) (hr : r ≠ 1) :
    2*hAlphaAlpha 3 r b z*(Phi 3 r b z/4) - (gAlpha 3 r b z)^2
      = 8*(b-r)*(1-b)^2*(b+z)*RAlphaThree r b z /
          (3*(1-r)^4) := by
  unfold hAlphaAlpha gAlpha SAlpha Phi RAlphaThree
  field_simp [hr]
  ring

/-- On the feasible routing region, a negative alpha gradient forces the specialized
alpha-face discriminant polynomial to be positive. -/
theorem rAlphaThree_pos_of_stationary (r b z : ℝ)
    (hr0 : 0 ≤ r) (hrb : r ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z)
    (hS : SAlpha 3 r b z < 0) :
    0 < RAlphaThree r b z := by
  have hb0 : 0 ≤ b := le_trans hr0 hrb
  have hz16 : (16 : ℝ) / 3 < z := by
    by_contra hnot
    have hzle : z ≤ (16 : ℝ) / 3 := le_of_not_gt hnot
    have hzterm : 0 ≤ z * (32 - 6*z) := mul_nonneg hz (by linarith)
    have hroute : 0 ≤ 30*r*(1-b) + 6*b^2 + 2*b := by positivity
    norm_num [SAlpha] at hS
    nlinarith
  have hz3 : 3 < z := by linarith
  have hb2 : b^2 ≤ 1 := by nlinarith [sq_nonneg (1-b), sq_nonneg b]
  have hb3 : b^3 ≤ 1 := by
    have := mul_le_mul hb2 hb1 hb0 (by norm_num : (0 : ℝ) ≤ 1)
    simpa [pow_succ] using this
  have hzb : 0 < z - 5*b := by linarith
  have hcoef : 0 < 36*b^3 + 72*b^2*z - 45*b*z^2 + 9*z^3 := by
    have hid : 36*b^3 + 72*b^2*z - 45*b*z^2 + 9*z^3 =
        36*b^3 + 72*b^2*z + 9*z^2*(z-5*b) := by ring
    rw [hid]
    have hlast : 0 < 9*z^2*(z-5*b) := by positivity
    positivity
  have hcubic : 0 < 6*z^3 - 15*z^2 - 4*z - 4 := by
    let t := z - 3
    have ht : 0 < t := by dsimp [t]; linarith
    have hid : 6*z^3 - 15*z^2 - 4*z - 4 =
        6*t^3 + 39*t^2 + 68*t + 11 := by
      dsimp [t]
      ring
    rw [hid]
    positivity
  have htail : 0 < 6*z^3 - 15*b*z^2 - 4*b^2*z - 4*b^3 := by
    have hid : 6*z^3 - 15*b*z^2 - 4*b^2*z - 4*b^3 =
        (6*z^3 - 15*z^2 - 4*z - 4) +
          15*(1-b)*z^2 + 4*(1-b^2)*z + 4*(1-b^3) := by ring
    rw [hid]
    have h1 : 0 ≤ 15*(1-b)*z^2 := by positivity
    have h2 : 0 ≤ 4*(1-b^2)*z := by positivity
    have h3 : 0 ≤ 4*(1-b^3) := by positivity
    linarith
  have hbase : 0 < -4*b^4 - 8*b^3*z - 19*b^2*z^2 - 9*b*z^3 + 6*z^4 := by
    have hid : -4*b^4 - 8*b^3*z - 19*b^2*z^2 - 9*b*z^3 + 6*z^4 =
        (b+z)*(6*z^3 - 15*b*z^2 - 4*b^2*z - 4*b^3) := by ring
    rw [hid]
    positivity
  have hid : RAlphaThree r b z =
      (-4*b^4 - 8*b^3*z - 19*b^2*z^2 - 9*b*z^3 + 6*z^4) +
        r*(36*b^3 + 72*b^2*z - 45*b*z^2 + 9*z^3) := by
    unfold RAlphaThree
    ring
  rw [hid]
  exact add_pos_of_pos_of_nonneg hbase (mul_nonneg hr0 hcoef.le)

theorem interiorR_three_pos (x u v p q : ℝ)
    (hx : 0 < x) (hu : 0 < u) (hv : 0 < v)
    (hp : 0 < p) (hq : 0 < q) :
    0 < InteriorR 3 x u v p q := by
  have hR0 : 0 < InteriorR0 3 x u := by
    norm_num [InteriorR0]
    positivity
  have hR1 : 0 < InteriorR1 3 x u v := by
    norm_num [InteriorR1]
    positivity
  have hR2 : 0 < InteriorR2 3 x u v := by
    norm_num [InteriorR2]
    positivity
  unfold InteriorR
  positivity

/-! ## The beta face -/

theorem fBeta_three_threshold (y : ℝ) (hy : 0 ≤ y)
    (hf : FBeta 3 y ≤ 0) :
    11*y ≤ 16 := by
  have hid := fBeta_threshold_identity 3 y
  norm_num at hid
  have hcoef : 0 < 208 + 22*y := by positivity
  by_contra hnot
  have hgap : 0 < 11*y - 16 := by linarith
  have hrhs : 0 < 1392 + (11*y-16)*(208+22*y) := by positivity
  have hlhs : 121*FBeta 3 y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num) hf
  linarith

theorem fBeta_three_threshold_strict (y : ℝ) (hy : 0 ≤ y)
    (hf : FBeta 3 y < 0) :
    11*y < 16 := by
  have hid := fBeta_threshold_identity 3 y
  norm_num at hid
  have hcoef : 0 < 208+22*y := by positivity
  by_contra hnot
  have hgap : 0 ≤ 11*y-16 := by linarith
  have hrhs : 0 < 1392+(11*y-16)*(208+22*y) := by
    have hsecond : 0 ≤ (11*y-16)*(208+22*y) := mul_nonneg hgap hcoef.le
    linarith
  have hlhs : 121*FBeta 3 y < 0 := mul_neg_of_pos_of_neg (by norm_num) hf
  linarith

theorem pBeta_three_pos (y : ℝ) (hy : 0 ≤ y) : 0 < PBeta 3 y := by
  have hid : PBeta 3 y = 16*y^3 + (360*y^2 - 192*y + 304) := by
    unfold PBeta
    ring
  have hquad : 0 < 360*y^2 - 192*y + 304 := by
    have hs := sq_nonneg (60*y-16)
    nlinarith
  rw [hid]
  have hy3 : 0 ≤ y^3 := by positivity
  linarith

theorem dBeta_three_pos (y : ℝ) (hy : 0 ≤ y) : 0 < DBeta 3 y := by
  norm_num [DBeta]
  positivity

theorem tBeta_three_le_zero (y b : ℝ)
    (hy : 0 ≤ y) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hfeas : b*DBeta 3 y ≤ 30) :
    TBeta 3 b (b*y) ≤ 0 := by
  let den := DBeta 3 y
  let a : ℝ := 80 + 248*y
  have hden : 0 < den := by dsimp [den]; exact dBeta_three_pos y hy
  have ha : 0 < a := by dsimp [a]; positivity
  have hT0 : TBeta 3 0 0 < 0 := by norm_num [TBeta]
  rcases le_total den 30 with hdc | hcd
  · have hf : FBeta 3 y ≤ 0 := by
      rw [← dBeta_sub_cap]
      norm_num
      simpa [den] using hdc
    have hthreshold := fBeta_three_threshold y hy hf
    have hT1 : TBeta 3 1 y ≤ 0 := by
      rw [tBeta_one_scaled]
      norm_num
      linarith
    have hch := tBeta_chord_scaled 3 y b 1
    norm_num at hch
    have h₁ : (1-b)*TBeta 3 0 0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hT0.le
    have h₂ : b*TBeta 3 1 y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb0 hT1
    have h₃ : 0 ≤ a*b*(1-b) := by positivity
    dsimp [a] at h₃
    nlinarith
  · let t := 30/den
    have ht : 0 < t := by dsimp [t]; positivity
    have ht1 : t ≤ 1 := by
      dsimp [t]
      exact (div_le_one hden).mpr hcd
    have hbt : b ≤ t := by
      dsimp [t, den] at *
      exact (le_div_iff₀ hden).mpr hfeas
    have hPt : 0 < PBeta 3 y := pBeta_three_pos y hy
    have hTt : TBeta 3 t (t*y) < 0 := by
      have hid := tBeta_moving_value 3 y (ne_of_gt hden)
      have hy16 : 0 < y+16 := by linarith
      have hpos : 0 < 12*(y+16)*PBeta 3 y := by positivity
      have hrhs : -12*(y+16)*PBeta 3 y < 0 := by linarith
      have hden2 : 0 < (DBeta 3 y)^2 := sq_pos_of_pos hden
      dsimp [t, den] at *
      norm_num at hid
      nlinarith
    have hch := tBeta_chord_scaled 3 y b t
    norm_num at hch
    have h₁ : (t-b)*TBeta 3 0 0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hT0.le
    have h₂ : b*TBeta 3 t (t*y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb0 hTt.le
    have h₃ : 0 ≤ a*b*t*(t-b) := by positivity
    dsimp [a] at h₃
    have htT : t*TBeta 3 b (b*y) ≤ 0 := by nlinarith
    exact nonpos_of_mul_nonpos_left (by simpa [mul_comm] using htT) ht

theorem kBeta_three_nonneg (r b z : ℝ)
    (hr0 : 0 ≤ r) (hrb : r ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z)
    (hS : SBeta 3 r b z ≤ 0) :
    0 ≤ KBeta 3 r b z := by
  have hb0 : 0 ≤ b := le_trans hr0 hrb
  by_cases hbzero : b = 0
  · subst b
    have hr : r = 0 := by linarith
    subst r
    have hz0 : z = 0 := by
      norm_num [SBeta] at hS
      nlinarith [sq_nonneg z]
    subst z
    norm_num [KBeta, MBeta, SBeta, Phi]
  · have hb : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hbzero)
    let y := z/b
    have hy : 0 ≤ y := div_nonneg hz hb.le
    have hzy : z = b*y := by
      dsimp [y]
      field_simp
    have hS0le : SBeta 3 0 b z ≤ 0 := by
      have haff := sBeta_affine 3 0 r b z
      have hslope : 0 ≤ 30*(1-b)*r := by positivity
      norm_num at haff
      nlinarith
    have hfeas : b*DBeta 3 y ≤ 30 := by
      have hs0 := sBeta_at_zero_scaled 3 b y
      rw [← hzy] at hs0
      norm_num at hs0
      nlinarith
    have hT : TBeta 3 b z ≤ 0 := by
      rw [hzy]
      exact tBeta_three_le_zero y b hy hb.le hb1 hfeas
    have hK0 : 0 ≤ KBeta 3 0 b z := by
      rw [kBeta_at_zero]
      norm_num
      have hpre : 0 ≤ 4*b*(b+z)^2 := by positivity
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hpre hT]
    rcases le_total (SBeta 3 b b z) 0 with hSb | hSb
    · have hf : FBeta 3 y ≤ 0 := by
        have hsbb := sBeta_at_b_scaled 3 b y
        rw [← hzy] at hsbb
        have hb2 : 0 < b^2 := sq_pos_of_pos hb
        rw [hsbb] at hSb
        change b^2 * FBeta 3 y ≤ 0 at hSb
        by_contra hnot
        have hpos : 0 < FBeta 3 y := lt_of_not_ge hnot
        nlinarith [mul_pos hb2 hpos]
      have hthreshold := fBeta_three_threshold y hy hf
      have hKb : 0 ≤ KBeta 3 b b z := by
        rw [kBeta_at_b]
        norm_num
        have hfac : 0 ≤ 16*b-11*z := by
          rw [hzy]
          have : 0 ≤ 16-11*y := by linarith
          nlinarith [mul_nonneg hb.le this]
        positivity
      have hch := kBeta_chord 3 r b b z
      norm_num at hch
      have hcorr : 0 ≤ 960*(b+z)*(1-b)^2*b*r*(b-r) := by positivity
      have hleft : 0 ≤ (b-r)*KBeta 3 0 b z :=
        mul_nonneg (sub_nonneg.mpr hrb) hK0
      have hright : 0 ≤ r*KBeta 3 b b z := mul_nonneg hr0 hKb
      have hbK : 0 ≤ b*KBeta 3 r b z := by nlinarith
      exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hbK) hb
    · rcases eq_or_lt_of_le hS with hSr | hSr
      · have hphi := corner_three_nonneg r b z hr0 hrb hb1 hz
        have hM : 0 ≤ MBeta 3 b z := by unfold MBeta; positivity
        unfold KBeta
        rw [hSr]
        norm_num
        positivity
      · have hbone : b < 1 := by
          by_contra hnot
          have hbeq : b = 1 := by linarith
          subst b
          have haff := sBeta_affine 3 r 1 1 z
          norm_num at haff
          linarith
        let c : ℝ := 30*(1-b)
        have hc : 0 < c := by dsimp [c]; positivity
        let t := r + (-SBeta 3 r b z)/c
        have htr : r < t := by
          dsimp [t]
          have : 0 < (-SBeta 3 r b z)/c := div_pos (by linarith) hc
          linarith
        have hSt : SBeta 3 t b z = 0 := by
          have haff := sBeta_affine 3 r t b z
          norm_num at haff
          have hct : c*(t-r) = -SBeta 3 r b z := by
            dsimp [t]
            field_simp [ne_of_gt hc]
            ring
          change SBeta 3 t b z = SBeta 3 r b z + c*(t-r) at haff
          linarith
        have htb : t ≤ b := by
          have haff := sBeta_affine 3 t b b z
          norm_num at haff
          rw [hSt] at haff
          have hspos : 0 < 30*(1-b) := by positivity
          by_contra hnot
          have hprod : 30*(1-b)*(b-t) < 0 :=
            mul_neg_of_pos_of_neg hspos (by linarith)
          linarith
        have ht0 : 0 < t := lt_of_le_of_lt hr0 htr
        have hphi := corner_three_nonneg t b z ht0.le htb hb1 hz
        have hM : 0 ≤ MBeta 3 b z := by unfold MBeta; positivity
        have hKt : 0 ≤ KBeta 3 t b z := by
          unfold KBeta
          rw [hSt]
          norm_num
          positivity
        have hch := kBeta_chord 3 r t b z
        norm_num at hch
        have hcorr : 0 ≤ 960*(b+z)*(1-b)^2*t*r*(t-r) := by positivity
        have hleft : 0 ≤ (t-r)*KBeta 3 0 b z := mul_nonneg (by linarith) hK0
        have hright : 0 ≤ r*KBeta 3 t b z := mul_nonneg hr0 hKt
        have htK : 0 ≤ t*KBeta 3 r b z := by nlinarith
        exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using htK) ht0

theorem kBeta_three_pos_interior (r b z : ℝ)
    (hr0 : 0 < r) (hrb : r < b) (hb1 : b < 1) (hz : 0 < z)
    (hS : SBeta 3 r b z < 0) :
    0 < KBeta 3 r b z := by
  have hb0 : 0 < b := lt_trans hr0 hrb
  have hS0 : SBeta 3 0 b z < 0 := by
    have haff := sBeta_affine 3 0 r b z
    norm_num at haff
    have hslope : 0 < 30*(1-b)*r := by positivity
    nlinarith
  have hK0 : 0 ≤ KBeta 3 0 b z :=
    kBeta_three_nonneg 0 b z (by norm_num) hb0.le hb1.le hz.le hS0.le
  rcases le_total (SBeta 3 b b z) 0 with hSb | hSb
  · have hKb : 0 ≤ KBeta 3 b b z :=
      kBeta_three_nonneg b b z hb0.le le_rfl hb1.le hz.le hSb
    have hch := kBeta_chord 3 r b b z
    norm_num at hch
    have hcorr : 0 < 960*(b+z)*(1-b)^2*b*r*(b-r) := by positivity
    have hleft : 0 ≤ (b-r)*KBeta 3 0 b z := mul_nonneg (by linarith) hK0
    have hright : 0 ≤ r*KBeta 3 b b z := mul_nonneg hr0.le hKb
    have hbK : 0 < b*KBeta 3 r b z := by nlinarith
    exact pos_of_mul_pos_right hbK hb0.le
  · let c : ℝ := 30*(1-b)
    have hc : 0 < c := by dsimp [c]; positivity
    let t := r+(-SBeta 3 r b z)/c
    have htr : r < t := by
      dsimp [t]
      have : 0 < (-SBeta 3 r b z)/c := div_pos (by linarith) hc
      linarith
    have hSt : SBeta 3 t b z = 0 := by
      have haff := sBeta_affine 3 r t b z
      norm_num at haff
      have hct : c*(t-r) = -SBeta 3 r b z := by
        dsimp [t]
        field_simp [ne_of_gt hc]
        ring
      change SBeta 3 t b z = SBeta 3 r b z+c*(t-r) at haff
      linarith
    have htb : t ≤ b := by
      have haff := sBeta_affine 3 t b b z
      norm_num at haff
      rw [hSt] at haff
      have hslope : 0 < 30*(1-b) := by positivity
      by_contra hnot
      have hprod : 30*(1-b)*(b-t) < 0 :=
        mul_neg_of_pos_of_neg hslope (by linarith)
      linarith
    have ht0 : 0 < t := lt_trans hr0 htr
    have hKt : 0 ≤ KBeta 3 t b z :=
      kBeta_three_nonneg t b z ht0.le htb hb1.le hz.le (le_of_eq hSt)
    have hch := kBeta_chord 3 r t b z
    norm_num at hch
    have hcorr : 0 < 960*(b+z)*(1-b)^2*t*r*(t-r) := by positivity
    have hleft : 0 ≤ (t-r)*KBeta 3 0 b z := mul_nonneg (by linarith) hK0
    have hright : 0 ≤ r*KBeta 3 t b z := mul_nonneg hr0.le hKt
    have htK : 0 < t*KBeta 3 r b z := by nlinarith
    exact pos_of_mul_pos_right htK ht0.le

/-! ## Assembly -/

theorem renewalQuad_three_nonneg (r b z da db : ℝ)
    (hr0 : 0 < r) (hrb : r < b) (hb1 : b < 1) (hz : 0 < z)
    (hda : 0 ≤ da) (hdb : 0 ≤ db) :
    0 ≤ renewalQuad 3 r b z da db := by
  have hr1 : r < 1 := lt_trans hrb hb1
  have hb0 : 0 < b := lt_trans hr0 hrb
  have hcorner : 0 ≤ Phi 3 r b z :=
    corner_three_nonneg r b z hr0.le hrb.le hb1.le hz.le
  have hq0 : 0 ≤ Phi 3 r b z / 4 := by positivity
  have hhbb : 0 < hBetaBeta 3 b z := by
    unfold hBetaBeta
    positivity
  have hhaa : 0 < hAlphaAlpha 3 r b z := by
    unfold hAlphaAlpha
    positivity
  have hdet : 0 < hAlphaAlpha 3 r b z*hBetaBeta 3 b z
      -(hAlphaBeta 3 r b z)^2 := by
    rw [hessian_det_factor 3 r b z (by norm_num) (ne_of_gt hz) (ne_of_lt hr1)]
    positivity
  have hR : 0 < interiorRNorm 3 r b z := by
    unfold interiorRNorm
    apply interiorR_three_pos r (1-r) (z*(1-r)/(1-b))
      ((b-r)/(1-r)) ((1-b)/(1-r))
    all_goals positivity
  have hstar : hAlphaBeta 3 r b z*gBeta 3 r b z
      -hBetaBeta 3 b z*gAlpha 3 r b z < 0 := by
    rw [interior_stationary_factor 3 r b z (by norm_num) (by norm_num)
      (ne_of_gt hz) (ne_of_lt hr1) (ne_of_lt hb1)]
    have hnum : 0 < 2*(b-r)*(1-b)*(b+z)*(3+1: ℝ) := by positivity
    have hden : 0 < 3*z*(3-1)*(1-r)^2 := by positivity
    have hnumneg : -2*(b-r)*(1-b)*(b+z)*(3+1: ℝ) < 0 := by
      have heq : -2*(b-r)*(1-b)*(b+z)*(3+1: ℝ) =
          -(2*(b-r)*(1-b)*(b+z)*(3+1)) := by ring
      rw [heq]
      exact neg_neg_of_pos hnum
    have hpref : -2*(b-r)*(1-b)*(b+z)*(3+1) /
        (3*z*(3-1)*(1-r)^2) < 0 :=
      div_neg_of_neg_of_pos hnumneg hden
    exact mul_neg_of_neg_of_pos hpref hR
  have hfaceBeta : ∀ t, 0 ≤ t →
      0 ≤ quad2 (Phi 3 r b z/4)
        (gAlpha 3 r b z) (gBeta 3 r b z)
        (hAlphaAlpha 3 r b z) (hAlphaBeta 3 r b z)
        (hBetaBeta 3 b z) 0 t := by
    intro t ht
    unfold quad2
    norm_num
    apply quad1_nonneg (Phi 3 r b z/4) (gBeta 3 r b z)
      (hBetaBeta 3 b z) t hq0 hhbb ht
    intro hg
    have hS : SBeta 3 r b z ≤ 0 := by
      unfold gBeta at hg
      norm_num at hg
      linarith
    have hK := kBeta_three_nonneg r b z hr0.le hrb.le hb1.le hz.le hS
    have hid := beta_face_discriminant 3 r b z (by norm_num) (by norm_num)
      (ne_of_gt hz)
    norm_num at hid
    rw [hid]
    positivity
  have hfaceAlpha : ∀ t, 0 ≤ t →
      0 ≤ quad2 (Phi 3 r b z/4)
        (gAlpha 3 r b z) (gBeta 3 r b z)
        (hAlphaAlpha 3 r b z) (hAlphaBeta 3 r b z)
        (hBetaBeta 3 b z) t 0 := by
    intro t ht
    unfold quad2
    norm_num
    apply quad1_nonneg (Phi 3 r b z/4) (gAlpha 3 r b z)
      (hAlphaAlpha 3 r b z) t hq0 hhaa ht
    intro hg
    have hpre : 0 < (b-r)*(1-b)/((1-r)^2*(3-1: ℝ)) := by positivity
    have hS : SAlpha 3 r b z < 0 := by
      have hgeq : gAlpha 3 r b z =
          (b-r)*(1-b)/((1-r)^2*(3-1: ℝ)) * SAlpha 3 r b z := rfl
      rw [hgeq] at hg
      by_contra hnot
      have hs0 : 0 ≤ SAlpha 3 r b z := le_of_not_gt hnot
      exact (not_lt_of_ge (mul_nonneg hpre.le hs0)) hg
    have hRA := rAlphaThree_pos_of_stationary r b z hr0.le hrb.le hb1.le hz.le hS
    rw [alpha_face_discriminant_three r b z (ne_of_lt hr1)]
    positivity
  unfold renewalQuad
  norm_num
  exact quad2_nonneg_on_quadrant
    (Phi 3 r b z/4) (gAlpha 3 r b z) (gBeta 3 r b z)
    (hAlphaAlpha 3 r b z) (hAlphaBeta 3 r b z) (hBetaBeta 3 b z)
    hhbb hdet hstar hfaceBeta hfaceAlpha da db hda hdb

theorem renewalQuad_three_pos (r b z da db : ℝ)
    (hr0 : 0 < r) (hrb : r < b) (hb1 : b < 1) (hz : 0 < z)
    (hda : 0 ≤ da) (hdb : 0 ≤ db) :
    0 < renewalQuad 3 r b z da db := by
  have hr1 : r < 1 := lt_trans hrb hb1
  have hb0 : 0 < b := lt_trans hr0 hrb
  have hcorner : 0 < Phi 3 r b z :=
    corner_three_pos_interior r b z hr0 hrb hb1 hz.le
  have hq0 : 0 < Phi 3 r b z/4 := by positivity
  have hhbb : 0 < hBetaBeta 3 b z := by
    unfold hBetaBeta
    positivity
  have hhaa : 0 < hAlphaAlpha 3 r b z := by
    unfold hAlphaAlpha
    positivity
  have hdet : 0 < hAlphaAlpha 3 r b z*hBetaBeta 3 b z
      -(hAlphaBeta 3 r b z)^2 := by
    rw [hessian_det_factor 3 r b z (by norm_num) (ne_of_gt hz) (ne_of_lt hr1)]
    positivity
  have hR : 0 < interiorRNorm 3 r b z := by
    unfold interiorRNorm
    apply interiorR_three_pos r (1-r) (z*(1-r)/(1-b))
      ((b-r)/(1-r)) ((1-b)/(1-r))
    all_goals positivity
  have hstar : hAlphaBeta 3 r b z*gBeta 3 r b z
      -hBetaBeta 3 b z*gAlpha 3 r b z < 0 := by
    rw [interior_stationary_factor 3 r b z (by norm_num) (by norm_num)
      (ne_of_gt hz) (ne_of_lt hr1) (ne_of_lt hb1)]
    have hnum : 0 < 2*(b-r)*(1-b)*(b+z)*(3+1: ℝ) := by positivity
    have hden : 0 < 3*z*(3-1)*(1-r)^2 := by positivity
    have hnumneg : -2*(b-r)*(1-b)*(b+z)*(3+1: ℝ) < 0 := by
      have heq : -2*(b-r)*(1-b)*(b+z)*(3+1: ℝ) =
          -(2*(b-r)*(1-b)*(b+z)*(3+1)) := by ring
      rw [heq]
      exact neg_neg_of_pos hnum
    have hpref : -2*(b-r)*(1-b)*(b+z)*(3+1) /
        (3*z*(3-1)*(1-r)^2) < 0 :=
      div_neg_of_neg_of_pos hnumneg hden
    exact mul_neg_of_neg_of_pos hpref hR
  have hfaceBeta : ∀ t, 0 ≤ t →
      0 < quad2 (Phi 3 r b z/4)
        (gAlpha 3 r b z) (gBeta 3 r b z)
        (hAlphaAlpha 3 r b z) (hAlphaBeta 3 r b z)
        (hBetaBeta 3 b z) 0 t := by
    intro t ht
    unfold quad2
    norm_num
    apply quad1_pos (Phi 3 r b z/4) (gBeta 3 r b z)
      (hBetaBeta 3 b z) t hq0 hhbb ht
    intro hg
    have hS : SBeta 3 r b z < 0 := by
      unfold gBeta at hg
      norm_num at hg
      linarith
    have hK := kBeta_three_pos_interior r b z hr0 hrb hb1 hz hS
    have hid := beta_face_discriminant 3 r b z (by norm_num) (by norm_num)
      (ne_of_gt hz)
    norm_num at hid
    rw [hid]
    positivity
  have hfaceAlpha : ∀ t, 0 ≤ t →
      0 < quad2 (Phi 3 r b z/4)
        (gAlpha 3 r b z) (gBeta 3 r b z)
        (hAlphaAlpha 3 r b z) (hAlphaBeta 3 r b z)
        (hBetaBeta 3 b z) t 0 := by
    intro t ht
    unfold quad2
    norm_num
    apply quad1_pos (Phi 3 r b z/4) (gAlpha 3 r b z)
      (hAlphaAlpha 3 r b z) t hq0 hhaa ht
    intro hg
    have hpre : 0 < (b-r)*(1-b)/((1-r)^2*(3-1: ℝ)) := by positivity
    have hS : SAlpha 3 r b z < 0 := by
      have hgeq : gAlpha 3 r b z =
          (b-r)*(1-b)/((1-r)^2*(3-1: ℝ))*SAlpha 3 r b z := rfl
      rw [hgeq] at hg
      by_contra hnot
      have hs0 : 0 ≤ SAlpha 3 r b z := le_of_not_gt hnot
      exact (not_lt_of_ge (mul_nonneg hpre.le hs0)) hg
    have hRA := rAlphaThree_pos_of_stationary r b z hr0.le hrb.le hb1.le hz.le hS
    rw [alpha_face_discriminant_three r b z (ne_of_lt hr1)]
    positivity
  unfold renewalQuad
  norm_num
  exact quad2_pos_on_quadrant
    (Phi 3 r b z/4) (gAlpha 3 r b z) (gBeta 3 r b z)
    (hAlphaAlpha 3 r b z) (hAlphaBeta 3 r b z) (hBetaBeta 3 b z)
    hhbb hdet hstar hfaceBeta hfaceAlpha da db hda hdb

theorem renewalGap_three_nonneg
    (x u v p q A B C D : ℝ)
    (hx : 0 < x) (hu : 0 < u) (hv : 0 < v)
    (hp : 0 < p) (hq : 0 < q) (hpq : p+q=1)
    (hA : (3:ℝ)/2*u^2 ≤ A) (hB : (3:ℝ)/2*v^2 ≤ B)
    (hC : 4*A^2 ≤ 3*u*C) (hD : 4*B^2 ≤ 3*v*D) :
    0 ≤ renewalGap 3 x u v p q A B C D := by
  let l := x+u
  let r := x/l
  let b := p+q*r
  let z := q*v/l
  let da := A/l^2-(3:ℝ)/2*(u/l)^2
  let db := q^2*B/l^2-(3:ℝ)/2*z^2
  have hl : 0 < l := by dsimp [l]; linarith
  have h1r : 0 < 1-r := by
    have hid : 1-r = u/l := by
      dsimp [r, l]
      field_simp [ne_of_gt (show 0 < x+u by linarith)]
      ring
    rw [hid]
    positivity
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hbr : b-r = p*(1-r) := by
    have hpform : p = 1-q := by linarith
    dsimp [b]
    rw [hpform]
    ring
  have hrb : r < b := by rw [← sub_pos, hbr]; positivity
  have h1b : 1-b = q*(1-r) := by
    have hpform : p = 1-q := by linarith
    dsimp [b]
    rw [hpform]
    ring
  have hb1 : b < 1 := by rw [← sub_pos, h1b]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hda : 0 ≤ da := by
    have hbase : 0 ≤ A-(3:ℝ)/2*u^2 := by linarith
    have hid : da = (A-(3:ℝ)/2*u^2)/l^2 := by
      dsimp [da]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  have hdb : 0 ≤ db := by
    have hbase : 0 ≤ B-(3:ℝ)/2*v^2 := by linarith
    have hid : db = q^2/l^2*(B-(3:ℝ)/2*v^2) := by
      dsimp [db, z]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  have hquad := renewalQuad_three_nonneg r b z da db hr0 hrb hb1 hz hda hdb
  have hnorm := renewalGap_normalization 3 x u v p q A B (by norm_num)
    (by norm_num) (ne_of_gt hu) (ne_of_gt hv) (ne_of_gt hl) hpq
  have hquad' : 0 ≤ renewalQuad 3
      (x/(x+u)) (p+q*(x/(x+u))) (q*v/(x+u))
      (A/(x+u)^2-3/(3-1)*(u/(x+u))^2)
      (q^2*B/(x+u)^2-3/(3-1)*(q*v/(x+u))^2) := by
    norm_num
    simpa [l, r, b, z, da, db] using hquad
  have hsub : 0 ≤ renewalGapSub 3 x u v p q A B := by
    rw [hnorm]
    exact mul_nonneg (by positivity) hquad'
  have hdu : 0 ≤ C-4/3*A^2/u := by
    have hden : 0 < 3*u := by positivity
    have hquot : 4*A^2/(3*u) ≤ C := by
      rw [div_le_iff₀ hden]
      nlinarith
    have hid : (4:ℝ)/3*A^2/u = 4*A^2/(3*u) := by
      field_simp [ne_of_gt hu]
    rw [hid]
    linarith
  have hdv : 0 ≤ D-4/3*B^2/v := by
    have hden : 0 < 3*v := by positivity
    have hquot : 4*B^2/(3*v) ≤ D := by
      rw [div_le_iff₀ hden]
      nlinarith
    have hid : (4:ℝ)/3*B^2/v = 4*B^2/(3*v) := by
      field_simp [ne_of_gt hv]
    rw [hid]
    linarith
  have hx1 : 0 < renewalX1 x u v p q := by
    unfold renewalX1 kernelM1
    positivity
  rw [renewalGap_third_slacks 3 x u v p q A B C D
    (by norm_num) (ne_of_gt hu) (ne_of_gt hv)]
  have hslack : 0 ≤ p*q^2*(C-4/3*A^2/u)+q^3*(D-4/3*B^2/v) := by positivity
  norm_num
  positivity

theorem renewalGap_three_pos
    (x u v p q A B C D : ℝ)
    (hx : 0 < x) (hu : 0 < u) (hv : 0 < v)
    (hp : 0 < p) (hq : 0 < q) (hpq : p+q=1)
    (hA : (3:ℝ)/2*u^2 ≤ A) (hB : (3:ℝ)/2*v^2 ≤ B)
    (hC : 4*A^2 ≤ 3*u*C) (hD : 4*B^2 ≤ 3*v*D) :
    0 < renewalGap 3 x u v p q A B C D := by
  let l := x+u
  let r := x/l
  let b := p+q*r
  let z := q*v/l
  let da := A/l^2-(3:ℝ)/2*(u/l)^2
  let db := q^2*B/l^2-(3:ℝ)/2*z^2
  have hl : 0 < l := by dsimp [l]; linarith
  have h1r : 0 < 1-r := by
    have hid : 1-r = u/l := by
      dsimp [r, l]
      field_simp [ne_of_gt (show 0 < x+u by linarith)]
      ring
    rw [hid]
    positivity
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hbr : b-r = p*(1-r) := by
    have hpform : p = 1-q := by linarith
    dsimp [b]
    rw [hpform]
    ring
  have hrb : r < b := by rw [← sub_pos, hbr]; positivity
  have h1b : 1-b = q*(1-r) := by
    have hpform : p = 1-q := by linarith
    dsimp [b]
    rw [hpform]
    ring
  have hb1 : b < 1 := by rw [← sub_pos, h1b]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hda : 0 ≤ da := by
    have hbase : 0 ≤ A-(3:ℝ)/2*u^2 := by linarith
    have hid : da = (A-(3:ℝ)/2*u^2)/l^2 := by
      dsimp [da]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  have hdb : 0 ≤ db := by
    have hbase : 0 ≤ B-(3:ℝ)/2*v^2 := by linarith
    have hid : db = q^2/l^2*(B-(3:ℝ)/2*v^2) := by
      dsimp [db, z]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  have hquad := renewalQuad_three_pos r b z da db hr0 hrb hb1 hz hda hdb
  have hnorm := renewalGap_normalization 3 x u v p q A B (by norm_num)
    (by norm_num) (ne_of_gt hu) (ne_of_gt hv) (ne_of_gt hl) hpq
  have hquad' : 0 < renewalQuad 3
      (x/(x+u)) (p+q*(x/(x+u))) (q*v/(x+u))
      (A/(x+u)^2-3/(3-1)*(u/(x+u))^2)
      (q^2*B/(x+u)^2-3/(3-1)*(q*v/(x+u))^2) := by
    norm_num
    simpa [l, r, b, z, da, db] using hquad
  have hsub : 0 < renewalGapSub 3 x u v p q A B := by
    rw [hnorm]
    exact mul_pos (by positivity) hquad'
  have hdu : 0 ≤ C-4/3*A^2/u := by
    have hden : 0 < 3*u := by positivity
    have hquot : 4*A^2/(3*u) ≤ C := by
      rw [div_le_iff₀ hden]
      nlinarith
    have hid : (4:ℝ)/3*A^2/u = 4*A^2/(3*u) := by
      field_simp [ne_of_gt hu]
    rw [hid]
    linarith
  have hdv : 0 ≤ D-4/3*B^2/v := by
    have hden : 0 < 3*v := by positivity
    have hquot : 4*B^2/(3*v) ≤ D := by
      rw [div_le_iff₀ hden]
      nlinarith
    have hid : (4:ℝ)/3*B^2/v = 4*B^2/(3*v) := by
      field_simp [ne_of_gt hv]
    rw [hid]
    linarith
  rw [renewalGap_third_slacks 3 x u v p q A B C D
    (by norm_num) (ne_of_gt hu) (ne_of_gt hv)]
  have hx1 : 0 < renewalX1 x u v p q := by
    unfold renewalX1 kernelM1
    positivity
  have hslack : 0 ≤ p*q^2*(C-4/3*A^2/u)+q^3*(D-4/3*B^2/v) := by positivity
  norm_num
  positivity

theorem renewal_moment_inequality_three
    (x u v p q A B C D : ℝ)
    (hx : 0 < x) (hu : 0 < u) (hv : 0 < v)
    (hp : 0 < p) (hq : 0 < q) (hpq : p+q=1)
    (hA : (3:ℝ)/2*u^2 ≤ A) (hB : (3:ℝ)/2*v^2 ≤ B)
    (hC : 4*A^2 ≤ 3*u*C) (hD : 4*B^2 ≤ 3*v*D) :
    5*(renewalM2 x u v p q A B)^2 ≤
      4*renewalM1 x u v p q*renewalM3 x u v p q A B C D := by
  have hgap := renewalGap_three_nonneg x u v p q A B C D hx hu hv hp hq hpq
    hA hB hC hD
  have huq := renewalGap_unscale 3 x u v p q A B C D (ne_of_gt hq)
  have hscaled := div_nonneg hgap (show 0 ≤ q^4 by positivity)
  unfold gap at huq
  norm_num at huq
  linarith

theorem renewal_moment_strict_three
    (x u v p q A B C D : ℝ)
    (hx : 0 < x) (hu : 0 < u) (hv : 0 < v)
    (hp : 0 < p) (hq : 0 < q) (hpq : p+q=1)
    (hA : (3:ℝ)/2*u^2 ≤ A) (hB : (3:ℝ)/2*v^2 ≤ B)
    (hC : 4*A^2 ≤ 3*u*C) (hD : 4*B^2 ≤ 3*v*D) :
    5*(renewalM2 x u v p q A B)^2 <
      4*renewalM1 x u v p q*renewalM3 x u v p q A B C D := by
  have hgap := renewalGap_three_pos x u v p q A B C D hx hu hv hp hq hpq
    hA hB hC hD
  have huq := renewalGap_unscale 3 x u v p q A B C D (ne_of_gt hq)
  have hscaled : 0 < renewalGap 3 x u v p q A B C D/q^4 := by positivity
  unfold gap at huq
  norm_num at huq
  linarith

theorem renewalQuad_alpha_face_three_nonneg (r b da : ℝ)
    (hr0 : 0 < r) (hrb : r < b) (hb1 : b < 1) (hda : 0 ≤ da) :
    0 ≤ renewalQuad 3 r b 0 da 0 := by
  have hr1 : r < 1 := lt_trans hrb hb1
  have hcorner : 0 ≤ Phi 3 r b 0 :=
    corner_three_nonneg r b 0 hr0.le hrb.le hb1.le (by norm_num)
  have hq0 : 0 ≤ Phi 3 r b 0/4 := by positivity
  have hhaa : 0 < hAlphaAlpha 3 r b 0 := by
    rw [show hAlphaAlpha 3 r b 0 =
        2*(b-r)*(1-b)^2/(3*(1-r)^4)*(15*r+b) by norm_num [hAlphaAlpha]]
    have hleft : 0 < 2*(b-r)*(1-b)^2/(3*(1-r)^4) := by positivity
    have hright : 0 < 15*r+b := by linarith
    exact mul_pos hleft hright
  have hface := quad1_nonneg (Phi 3 r b 0/4) (gAlpha 3 r b 0)
    (hAlphaAlpha 3 r b 0) da hq0 hhaa hda
  have hdisc : gAlpha 3 r b 0 < 0 →
      0 ≤ 2*hAlphaAlpha 3 r b 0*(Phi 3 r b 0/4)-(gAlpha 3 r b 0)^2 := by
    intro hg
    have hpre : 0 < (b-r)*(1-b)/((1-r)^2*(3-1: ℝ)) := by positivity
    have hSA : 0 < SAlpha 3 r b 0 := by
      have hterm : 0 < 30*r*(1-b) := by positivity
      norm_num [SAlpha]
      nlinarith [sq_nonneg b]
    have hgeq : gAlpha 3 r b 0 =
        (b-r)*(1-b)/((1-r)^2*(3-1: ℝ))*SAlpha 3 r b 0 := rfl
    rw [hgeq] at hg
    exact False.elim ((not_lt_of_ge (mul_nonneg hpre.le hSA.le)) hg)
  specialize hface hdisc
  unfold renewalQuad quad2
  norm_num
  simpa using hface

theorem renewalQuad_alpha_face_three_pos (r b da : ℝ)
    (hr0 : 0 < r) (hrb : r < b) (hb1 : b < 1) (hda : 0 ≤ da) :
    0 < renewalQuad 3 r b 0 da 0 := by
  have hr1 : r < 1 := lt_trans hrb hb1
  have hcorner : 0 < Phi 3 r b 0 :=
    corner_three_pos_interior r b 0 hr0 hrb hb1 (by norm_num)
  have hq0 : 0 < Phi 3 r b 0/4 := by positivity
  have hhaa : 0 < hAlphaAlpha 3 r b 0 := by
    rw [show hAlphaAlpha 3 r b 0 =
        2*(b-r)*(1-b)^2/(3*(1-r)^4)*(15*r+b) by norm_num [hAlphaAlpha]]
    have hleft : 0 < 2*(b-r)*(1-b)^2/(3*(1-r)^4) := by positivity
    have hright : 0 < 15*r+b := by linarith
    exact mul_pos hleft hright
  have hdisc : gAlpha 3 r b 0 < 0 →
      0 < 2*hAlphaAlpha 3 r b 0*(Phi 3 r b 0/4)-(gAlpha 3 r b 0)^2 := by
    intro hg
    have hpre : 0 < (b-r)*(1-b)/((1-r)^2*(3-1: ℝ)) := by positivity
    have hSA : 0 < SAlpha 3 r b 0 := by
      have hterm : 0 < 30*r*(1-b) := by positivity
      norm_num [SAlpha]
      nlinarith [sq_nonneg b]
    have hgeq : gAlpha 3 r b 0 =
        (b-r)*(1-b)/((1-r)^2*(3-1: ℝ))*SAlpha 3 r b 0 := rfl
    rw [hgeq] at hg
    exact False.elim ((not_lt_of_ge (mul_nonneg hpre.le hSA.le)) hg)
  have hface := quad1_pos (Phi 3 r b 0/4) (gAlpha 3 r b 0)
    (hAlphaAlpha 3 r b 0) da hq0 hhaa hda hdisc
  unfold renewalQuad quad2
  norm_num
  simpa using hface

theorem renewalGap_vzero_three_nonneg
    (x u p q A C : ℝ) (hx : 0 < x) (hu : 0 < u)
    (hp : 0 < p) (hq : 0 < q) (hpq : p+q=1)
    (hA : (3:ℝ)/2*u^2 ≤ A) (hC : 4*A^2 ≤ 3*u*C) :
    0 ≤ renewalGap 3 x u 0 p q A 0 C 0 := by
  let l := x+u
  let r := x/l
  let b := p+q*r
  let da := A/l^2-(3:ℝ)/2*(u/l)^2
  have hl : 0 < l := by dsimp [l]; linarith
  have h1r : 0 < 1-r := by
    have hid : 1-r=u/l := by
      dsimp [r, l]
      field_simp [ne_of_gt hl]
      ring
    rw [hid]
    positivity
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hbr : b-r=p*(1-r) := by
    have hpform : p=1-q := by linarith
    dsimp [b]
    rw [hpform]
    ring
  have hrb : r < b := by rw [← sub_pos, hbr]; positivity
  have h1b : 1-b=q*(1-r) := by
    have hpform : p=1-q := by linarith
    dsimp [b]
    rw [hpform]
    ring
  have hb1 : b < 1 := by rw [← sub_pos, h1b]; positivity
  have hda : 0 ≤ da := by
    have hbase : 0 ≤ A-(3:ℝ)/2*u^2 := by linarith
    have hid : da=(A-(3:ℝ)/2*u^2)/l^2 := by
      dsimp [da]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  have hquad := renewalQuad_alpha_face_three_nonneg r b da hr0 hrb hb1 hda
  have hnorm := renewalGap_normalization_vzero 3 x u p q A (by norm_num)
    (by norm_num) (ne_of_gt hu) (ne_of_gt hl) hpq
  have hquad' : 0 ≤ renewalQuad 3 (x/(x+u)) (p+q*(x/(x+u))) 0
      (A/(x+u)^2-3/(3-1)*(u/(x+u))^2) 0 := by
    norm_num
    simpa [l, r, b, da] using hquad
  have hsub : 0 ≤ renewalGapSubVZero 3 x u p q A := by
    rw [hnorm]
    exact mul_nonneg (by positivity) hquad'
  have hdu : 0 ≤ C-4/3*A^2/u := by
    have hden : 0 < 3*u := by positivity
    have hquot : 4*A^2/(3*u) ≤ C := by
      rw [div_le_iff₀ hden]
      nlinarith
    have hid : (4:ℝ)/3*A^2/u=4*A^2/(3*u) := by
      field_simp [ne_of_gt hu]
    rw [hid]
    linarith
  rw [renewalGap_vzero_third_slack 3 x u p q A C (by norm_num) (ne_of_gt hu)]
  have hx1 : 0 < renewalX1 x u 0 p q := by
    unfold renewalX1 kernelM1
    positivity
  norm_num
  positivity

theorem renewalGap_vzero_three_pos
    (x u p q A C : ℝ) (hx : 0 < x) (hu : 0 < u)
    (hp : 0 < p) (hq : 0 < q) (hpq : p+q=1)
    (hA : (3:ℝ)/2*u^2 ≤ A) (hC : 4*A^2 ≤ 3*u*C) :
    0 < renewalGap 3 x u 0 p q A 0 C 0 := by
  let l := x+u
  let r := x/l
  let b := p+q*r
  let da := A/l^2-(3:ℝ)/2*(u/l)^2
  have hl : 0 < l := by dsimp [l]; linarith
  have h1r : 0 < 1-r := by
    have hid : 1-r=u/l := by
      dsimp [r, l]
      field_simp [ne_of_gt hl]
      ring
    rw [hid]
    positivity
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hbr : b-r=p*(1-r) := by
    have hpform : p=1-q := by linarith
    dsimp [b]
    rw [hpform]
    ring
  have hrb : r < b := by rw [← sub_pos, hbr]; positivity
  have h1b : 1-b=q*(1-r) := by
    have hpform : p=1-q := by linarith
    dsimp [b]
    rw [hpform]
    ring
  have hb1 : b < 1 := by rw [← sub_pos, h1b]; positivity
  have hda : 0 ≤ da := by
    have hbase : 0 ≤ A-(3:ℝ)/2*u^2 := by linarith
    have hid : da=(A-(3:ℝ)/2*u^2)/l^2 := by
      dsimp [da]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  have hquad := renewalQuad_alpha_face_three_pos r b da hr0 hrb hb1 hda
  have hnorm := renewalGap_normalization_vzero 3 x u p q A (by norm_num)
    (by norm_num) (ne_of_gt hu) (ne_of_gt hl) hpq
  have hquad' : 0 < renewalQuad 3 (x/(x+u)) (p+q*(x/(x+u))) 0
      (A/(x+u)^2-3/(3-1)*(u/(x+u))^2) 0 := by
    norm_num
    simpa [l, r, b, da] using hquad
  have hsub : 0 < renewalGapSubVZero 3 x u p q A := by
    rw [hnorm]
    exact mul_pos (by positivity) hquad'
  have hdu : 0 ≤ C-4/3*A^2/u := by
    have hden : 0 < 3*u := by positivity
    have hquot : 4*A^2/(3*u) ≤ C := by
      rw [div_le_iff₀ hden]
      nlinarith
    have hid : (4:ℝ)/3*A^2/u=4*A^2/(3*u) := by
      field_simp [ne_of_gt hu]
    rw [hid]
    linarith
  rw [renewalGap_vzero_third_slack 3 x u p q A C (by norm_num) (ne_of_gt hu)]
  have hx1 : 0 < renewalX1 x u 0 p q := by
    unfold renewalX1 kernelM1
    positivity
  norm_num
  positivity

theorem renewalQuad_three_nonneg_pzero (r z da db : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (hz : 0 < z) (hdb : 0 ≤ db) :
    0 ≤ renewalQuad 3 r r z da db := by
  have hcorner : 0 ≤ Phi 3 r r z :=
    corner_three_nonneg r r z hr0.le le_rfl hr1.le hz.le
  have hq0 : 0 ≤ Phi 3 r r z/4 := by positivity
  have hhbb : 0 < hBetaBeta 3 r z := by
    unfold hBetaBeta
    positivity
  have hdisc : gBeta 3 r r z < 0 →
      0 ≤ 2*hBetaBeta 3 r z*(Phi 3 r r z/4)-(gBeta 3 r r z)^2 := by
    intro hg
    have hS : SBeta 3 r r z ≤ 0 := by
      unfold gBeta at hg
      norm_num at hg
      linarith
    have hK := kBeta_three_nonneg r r z hr0.le le_rfl hr1.le hz.le hS
    have hid := beta_face_discriminant 3 r r z (by norm_num) (by norm_num)
      (ne_of_gt hz)
    norm_num at hid
    rw [hid]
    positivity
  have hface := quad1_nonneg (Phi 3 r r z/4) (gBeta 3 r r z)
    (hBetaBeta 3 r z) db hq0 hhbb hdb hdisc
  unfold renewalQuad quad2 gAlpha hAlphaAlpha hAlphaBeta
  norm_num
  simpa using hface

theorem renewalQuad_three_pzero_eq_zero_iff (r z da db : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (hz : 0 < z) (hdb : 0 ≤ db) :
    renewalQuad 3 r r z da db = 0 ↔ db = 0 ∧ z = 2*r := by
  have hq0 : 0 ≤ Phi 3 r r z/4 := by
    have := corner_three_nonneg r r z hr0.le le_rfl hr1.le hz.le
    positivity
  have hh : 0 < hBetaBeta 3 r z := by unfold hBetaBeta; positivity
  have hreduce : renewalQuad 3 r r z da db =
      Phi 3 r r z/4+gBeta 3 r r z*db+hBetaBeta 3 r z*db^2/2 := by
    unfold renewalQuad quad2 gAlpha hAlphaAlpha hAlphaBeta
    norm_num
  constructor
  · intro hzero
    have hdb0 : db = 0 := by
      by_contra hne
      have hdbpos : 0 < db := lt_of_le_of_ne hdb (Ne.symm hne)
      have hstrict : 0 < Phi 3 r r z/4+gBeta 3 r r z*db
          +hBetaBeta 3 r z*db^2/2 := by
        rcases le_or_gt 0 (gBeta 3 r r z) with hg | hg
        · have hlin : 0 ≤ gBeta 3 r r z*db := mul_nonneg hg hdb
          have hquad : 0 < hBetaBeta 3 r z*db^2/2 := by positivity
          linarith
        · let y := z/r
          have hy : 0 ≤ y := by dsimp [y]; positivity
          have hzy : z = r*y := by dsimp [y]; field_simp
          have hS : SBeta 3 r r z < 0 := by
            unfold gBeta at hg
            norm_num at hg
            linarith
          have hf : FBeta 3 y < 0 := by
            have hid := sBeta_at_b_scaled 3 r y
            rw [← hzy] at hid
            rw [hid] at hS
            change r^2*FBeta 3 y < 0 at hS
            nlinarith [sq_pos_of_pos hr0]
          have hthreshold := fBeta_three_threshold_strict y hy hf
          have hfac : 0 < 16*r-11*z := by
            rw [hzy]
            nlinarith [mul_pos hr0 (sub_pos.mpr hthreshold)]
          have hK : 0 < KBeta 3 r r z := by
            rw [kBeta_at_b]
            norm_num
            positivity
          have hdiscEq := beta_face_discriminant 3 r r z (by norm_num)
            (by norm_num) (ne_of_gt hz)
          norm_num at hdiscEq
          have hdisc : 0 < 2*hBetaBeta 3 r z*(Phi 3 r r z/4)
              -(gBeta 3 r r z)^2 := by
            rw [hdiscEq]
            positivity
          have hid : Phi 3 r r z/4+gBeta 3 r r z*db+hBetaBeta 3 r z*db^2/2 =
              (2*hBetaBeta 3 r z*(Phi 3 r r z/4)-(gBeta 3 r r z)^2) /
                (2*hBetaBeta 3 r z) +
              hBetaBeta 3 r z/2*(db+gBeta 3 r r z/hBetaBeta 3 r z)^2 := by
            field_simp [ne_of_gt hh]
            ring
          rw [hid]
          have hfirst : 0 <
              (2*hBetaBeta 3 r z*(Phi 3 r r z/4)-(gBeta 3 r r z)^2) /
                (2*hBetaBeta 3 r z) := by positivity
          have hsecond : 0 ≤ hBetaBeta 3 r z/2*
              (db+gBeta 3 r r z/hBetaBeta 3 r z)^2 := by positivity
          linarith
      rw [hreduce] at hzero
      linarith
    have hphi0 : Phi 3 r r z = 0 := by
      have hreduce0 : renewalQuad 3 r r z da 0 = Phi 3 r r z/4 := by
        simpa [hdb0] using hreduce
      rw [hdb0] at hzero
      rw [hreduce0] at hzero
      norm_num at hzero
      linarith
    have hfactor := phi_at_b 3 r z
    norm_num at hfactor
    rw [hfactor] at hphi0
    have hpref : 0 < 4*r^2+12*r*z+3*z^2 := by positivity
    have hsquare : (z-2*r)^2 = 0 :=
      (mul_eq_zero.mp hphi0).resolve_left (ne_of_gt hpref)
    exact ⟨hdb0, by nlinarith [sq_nonneg (z-2*r)]⟩
  · rintro ⟨rfl, hzrel⟩
    rw [hreduce]
    norm_num
    rw [phi_at_b]
    norm_num [hzrel]

theorem no_return_moment_inequality_three
    (x v B D : ℝ) (hx : 0 < x) (hv : 0 < v)
    (hB : (3:ℝ)/2*v^2 ≤ B) (hD : 4*B^2 ≤ 3*v*D) :
    5*(kernelM2 x v B)^2 ≤ 4*kernelM1 x v*kernelM3 x v B D := by
  let u := x
  let A := (3:ℝ)/2*u^2
  let l := x+u
  let r := x/l
  let z := v/l
  let db := B/l^2-(3:ℝ)/2*z^2
  have hu : 0 < u := by simpa [u]
  have hl : 0 < l := by dsimp [l, u]; linarith
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r, l, u]
    rw [div_lt_one (by linarith)]
    linarith
  have hz : 0 < z := by dsimp [z]; positivity
  have hdb : 0 ≤ db := by
    have hbase : 0 ≤ B-(3:ℝ)/2*v^2 := by linarith
    have hid : db=(B-(3:ℝ)/2*v^2)/l^2 := by
      dsimp [db, z]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  let da := A/l^2-(3:ℝ)/2*(u/l)^2
  have hquad := renewalQuad_three_nonneg_pzero r z da db hr0 hr1 hz hdb
  have hnorm := renewalGap_normalization 3 x u v 0 1 A B (by norm_num)
    (by norm_num) (ne_of_gt hu) (ne_of_gt hv) (ne_of_gt hl) (by norm_num)
  have hquad' : 0 ≤ renewalQuad 3 (x/(x+u)) (x/(x+u)) (v/(x+u))
      (A/(x+u)^2-3/(3-1)*(u/(x+u))^2)
      (B/(x+u)^2-3/(3-1)*(v/(x+u))^2) := by
    norm_num
    simpa [l, r, z, da, db] using hquad
  have hsub : 0 ≤ renewalGapSub 3 x u v 0 1 A B := by
    rw [hnorm]
    norm_num
    norm_num at hquad'
    exact mul_nonneg (by positivity) hquad'
  have hdv : 0 ≤ D-4/3*B^2/v := by
    have hden : 0 < 3*v := by positivity
    have hquot : 4*B^2/(3*v) ≤ D := by
      rw [div_le_iff₀ hden]
      nlinarith
    have hid : (4:ℝ)/3*B^2/v=4*B^2/(3*v) := by
      field_simp [ne_of_gt hv]
    rw [hid]
    linarith
  have hgapid := renewalGap_third_slacks 3 x u v 0 1 A B 0 D
    (by norm_num) (ne_of_gt hu) (ne_of_gt hv)
  norm_num at hgapid
  have hgap : 0 ≤ renewalGap 3 x u v 0 1 A B 0 D := by
    rw [hgapid]
    unfold renewalX1 kernelM1
    positivity
  unfold renewalGap renewalX1 renewalX2 renewalX3 at hgap
  norm_num [kernelM1, kernelM2, kernelM3] at hgap
  exact hgap

theorem no_return_equality_three_iff
    (x v B D : ℝ) (hx : 0 < x) (hv : 0 < v)
    (hB : (3:ℝ)/2*v^2 ≤ B) (hD : 4*B^2 ≤ 3*v*D) :
    4*kernelM1 x v*kernelM3 x v B D-5*(kernelM2 x v B)^2 = 0 ↔
      B=(3:ℝ)/2*v^2 ∧ D=(4:ℝ)/3*B^2/v ∧ v=2*x := by
  let u := x
  let A := (3:ℝ)/2*u^2
  let l := x+u
  let r := x/l
  let z := v/l
  let db := B/l^2-(3:ℝ)/2*z^2
  let da := A/l^2-(3:ℝ)/2*(u/l)^2
  have hu : 0 < u := by simpa [u]
  have hl : 0 < l := by dsimp [l, u]; linarith
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r, l, u]
    rw [div_lt_one (by linarith)]
    linarith
  have hz : 0 < z := by dsimp [z]; positivity
  have hdb : 0 ≤ db := by
    have hbase : 0 ≤ B-(3:ℝ)/2*v^2 := by linarith
    have hid : db=(B-(3:ℝ)/2*v^2)/l^2 := by
      dsimp [db, z]
      field_simp [ne_of_gt hl]
    rw [hid]
    positivity
  have hdu : 0 ≤ D-(4:ℝ)/3*B^2/v := by
    have hden : 0 < 3*v := by positivity
    have hquot : 4*B^2/(3*v) ≤ D := by
      rw [div_le_iff₀ hden]
      nlinarith
    have hid : (4:ℝ)/3*B^2/v=4*B^2/(3*v) := by
      field_simp [ne_of_gt hv]
    rw [hid]
    linarith
  have hquadnon := renewalQuad_three_nonneg_pzero r z da db hr0 hr1 hz hdb
  have hnorm := renewalGap_normalization 3 x u v 0 1 A B (by norm_num)
    (by norm_num) (ne_of_gt hu) (ne_of_gt hv) (ne_of_gt hl) (by norm_num)
  have hnorm' : renewalGapSub 3 x u v 0 1 A B =
      l^4*renewalQuad 3 r r z da db := by
    norm_num at hnorm
    simpa [l, r, z, da, db] using hnorm
  have hsub : 0 ≤ renewalGapSub 3 x u v 0 1 A B := by
    rw [hnorm']
    exact mul_nonneg (by positivity) hquadnon
  have hgapid := renewalGap_third_slacks 3 x u v 0 1 A B 0 D
    (by norm_num) (ne_of_gt hu) (ne_of_gt hv)
  norm_num [renewalX1, kernelM1] at hgapid
  have hxv : 0 < 4*(x+v) := by positivity
  constructor
  · intro heq
    have hrenew : renewalGap 3 x u v 0 1 A B 0 D = 0 := by
      unfold renewalGap renewalX1 renewalX2 renewalX3
      norm_num [kernelM1, kernelM2, kernelM3]
      exact heq
    have hsumzero : renewalGapSub 3 x u v 0 1 A B+
        4*(x+v)*(D-4*B^2/(3*v)) = 0 := by
      rw [hgapid] at hrenew
      convert hrenew using 1
      all_goals ring
    have hdu' : 0 ≤ D-4*B^2/(3*v) := by
      have hid : (4:ℝ)/3*B^2/v=4*B^2/(3*v) := by
        field_simp [ne_of_gt hv]
      rw [← hid]
      exact hdu
    have hthirdterm : 0 ≤ 4*(x+v)*(D-4*B^2/(3*v)) :=
      mul_nonneg hxv.le hdu'
    have hsubzero : renewalGapSub 3 x u v 0 1 A B = 0 := by linarith
    have hthirdzero : D-4*B^2/(3*v) = 0 := by
      have hprod : 4*(x+v)*(D-4*B^2/(3*v)) = 0 := by linarith
      exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hxv)
    have hquadzero : renewalQuad 3 r r z da db = 0 := by
      have hl4 : 0 < l^4 := by positivity
      rw [hnorm'] at hsubzero
      exact (mul_eq_zero.mp hsubzero).resolve_left (ne_of_gt hl4)
    have hsharp :=
      (renewalQuad_three_pzero_eq_zero_iff r z da db hr0 hr1 hz hdb).mp hquadzero
    have hBeq : B=(3:ℝ)/2*v^2 := by
      have hid : db=(B-(3:ℝ)/2*v^2)/l^2 := by
        dsimp [db, z]
        field_simp [ne_of_gt hl]
      rw [hsharp.1] at hid
      have hl2 : l^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hl)
      field_simp [hl2] at hid
      linarith
    have hveq : v=2*x := by
      have hzrel := hsharp.2
      dsimp [z, r, l, u] at hzrel
      field_simp [show x+x ≠ 0 by linarith] at hzrel
      linarith
    have hDeq : D=(4:ℝ)/3*B^2/v := by
      have hid : 4*B^2/(3*v)=(4:ℝ)/3*B^2/v := by
        field_simp [ne_of_gt hv]
      linarith
    exact ⟨hBeq, hDeq, hveq⟩
  · rintro ⟨hBeq, hDeq, hveq⟩
    rw [hDeq, hBeq, hveq]
    unfold kernelM1 kernelM2 kernelM3
    field_simp
    ring

theorem renewal_equality_three_iff
    (x u v p q A B C D : ℝ)
    (hx : 0 < x) (_hu : 0 ≤ u) (hv : 0 ≤ v)
    (hp : 0 ≤ p) (hq : 0 < q) (hpq : p+q=1)
    (hreturn : 0 < p → 0 < u) (hvzero : v=0 → B=0 ∧ D=0)
    (hA : (3:ℝ)/2*u^2 ≤ A) (hB : (3:ℝ)/2*v^2 ≤ B)
    (hC : 4*A^2 ≤ 3*u*C) (hD : 4*B^2 ≤ 3*v*D) :
    gap 3 (renewalM1 x u v p q) (renewalM2 x u v p q A B)
        (renewalM3 x u v p q A B C D) = 0 ↔
      p=0 ∧ B=(3:ℝ)/2*v^2 ∧ D=(4:ℝ)/3*B^2/v ∧ v=2*x := by
  constructor
  · intro heq
    have hpzero : p=0 := by
      by_contra hne
      have hppos : 0 < p := lt_of_le_of_ne hp (Ne.symm hne)
      have hupos := hreturn hppos
      rcases eq_or_lt_of_le hv with hv0 | hvpos
      · have hv0' : v=0 := hv0.symm
        have hz := hvzero hv0'
        have hraw := renewalGap_vzero_three_pos x u p q A C hx hupos hppos hq hpq hA hC
        have hun := renewalGap_unscale 3 x u 0 p q A 0 C 0 (ne_of_gt hq)
        have hscaled : 0 < renewalGap 3 x u 0 p q A 0 C 0/q^4 :=
          div_pos hraw (pow_pos hq 4)
        rw [hv0', hz.1, hz.2] at heq
        linarith
      · have hstrict := renewal_moment_strict_three x u v p q A B C D hx hupos hvpos
          hppos hq hpq hA hB hC hD
        unfold gap at heq
        norm_num at heq
        linarith
    have hqone : q=1 := by linarith
    rcases eq_or_lt_of_le hv with hv0 | hvpos
    · have hv0' : v=0 := hv0.symm
      have hz := hvzero hv0'
      have hstrict := no_return_atom_strict 3 (by omega) x hx
      rw [hpzero, hqone, hv0', hz.1, hz.2] at heq
      unfold gap at heq
      simp [renewalM1, renewalM2, renewalM3, renewalX1, renewalX2, renewalX3,
        kernelM1, kernelM2, kernelM3] at heq
      unfold kernelM1 kernelM2 kernelM3 at hstrict
      norm_num at hstrict
      nlinarith
    · have hiff := no_return_equality_three_iff x v B D hx hvpos hB hD
      have hkernel : 4*kernelM1 x v*kernelM3 x v B D-
          5*(kernelM2 x v B)^2=0 := by
        rw [hpzero, hqone] at heq
        unfold gap at heq
        norm_num at heq
        simpa [renewalM1, renewalM2, renewalM3, renewalX1, renewalX2, renewalX3,
          kernelM1, kernelM2, kernelM3] using heq
      exact ⟨hpzero, (hiff.mp hkernel).1, (hiff.mp hkernel).2.1,
        (hiff.mp hkernel).2.2⟩
  · rintro ⟨hpzero, hBeq, hDeq, hveq⟩
    have hqone : q=1 := by linarith
    have hvpos : 0 < v := by rw [hveq]; positivity
    have hiff := no_return_equality_three_iff x v B D hx hvpos hB hD
    have hkernel := hiff.mpr ⟨hBeq, hDeq, hveq⟩
    rw [hpzero, hqone]
    unfold gap
    norm_num
    simpa [renewalM1, renewalM2, renewalM3, renewalX1, renewalX2, renewalX3,
      kernelM1, kernelM2, kernelM3] using hkernel

end SSP.K2AllStages

namespace SSP.Chain

/-- The acyclic endpoint of the two-state numerator is sharp exactly for a certain
transition to a second state with the same exit rate. -/
theorem cyc2N_at_zero_eq_zero_iff (a b u : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    cyc2N a b u 0 = 0 ↔ u = 1 ∧ a = b := by
  have hid : cyc2N a b u 0
      = u^2 * a^2 * (a^2 - 7*a*b + b^2)
        + u * (a*b * (9*a^2 - 7*a*b + 2*b^2)) + b^4 := by
    unfold cyc2N
    ring
  constructor
  · intro hz
    rcases le_or_gt 0 (a^2 - 7*a*b + b^2) with hq | hq
    · have hlin : 0 < 9*a^2 - 7*a*b + 2*b^2 := by
        nlinarith [sq_nonneg (3*a - b), sq_nonneg a, sq_nonneg b,
          mul_pos ha hb]
      have hfirst : 0 ≤ u^2 * a^2 * (a^2 - 7*a*b + b^2) := by positivity
      have hsecond : 0 ≤ u * (a*b * (9*a^2 - 7*a*b + 2*b^2)) := by positivity
      have hb4 : 0 < b^4 := by positivity
      rw [hid] at hz
      linarith
    · have hA : a^2 * (a^2 - 7*a*b + b^2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) (le_of_lt hq)
      have h0 : 0 < b^4 := by positivity
      have h1nonneg :
          0 ≤ (a - b)^2 * (a^2 + 4*a*b + b^2) := by positivity
      have hone : cyc2N a b 1 0 =
          (a - b)^2 * (a^2 + 4*a*b + b^2) := by
        unfold cyc2N
        ring
      have hchord :
          0 ≤ (1-u) * b^4
            + u * ((a-b)^2 * (a^2 + 4*a*b + b^2)) := by positivity
      have hcurv :
          0 ≤ (u-u^2) * (-(a^2 * (a^2 - 7*a*b + b^2))) := by
        have huu : 0 ≤ u-u^2 := by nlinarith
        exact mul_nonneg huu (neg_nonneg.mpr hA)
      have hdecomp : cyc2N a b u 0 =
          (1-u) * b^4
            + u * ((a-b)^2 * (a^2 + 4*a*b + b^2))
            + (u-u^2) * (-(a^2 * (a^2 - 7*a*b + b^2))) := by
        unfold cyc2N
        ring
      have hu : u = 1 := by
        by_contra hne
        have hult : u < 1 := lt_of_le_of_ne hu1 hne
        have hpos : 0 < (1-u) * b^4 := mul_pos (sub_pos.mpr hult) h0
        have hmiddle : 0 ≤ u * ((a-b)^2 * (a^2 + 4*a*b + b^2)) :=
          mul_nonneg hu0 h1nonneg
        rw [hdecomp] at hz
        linarith
      subst u
      have hfactor : cyc2N a b 1 0 =
          (a-b)^2 * (a^2 + 4*a*b + b^2) := hone
      have hfacpos : 0 < a^2 + 4*a*b + b^2 := by positivity
      rw [hfactor] at hz
      have habsq : (a-b)^2 = 0 := (mul_eq_zero.mp hz).resolve_right hfacpos.ne'
      exact ⟨rfl, sub_eq_zero.mp (sq_eq_zero_iff.mp habsq)⟩
  · rintro ⟨rfl, rfl⟩
    unfold cyc2N
    ring

/-- The full two-state numerator is sharp exactly for the acyclic equal-rate Erlang chain. -/
theorem cyc2N_eq_zero_iff (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    cyc2N a b u v = 0 ↔ v = 0 ∧ u = 1 ∧ a = b := by
  have hzero := cyc2N_at_zero_nonneg a b u ha hb hu0 hu1
  have hone_nonneg := cyc2N_at_one_nonneg a b u ha hb hu0
  have hone_pos : 0 < cyc2N a b u 1 := by
    have hamgm : 0 ≤ 9*a^3*b * (u * (u-1)^2) := by positivity
    have hfour : 0 ≤ 4*a^3*b*u^2 := by positivity
    have hrest0 : 0 ≤ a^4*u^2 + 4*a^2*b^2*u^2 + 2*a^2*b^2*u + 4*a*b^3*u := by
      positivity
    have hb4 : 0 < b^4 := by positivity
    have hid : cyc2N a b u 1 =
        9*a^3*b * (u * (u-1)^2) + 4*a^3*b*u^2
          + (a^4*u^2 + 4*a^2*b^2*u^2 + 2*a^2*b^2*u + 4*a*b^3*u + b^4) := by
      unfold cyc2N
      ring
    rw [hid]
    linarith
  have hcurve : 0 ≤ 8*a^2*b^2*u^2*v*(1-v) := by positivity
  have hdecomp : cyc2N a b u v =
      (1-v) * cyc2N a b u 0 + v * cyc2N a b u 1
        + 8*a^2*b^2*u^2*v*(1-v) := by
    unfold cyc2N
    ring
  constructor
  · intro hz
    have hv : v = 0 := by
      by_contra hne
      have hvpos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hne)
      have hfirst : 0 ≤ (1-v) * cyc2N a b u 0 :=
        mul_nonneg (sub_nonneg.mpr hv1) hzero
      have hsecond : 0 < v * cyc2N a b u 1 := mul_pos hvpos hone_pos
      rw [hdecomp] at hz
      linarith
    subst v
    have hendpoint : cyc2N a b u 0 = 0 := by simpa using hz
    exact ⟨rfl, (cyc2N_at_zero_eq_zero_iff a b u ha hb hu0 hu1).mp hendpoint⟩
  · rintro ⟨rfl, rfl, rfl⟩
    unfold cyc2N
    ring

end SSP.Chain

namespace SSP.K2AllStages

/-- If a nonnegative finite mixture is sharp and every component satisfies the stage bound,
then every component carrying positive weight is itself sharp. -/
theorem mixture_equality_component_gap {ι : Type*}
    (s : ℕ) (hs : 1 ≤ s) (t : Finset ι) (w m₁ m₂ m₃ : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hm₁ : ∀ i ∈ t, 0 < m₁ i)
    (hcomp : ∀ i ∈ t, 0 ≤ gap s (m₁ i) (m₂ i) (m₃ i))
    (heq : gap s (∑ i ∈ t, w i*m₁ i) (∑ i ∈ t, w i*m₂ i)
      (∑ i ∈ t, w i*m₃ i) = 0) :
    ∀ i ∈ t, 0 < w i → gap s (m₁ i) (m₂ i) (m₃ i) = 0 := by
  classical
  let U : ι → ℝ := fun i => Real.sqrt (w i*m₁ i)
  let V : ι → ℝ := fun i => Real.sqrt (w i*m₁ i) * (m₂ i/m₁ i)
  have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq t U V
  have eUV : ∑ i ∈ t, U i*V i = ∑ i ∈ t, w i*m₂ i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hnonneg : 0 ≤ w i*m₁ i := mul_nonneg (hw i hi) (hm₁ i hi).le
    dsimp [U, V]
    rw [← mul_assoc, Real.mul_self_sqrt hnonneg]
    field_simp [(hm₁ i hi).ne']
  have eU : ∑ i ∈ t, (U i)^2 = ∑ i ∈ t, w i*m₁ i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (mul_nonneg (hw i hi) (hm₁ i hi).le)
  have eV : ∑ i ∈ t, (V i)^2 = ∑ i ∈ t, w i*((m₂ i)^2/m₁ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hnonneg : 0 ≤ w i*m₁ i := mul_nonneg (hw i hi) (hm₁ i hi).le
    dsimp [V]
    rw [mul_pow, Real.sq_sqrt hnonneg]
    field_simp [(hm₁ i hi).ne']
  rw [eUV, eU, eV] at hcs0
  have hcpos : (0 : ℝ) < s+2 := by positivity
  have hdpos : (0 : ℝ) < s+1 := by positivity
  have hdiv : ∀ i ∈ t, (s+2)*((m₂ i)^2/m₁ i) ≤ (s+1)*m₃ i := by
    intro i hi
    have hc := hcomp i hi
    unfold gap at hc
    calc
      (s+2)*((m₂ i)^2/m₁ i) = ((s+2)*(m₂ i)^2)/m₁ i := by ring
      _ ≤ (s+1)*m₃ i := (div_le_iff₀ (hm₁ i hi)).mpr (by nlinarith)
  intro i hi hwi
  have hM1pos : 0 < ∑ j ∈ t, w j*m₁ j := by
    have hiterm : 0 < w i*m₁ i := mul_pos hwi (hm₁ i hi)
    have hle : w i*m₁ i ≤ ∑ j ∈ t, w j*m₁ j := by
      apply Finset.single_le_sum (fun j hj => mul_nonneg (hw j hj) (hm₁ j hj).le) hi
    exact lt_of_lt_of_le hiterm hle
  have hsumdiv : (s+2)*(∑ j ∈ t, w j*((m₂ j)^2/m₁ j)) ≤
      (s+1)*(∑ j ∈ t, w j*m₃ j) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    convert mul_le_mul_of_nonneg_left (hdiv j hj) (hw j hj) using 1 <;> ring
  have hsumdiv_eq : (s+2)*(∑ j ∈ t, w j*((m₂ j)^2/m₁ j)) =
      (s+1)*(∑ j ∈ t, w j*m₃ j) := by
    by_contra hne
    have hlt : (s+2)*(∑ j ∈ t, w j*((m₂ j)^2/m₁ j)) <
        (s+1)*(∑ j ∈ t, w j*m₃ j) := lt_of_le_of_ne hsumdiv hne
    have hcs : (s+2)*(∑ j ∈ t, w j*m₂ j)^2 ≤
        (s+2)*((∑ j ∈ t, w j*m₁ j) *
          (∑ j ∈ t, w j*((m₂ j)^2/m₁ j))) :=
      mul_le_mul_of_nonneg_left hcs0 hcpos.le
    have hprodlt :
        (∑ j ∈ t, w j*m₁ j) *
            ((s+2)*(∑ j ∈ t, w j*((m₂ j)^2/m₁ j))) <
          (∑ j ∈ t, w j*m₁ j) *
            ((s+1)*(∑ j ∈ t, w j*m₃ j)) :=
      mul_lt_mul_of_pos_left hlt hM1pos
    unfold gap at heq
    nlinarith
  have hterm : ∀ j ∈ t,
      0 ≤ w j * ((s+1)*m₃ j - (s+2)*((m₂ j)^2/m₁ j)) := by
    intro j hj
    exact mul_nonneg (hw j hj) (sub_nonneg.mpr (hdiv j hj))
  have hsumzero : ∑ j ∈ t,
      w j * ((s+1)*m₃ j - (s+2)*((m₂ j)^2/m₁ j)) = 0 := by
    calc
      _ = (s+1)*(∑ j ∈ t, w j*m₃ j)
          - (s+2)*(∑ j ∈ t, w j*((m₂ j)^2/m₁ j)) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = 0 := by linarith
  have hizero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsumzero i hi
  have hdef : (s+1)*m₃ i - (s+2)*((m₂ i)^2/m₁ i) = 0 :=
    (mul_eq_zero.mp hizero).resolve_left hwi.ne'
  unfold gap
  field_simp [(hm₁ i hi).ne'] at hdef
  nlinarith

end SSP.K2AllStages

namespace SSP.K2Concrete

open Finset

/-- Equality in the cleared two-cycle resolvent inequality forces the unique sharp routing:
no back edge, certain forward continuation, and equal exit rates. -/
theorem twoCycleClosed_sharp (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hδ : a * b * (1 - u * v) ≠ 0)
    (hsharp :
      18 * ((b + a * u) / (a * b * (1-u*v))) *
          ((b * (b * (b + a*u) + a*u*(b*v+a))
              + a*u*(b*v*(b+a*u) + a*(b*v+a))) /
            (a*b*(1-u*v))^3)
        - 16 * ((b*(b+a*u) + a*u*(b*v+a)) / (a*b*(1-u*v))^2)^2 = 0) :
    v = 0 ∧ u = 1 ∧ a = b := by
  have h1uv : 1-u*v ≠ 0 := by
    intro h
    apply hδ
    rw [h]
    ring
  have hid : (a*b*(1-u*v))^4 *
      (18 * ((b + a*u) / (a*b*(1-u*v))) *
          ((b * (b * (b+a*u) + a*u*(b*v+a))
              + a*u*(b*v*(b+a*u) + a*(b*v+a))) /
            (a*b*(1-u*v))^3)
        - 16 * ((b*(b+a*u) + a*u*(b*v+a)) / (a*b*(1-u*v))^2)^2)
      = 2 * SSP.Chain.cyc2N a b u v := by
    field_simp [h1uv, ha.ne', hb.ne']
    unfold SSP.Chain.cyc2N
    ring
  have hpoly : SSP.Chain.cyc2N a b u v = 0 := by
    rw [hsharp] at hid
    linarith
  exact (SSP.Chain.cyc2N_eq_zero_iff a b u v ha hb hu0 hu1 hv0 hv1).mp hpoly

set_option maxHeartbeats 1000000 in
-- Symbolic normalization of three products of a general `2 × 2` inverse is expensive.
/-- A sharp two-cycle law started at state zero has the first three moments of a two-stage
Erlang law.  This is the equality companion to `twoCycleMatrixStartZero`. -/
theorem twoCycleMatrixStartZero_equality_moments
    (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hδ : a * b * (1-u*v) ≠ 0) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![a, -a*u; -b*v, b]
    let N := A⁻¹
    SSP.K2AllStages.gap 2
        (N.mulVec (fun _ => (1 : ℝ)) 0)
        (2 * N.mulVec (N.mulVec (fun _ => (1 : ℝ))) 0)
        (6 * N.mulVec (N.mulVec (N.mulVec (fun _ => (1 : ℝ)))) 0) = 0 →
      ∃ θ : ℝ, 0 < θ ∧
        N.mulVec (fun _ => (1 : ℝ)) 0 =
          SSP.K2AllStages.erlangMixMoment 2 1 θ 1 ∧
        2 * N.mulVec (N.mulVec (fun _ => (1 : ℝ))) 0 =
          SSP.K2AllStages.erlangMixMoment 2 1 θ 2 ∧
        6 * N.mulVec (N.mulVec (N.mulVec (fun _ => (1 : ℝ)))) 0 =
          SSP.K2AllStages.erlangMixMoment 2 1 θ 3 := by
  dsimp only
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![a, -a*u; -b*v, b]
  have hn : A⁻¹ =
      !![b/(a*b*(1-u*v)), (a*u)/(a*b*(1-u*v));
          (b*v)/(a*b*(1-u*v)), a/(a*b*(1-u*v))] := by
    dsimp [A]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two,
        Ring.inverse_eq_inv] <;> field_simp [hδ]
  have hz1 : (A⁻¹.mulVec (fun _ => (1 : ℝ))) 0 =
      (b+a*u)/(a*b*(1-u*v)) := by
    rw [hn]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hz2 : (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ)))) 0 =
      (b*(b+a*u) + a*u*(b*v+a))/(a*b*(1-u*v))^2 := by
    rw [hn]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [hδ]
  have hz3 : (A⁻¹.mulVec (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ))))) 0 =
      (b*(b*(b+a*u) + a*u*(b*v+a))
          + a*u*(b*v*(b+a*u) + a*(b*v+a))) /
        (a*b*(1-u*v))^3 := by
    rw [hn]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [hδ]
  intro hsharp
  have hscalar :
      18 * ((b+a*u)/(a*b*(1-u*v))) *
          ((b*(b*(b+a*u) + a*u*(b*v+a))
              + a*u*(b*v*(b+a*u) + a*(b*v+a))) /
            (a*b*(1-u*v))^3)
        - 16 * ((b*(b+a*u) + a*u*(b*v+a))/(a*b*(1-u*v))^2)^2 = 0 := by
    unfold SSP.K2AllStages.gap at hsharp
    rw [hz1, hz2, hz3] at hsharp
    norm_num at hsharp
    nlinarith
  rcases twoCycleClosed_sharp a b u v ha hb hu0 hu1 hv0 hv1 hδ hscalar with
    ⟨rfl, rfl, rfl⟩
  refine ⟨1/a, by positivity, ?_, ?_, ?_⟩
  · rw [hz1]
    norm_num [SSP.K2AllStages.erlangMixMoment]
    field_simp [ha.ne']
    norm_num
  · rw [hz2]
    norm_num [SSP.K2AllStages.erlangMixMoment]
    field_simp [ha.ne']
    ring
  · rw [hz3]
    norm_num [SSP.K2AllStages.erlangMixMoment]
    field_simp [ha.ne']
    ring

set_option maxHeartbeats 1000000 in
-- Symbolic normalization of three products of a general `2 × 2` inverse is expensive.
/-- The symmetric equality statement for a two-cycle law started at state one. -/
theorem twoCycleMatrixStartOne_equality_moments
    (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hδ : a * b * (1-u*v) ≠ 0) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![a, -a*u; -b*v, b]
    let N := A⁻¹
    SSP.K2AllStages.gap 2
        (N.mulVec (fun _ => (1 : ℝ)) 1)
        (2 * N.mulVec (N.mulVec (fun _ => (1 : ℝ))) 1)
        (6 * N.mulVec (N.mulVec (N.mulVec (fun _ => (1 : ℝ)))) 1) = 0 →
      ∃ θ : ℝ, 0 < θ ∧
        N.mulVec (fun _ => (1 : ℝ)) 1 =
          SSP.K2AllStages.erlangMixMoment 2 1 θ 1 ∧
        2 * N.mulVec (N.mulVec (fun _ => (1 : ℝ))) 1 =
          SSP.K2AllStages.erlangMixMoment 2 1 θ 2 ∧
        6 * N.mulVec (N.mulVec (N.mulVec (fun _ => (1 : ℝ)))) 1 =
          SSP.K2AllStages.erlangMixMoment 2 1 θ 3 := by
  dsimp only
  have hδ' : b*a*(1-v*u) ≠ 0 := by
    intro h
    apply hδ
    nlinarith
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![a, -a*u; -b*v, b]
  have hn : A⁻¹ =
      !![b/(a*b*(1-u*v)), (a*u)/(a*b*(1-u*v));
          (b*v)/(a*b*(1-u*v)), a/(a*b*(1-u*v))] := by
    dsimp [A]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two,
        Ring.inverse_eq_inv] <;> field_simp [hδ]
  have hz1 : (A⁻¹.mulVec (fun _ => (1 : ℝ))) 1 =
      (a+b*v)/(b*a*(1-v*u)) := by
    rw [hn]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [hδ, hδ']
    ring
  have hz2 : (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ)))) 1 =
      (a*(a+b*v) + b*v*(a*u+b))/(b*a*(1-v*u))^2 := by
    rw [hn]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [hδ, hδ']
    ring
  have hz3 : (A⁻¹.mulVec (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ))))) 1 =
      (a*(a*(a+b*v) + b*v*(a*u+b))
          + b*v*(a*u*(a+b*v) + b*(a*u+b))) /
        (b*a*(1-v*u))^3 := by
    rw [hn]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [hδ, hδ']
    ring
  intro hsharp
  have hscalar :
      18 * ((a+b*v)/(b*a*(1-v*u))) *
          ((a*(a*(a+b*v) + b*v*(a*u+b))
              + b*v*(a*u*(a+b*v) + b*(a*u+b))) /
            (b*a*(1-v*u))^3)
        - 16 * ((a*(a+b*v) + b*v*(a*u+b))/(b*a*(1-v*u))^2)^2 = 0 := by
    unfold SSP.K2AllStages.gap at hsharp
    rw [hz1, hz2, hz3] at hsharp
    norm_num at hsharp
    nlinarith
  rcases twoCycleClosed_sharp b a v u hb ha hv0 hv1 hu0 hu1 hδ' hscalar with
    ⟨rfl, rfl, rfl⟩
  refine ⟨1/b, by positivity, ?_, ?_, ?_⟩
  · rw [hz1]
    norm_num [SSP.K2AllStages.erlangMixMoment]
    field_simp [hb.ne']
    norm_num
  · rw [hz2]
    norm_num [SSP.K2AllStages.erlangMixMoment]
    field_simp [hb.ne']
    ring
  · rw [hz3]
    norm_num [SSP.K2AllStages.erlangMixMoment]
    field_simp [hb.ne']
    ring

/-- The general transient state-return decomposition, specialized to three states. -/
noncomputable def generalTransientStateReturnDataThree (X : TransientStart 3) :
    TransientStateReturnData 3 X := by
  have hn2 : 2 ≤ 3 := by omega
  by_cases hp : 0 < transientReturnProbability X
  · refine
      { su := 2
        sv := 2
        su_pos := by omega
        sv_pos := by omega
        su_lt := by omega
        sv_lt := by omega
        U := transientReturnConditionedInitial X hn2 hp
        V := transientTerminalConditionedInitial X hn2 (transientTerminalProbability_pos X)
        x := transientHoldingMean X
        p := transientReturnProbability X
        q := transientTerminalProbability X
        x_pos := transientHoldingMean_pos X
        p_nonneg := transientReturnProbability_nonneg X
        q_pos := transientTerminalProbability_pos X
        prob_sum := transientReturnProbability_add_terminalProbability X
        return_weight_pos := by
          rw [transientReturnConditionedInitial_weight_sum X hn2 hp]
          norm_num
        moment1_decomp := transientMoment1_renewal_of_return_pos X hn2 hp
        moment2_decomp := transientMoment2_renewal_of_return_pos X hn2 hp
        moment3_decomp := transientMoment3_renewal_of_return_pos X hn2 hp }
  · have hp0 : transientReturnProbability X = 0 :=
      le_antisymm (not_lt.mp hp) (transientReturnProbability_nonneg X)
    let U := pureTransientInitial (transientReturnConditionedStart X ⟨0, by omega⟩)
    have hm := transient_renewal_moments_of_return_zero X hn2 hp0 U
    refine
      { su := 2
        sv := 2
        su_pos := by omega
        sv_pos := by omega
        su_lt := by omega
        sv_lt := by omega
        U := U
        V := transientTerminalConditionedInitial X hn2 (transientTerminalProbability_pos X)
        x := transientHoldingMean X
        p := transientReturnProbability X
        q := transientTerminalProbability X
        x_pos := transientHoldingMean_pos X
        p_nonneg := transientReturnProbability_nonneg X
        q_pos := transientTerminalProbability_pos X
        prob_sum := transientReturnProbability_add_terminalProbability X
        return_weight_pos := by
          dsimp [U]
          simp [pureTransientInitial]
        moment1_decomp := hm.1
        moment2_decomp := hm.2.1
        moment3_decomp := hm.2.2 }

/-- One direct renewal step at order three. -/
theorem transientStageBound_three_of_state_return {X : TransientStart 3}
    (d : TransientStateReturnData 3 X)
    (hU0 : SSP.K2AllStages.StageBound d.su
      (transientInitialMoment1 d.su d.U) (transientInitialMoment2 d.su d.U)
      (transientInitialMoment3 d.su d.U))
    (hV0 : SSP.K2AllStages.StageBound d.sv
      (transientInitialMoment1 d.sv d.V) (transientInitialMoment2 d.sv d.V)
      (transientInitialMoment3 d.sv d.V)) :
    SSP.K2AllStages.StageBound 3
      (transientMoment1 3 X) (transientMoment2 3 X) (transientMoment3 3 X) := by
  have hsuN : d.su ≤ 2 := by have := d.su_lt; omega
  have hsvN : d.sv ≤ 2 := by have := d.sv_lt; omega
  have hU := SSP.K2AllStages.stageBound_mono d.su_pos hsuN
    (transientInitialMoment1_nonneg d.U) (transientInitialMoment2_nonneg d.U)
    (transientInitialMoment3_nonneg d.U) hU0
  have hV := SSP.K2AllStages.stageBound_mono d.sv_pos hsvN
    (transientInitialMoment1_nonneg d.V) (transientInitialMoment2_nonneg d.V)
    (transientInitialMoment3_nonneg d.V) hV0
  have hUc : 4*(transientInitialMoment2 d.su d.U)^2 ≤
      3*transientInitialMoment1 d.su d.U*transientInitialMoment3 d.su d.U := by
    unfold SSP.K2AllStages.StageBound at hU
    norm_num at hU
    nlinarith
  have hVc : 4*(transientInitialMoment2 d.sv d.V)^2 ≤
      3*transientInitialMoment1 d.sv d.V*transientInitialMoment3 d.sv d.V := by
    unfold SSP.K2AllStages.StageBound at hV
    norm_num at hV
    nlinarith
  have hASU := transientInitialAldousSheppForParent d.su_pos d.su_lt d.U
  have hASV := transientInitialAldousSheppForParent d.sv_pos d.sv_lt d.V
  norm_num at hASU hASV
  have hreturn : 0 < transientInitialMoment1 d.su d.U :=
    transientInitialMoment1_pos_of_weight_sum_pos d.U d.return_weight_pos
  rcases eq_or_lt_of_le d.p_nonneg with hp0 | hp0
  · have hq1 : d.q=1 := by linarith [d.prob_sum]
    rcases eq_or_lt_of_le (transientInitialMoment1_nonneg d.V) with hv0 | hv0
    · have hv23 := transientInitial_higher_moments_eq_zero_of_moment1_eq_zero d.V hv0.symm
      have hstrict := SSP.K2AllStages.no_return_atom_strict 3 (by omega) d.x d.x_pos
      unfold SSP.K2AllStages.StageBound
      rw [d.moment1_decomp, d.moment2_decomp, d.moment3_decomp,
        ← hp0, hq1, ← hv0, hv23.1, hv23.2]
      simpa [SSP.K2AllStages.renewalM1, SSP.K2AllStages.renewalM2,
        SSP.K2AllStages.renewalM3, SSP.K2AllStages.renewalX1,
        SSP.K2AllStages.renewalX2, SSP.K2AllStages.renewalX3,
        SSP.K2AllStages.kernelM1, SSP.K2AllStages.kernelM2,
        SSP.K2AllStages.kernelM3] using le_of_lt hstrict
    · have hnr := SSP.K2AllStages.no_return_moment_inequality_three d.x
        (transientInitialMoment1 d.sv d.V) (transientInitialMoment2 d.sv d.V)
        (transientInitialMoment3 d.sv d.V) d.x_pos hv0 hASV hVc
      unfold SSP.K2AllStages.StageBound
      rw [d.moment1_decomp, d.moment2_decomp, d.moment3_decomp, ← hp0, hq1]
      norm_num
      simpa [SSP.K2AllStages.renewalM1, SSP.K2AllStages.renewalM2,
        SSP.K2AllStages.renewalM3, SSP.K2AllStages.renewalX1,
        SSP.K2AllStages.renewalX2, SSP.K2AllStages.renewalX3,
        SSP.K2AllStages.kernelM1, SSP.K2AllStages.kernelM2,
        SSP.K2AllStages.kernelM3] using hnr
  · rcases eq_or_lt_of_le (transientInitialMoment1_nonneg d.V) with hv0 | hv0
    · have hv23 := transientInitial_higher_moments_eq_zero_of_moment1_eq_zero d.V hv0.symm
      have hgap := SSP.K2AllStages.renewalGap_vzero_three_nonneg d.x
        (transientInitialMoment1 d.su d.U) d.p d.q
        (transientInitialMoment2 d.su d.U) (transientInitialMoment3 d.su d.U)
        d.x_pos hreturn hp0 d.q_pos d.prob_sum hASU hUc
      unfold SSP.K2AllStages.StageBound
      rw [d.moment1_decomp, d.moment2_decomp, d.moment3_decomp, ← hv0, hv23.1, hv23.2]
      have hunscale := SSP.K2AllStages.renewalGap_unscale 3 d.x
        (transientInitialMoment1 d.su d.U) 0 d.p d.q
        (transientInitialMoment2 d.su d.U) 0
        (transientInitialMoment3 d.su d.U) 0 (ne_of_gt d.q_pos)
      unfold SSP.K2AllStages.gap at hunscale
      have hscaled : 0 ≤ SSP.K2AllStages.renewalGap 3 d.x
          (transientInitialMoment1 d.su d.U) 0 d.p d.q
          (transientInitialMoment2 d.su d.U) 0
          (transientInitialMoment3 d.su d.U) 0/d.q^4 :=
        div_nonneg hgap (by positivity)
      norm_num at hunscale ⊢
      linarith
    · have hmain := SSP.K2AllStages.renewal_moment_inequality_three d.x
        (transientInitialMoment1 d.su d.U) (transientInitialMoment1 d.sv d.V) d.p d.q
        (transientInitialMoment2 d.su d.U) (transientInitialMoment2 d.sv d.V)
        (transientInitialMoment3 d.su d.U) (transientInitialMoment3 d.sv d.V)
        d.x_pos hreturn hv0 hp0 d.q_pos d.prob_sum hASU hASV hUc hVc
      unfold SSP.K2AllStages.StageBound
      norm_num
      rwa [d.moment1_decomp, d.moment2_decomp, d.moment3_decomp]

/-- Equality in a three-state renewal step forces no return, sharp terminal second and third
moments, and the Erlang mean-matching relation. -/
theorem transient_three_equality_of_state_return {X : TransientStart 3}
    (d : TransientStateReturnData 3 X)
    (hU0 : SSP.K2AllStages.StageBound d.su
      (transientInitialMoment1 d.su d.U) (transientInitialMoment2 d.su d.U)
      (transientInitialMoment3 d.su d.U))
    (hV0 : SSP.K2AllStages.StageBound d.sv
      (transientInitialMoment1 d.sv d.V) (transientInitialMoment2 d.sv d.V)
      (transientInitialMoment3 d.sv d.V))
    (heq : SSP.K2AllStages.gap 3 (transientMoment1 3 X)
      (transientMoment2 3 X) (transientMoment3 3 X) = 0) :
    d.p = 0 ∧
      transientInitialMoment2 d.sv d.V =
        (3:ℝ)/2*(transientInitialMoment1 d.sv d.V)^2 ∧
      transientInitialMoment3 d.sv d.V =
        (4:ℝ)/3*(transientInitialMoment2 d.sv d.V)^2 /
          transientInitialMoment1 d.sv d.V ∧
      transientInitialMoment1 d.sv d.V = 2*d.x := by
  have hsuN : d.su ≤ 2 := by have := d.su_lt; omega
  have hsvN : d.sv ≤ 2 := by have := d.sv_lt; omega
  have hU := SSP.K2AllStages.stageBound_mono d.su_pos hsuN
    (transientInitialMoment1_nonneg d.U) (transientInitialMoment2_nonneg d.U)
    (transientInitialMoment3_nonneg d.U) hU0
  have hV := SSP.K2AllStages.stageBound_mono d.sv_pos hsvN
    (transientInitialMoment1_nonneg d.V) (transientInitialMoment2_nonneg d.V)
    (transientInitialMoment3_nonneg d.V) hV0
  have hUc : 4*(transientInitialMoment2 d.su d.U)^2 ≤
      3*transientInitialMoment1 d.su d.U*transientInitialMoment3 d.su d.U := by
    unfold SSP.K2AllStages.StageBound at hU
    norm_num at hU
    nlinarith
  have hVc : 4*(transientInitialMoment2 d.sv d.V)^2 ≤
      3*transientInitialMoment1 d.sv d.V*transientInitialMoment3 d.sv d.V := by
    unfold SSP.K2AllStages.StageBound at hV
    norm_num at hV
    nlinarith
  have hASU := transientInitialAldousSheppForParent d.su_pos d.su_lt d.U
  have hASV := transientInitialAldousSheppForParent d.sv_pos d.sv_lt d.V
  norm_num at hASU hASV
  have hreturn : 0 < d.p → 0 < transientInitialMoment1 d.su d.U := by
    intro _
    exact transientInitialMoment1_pos_of_weight_sum_pos d.U d.return_weight_pos
  have hvzero : transientInitialMoment1 d.sv d.V = 0 →
      transientInitialMoment2 d.sv d.V = 0 ∧ transientInitialMoment3 d.sv d.V = 0 :=
    fun h => transientInitial_higher_moments_eq_zero_of_moment1_eq_zero d.V h
  have hrenew := SSP.K2AllStages.renewal_equality_three_iff d.x
    (transientInitialMoment1 d.su d.U) (transientInitialMoment1 d.sv d.V) d.p d.q
    (transientInitialMoment2 d.su d.U) (transientInitialMoment2 d.sv d.V)
    (transientInitialMoment3 d.su d.U) (transientInitialMoment3 d.sv d.V)
    d.x_pos (transientInitialMoment1_nonneg d.U) (transientInitialMoment1_nonneg d.V)
    d.p_nonneg d.q_pos d.prob_sum hreturn hvzero hASU hASV hUc hVc
  apply hrenew.mp
  rwa [d.moment1_decomp, d.moment2_decomp, d.moment3_decomp] at heq

/-- The `s = 3`, `k = 2` inequality for every deterministic transient start, proved directly
from the order-two theorem and the three-state semialgebraic renewal certificate. -/
theorem transientInitialStageBound_lt_three {s : ℕ}
    (hs0 : 1 ≤ s) (hs3 : s < 3) (X : TransientInitial s) :
    SSP.K2AllStages.StageBound s
      (transientInitialMoment1 s X) (transientInitialMoment2 s X)
      (transientInitialMoment3 s X) := by
  interval_cases s
  · exact transientInitialStageBound_one X
  · exact transientInitialStageBound_two X

theorem transientStageBound_three_direct (X : TransientStart 3) :
    SSP.K2AllStages.StageBound 3
      (transientMoment1 3 X) (transientMoment2 3 X) (transientMoment3 3 X) := by
  let d := generalTransientStateReturnDataThree X
  have hU : SSP.K2AllStages.StageBound d.su
      (transientInitialMoment1 d.su d.U) (transientInitialMoment2 d.su d.U)
      (transientInitialMoment3 d.su d.U) := by
    exact transientInitialStageBound_lt_three d.su_pos d.su_lt d.U
  have hV : SSP.K2AllStages.StageBound d.sv
      (transientInitialMoment1 d.sv d.V) (transientInitialMoment2 d.sv d.V)
      (transientInitialMoment3 d.sv d.V) := by
    exact transientInitialStageBound_lt_three d.sv_pos d.sv_lt d.V
  exact transientStageBound_three_of_state_return d hU hV

/-- Every one-state transient law is exponential, independently of the equality hypothesis. -/
theorem transientStageBound_one_equality_moments (X : TransientStart 1) :
    ∃ θ : ℝ, 0 < θ ∧
      transientMoment1 1 X = SSP.K2AllStages.erlangMixMoment 1 1 θ 1 ∧
      transientMoment2 1 X = SSP.K2AllStages.erlangMixMoment 1 1 θ 2 ∧
      transientMoment3 1 X = SSP.K2AllStages.erlangMixMoment 1 1 θ 3 := by
  refine ⟨transientMoment1 1 X, transientMoment1_pos X, ?_, ?_, ?_⟩
  · norm_num [SSP.K2AllStages.erlangMixMoment]
  · have hi : X.i = (0 : Fin 1) := Subsingleton.elim _ _
    unfold SSP.K2AllStages.erlangMixMoment transientMoment1 transientMoment2
    rw [hi]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, mul_one]
    ring
  · have hi : X.i = (0 : Fin 1) := Subsingleton.elim _ _
    unfold SSP.K2AllStages.erlangMixMoment transientMoment1 transientMoment3
    rw [hi]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, mul_one]
    ring

/-- Every sharp deterministic two-state transient law has the first three moments of a
two-stage Erlang law. -/
theorem transientStageBound_two_equality_moments (X : TransientStart 2)
    (hsharp : SSP.K2AllStages.gap 2 (transientMoment1 2 X)
      (transientMoment2 2 X) (transientMoment3 2 X) = 0) :
    ∃ θ : ℝ, 0 < θ ∧
      transientMoment1 2 X = SSP.K2AllStages.erlangMixMoment 2 1 θ 1 ∧
      transientMoment2 2 X = SSP.K2AllStages.erlangMixMoment 2 1 θ 2 ∧
      transientMoment3 2 X = SSP.K2AllStages.erlangMixMoment 2 1 θ 3 := by
  let a := 1-X.Q 0 0
  let b := 1-X.Q 1 1
  let u := X.Q 0 1/a
  let v := X.Q 1 0/b
  have hrow0 := X.hrow (0 : Fin 2)
  have hrow1 := X.hrow (1 : Fin 2)
  rw [Fin.sum_univ_two] at hrow0 hrow1
  have hca : X.Q 0 1 ≤ a := by dsimp [a]; linarith
  have hdb : X.Q 1 0 ≤ b := by dsimp [b]; linarith
  have ha0 : 0 ≤ a := (X.hQ 0 1).trans hca
  have hb0 : 0 ≤ b := (X.hQ 1 0).trans hdb
  have hdetunit := (Matrix.isUnit_iff_isUnit_det _).mp X.hu
  have ha : 0 < a := by
    rcases eq_or_lt_of_le ha0 with ha' | ha'
    · exfalso
      have hc : X.Q 0 1 = 0 := by
        rw [← ha'] at hca
        exact le_antisymm hca (X.hQ 0 1)
      apply hdetunit.ne_zero
      rw [Matrix.det_fin_two]
      simp only [Matrix.sub_apply, Matrix.one_apply]
      norm_num
      rw [show 1-X.Q 0 0=0 from ha'.symm, hc]
      ring
    · exact ha'
  have hb : 0 < b := by
    rcases eq_or_lt_of_le hb0 with hb' | hb'
    · exfalso
      have hd : X.Q 1 0 = 0 := by
        rw [← hb'] at hdb
        exact le_antisymm hdb (X.hQ 1 0)
      apply hdetunit.ne_zero
      rw [Matrix.det_fin_two]
      simp only [Matrix.sub_apply, Matrix.one_apply]
      norm_num
      rw [show 1-X.Q 1 1=0 from hb'.symm, hd]
      ring
    · exact hb'
  have hu0 : 0 ≤ u := div_nonneg (X.hQ 0 1) ha.le
  have hu1 : u ≤ 1 := (div_le_one ha).mpr hca
  have hv0 : 0 ≤ v := div_nonneg (X.hQ 1 0) hb.le
  have hv1 : v ≤ 1 := (div_le_one hb).mpr hdb
  have hau : a*u = X.Q 0 1 := by dsimp [u]; field_simp [ha.ne']
  have hbv : b*v = X.Q 1 0 := by dsimp [v]; field_simp [hb.ne']
  have hA : 1-X.Q = (!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [a, Matrix.sub_apply]
    · simp only [Matrix.sub_apply, Matrix.one_apply]
      norm_num
      rw [hau]
    · simp only [Matrix.sub_apply, Matrix.one_apply]
      norm_num
      rw [hbv]
    · simp [b, Matrix.sub_apply]
  have hδ : a*b*(1-u*v) ≠ 0 := by
    intro hz
    apply hdetunit.ne_zero
    rw [hA, Matrix.det_fin_two]
    norm_num
    calc a*b-a*u*(b*v) = a*b*(1-u*v) := by ring
      _ = 0 := hz
  have hzero := twoCycleMatrixStartZero_equality_moments
    a b u v ha hb hu0 hu1 hv0 hv1 hδ
  have hone := twoCycleMatrixStartOne_equality_moments
    a b u v ha hb hu0 hu1 hv0 hv1 hδ
  unfold transientMoment1 transientMoment2 transientMoment3 at hsharp ⊢
  rw [hA] at hsharp ⊢
  generalize hk : X.i = k at hsharp ⊢
  fin_cases k
  · simpa only [Fin.zero_eta] using hzero hsharp
  · simpa only [Fin.mk_one] using hone hsharp

/-- Concrete sharpness data for a three-state transient start attaining equality. -/
theorem transientStageBound_three_direct_equality (X : TransientStart 3)
    (heq : SSP.K2AllStages.gap 3 (transientMoment1 3 X)
      (transientMoment2 3 X) (transientMoment3 3 X) = 0) :
    let d := generalTransientStateReturnDataThree X
    d.p = 0 ∧
      transientInitialMoment2 d.sv d.V =
        (3:ℝ)/2*(transientInitialMoment1 d.sv d.V)^2 ∧
      transientInitialMoment3 d.sv d.V =
        (4:ℝ)/3*(transientInitialMoment2 d.sv d.V)^2 /
          transientInitialMoment1 d.sv d.V ∧
      transientInitialMoment1 d.sv d.V = 2*d.x := by
  dsimp only
  let d := generalTransientStateReturnDataThree X
  have hU : SSP.K2AllStages.StageBound d.su
      (transientInitialMoment1 d.su d.U) (transientInitialMoment2 d.su d.U)
      (transientInitialMoment3 d.su d.U) :=
    transientInitialStageBound_lt_three d.su_pos d.su_lt d.U
  have hV : SSP.K2AllStages.StageBound d.sv
      (transientInitialMoment1 d.sv d.V) (transientInitialMoment2 d.sv d.V)
      (transientInitialMoment3 d.sv d.V) :=
    transientInitialStageBound_lt_three d.sv_pos d.sv_lt d.V
  exact transient_three_equality_of_state_return d hU hV heq

/-- Every sharp deterministic three-state law has exactly the first three moments of an
Erlang law with three equal stages. -/
theorem transientStageBound_three_equality_moments (X : TransientStart 3)
    (heq : SSP.K2AllStages.gap 3 (transientMoment1 3 X)
      (transientMoment2 3 X) (transientMoment3 3 X) = 0) :
    ∃ θ : ℝ, 0 < θ ∧
      transientMoment1 3 X = SSP.K2AllStages.erlangMixMoment 3 1 θ 1 ∧
      transientMoment2 3 X = SSP.K2AllStages.erlangMixMoment 3 1 θ 2 ∧
      transientMoment3 3 X = SSP.K2AllStages.erlangMixMoment 3 1 θ 3 := by
  let d := generalTransientStateReturnDataThree X
  have hsharp := transientStageBound_three_direct_equality X heq
  change d.p = 0 ∧
      transientInitialMoment2 d.sv d.V =
        (3:ℝ)/2*(transientInitialMoment1 d.sv d.V)^2 ∧
      transientInitialMoment3 d.sv d.V =
        (4:ℝ)/3*(transientInitialMoment2 d.sv d.V)^2 /
          transientInitialMoment1 d.sv d.V ∧
      transientInitialMoment1 d.sv d.V = 2*d.x at hsharp
  rcases hsharp with ⟨hp, hB, hD, hv⟩
  have hq : d.q = 1 := by linarith [d.prob_sum]
  have hx : 0 < d.x := d.x_pos
  have hB' : transientInitialMoment2 d.sv d.V = 6*d.x^2 := by
    rw [hB, hv]
    ring
  have hD' : transientInitialMoment3 d.sv d.V = 24*d.x^3 := by
    rw [hD, hB', hv]
    field_simp [ne_of_gt hx]
    ring
  refine ⟨d.x, hx, ?_, ?_, ?_⟩
  · rw [d.moment1_decomp, hp, hq, hv]
    norm_num [SSP.K2AllStages.renewalM1, SSP.K2AllStages.renewalX1,
      SSP.K2AllStages.kernelM1, SSP.K2AllStages.erlangMixMoment]
    ring
  · rw [d.moment2_decomp, hp, hq, hv, hB']
    norm_num [SSP.K2AllStages.renewalM2, SSP.K2AllStages.renewalX2,
      SSP.K2AllStages.kernelM1, SSP.K2AllStages.kernelM2,
      SSP.K2AllStages.erlangMixMoment]
    ring
  · rw [d.moment3_decomp, hp, hq, hv, hB', hD']
    norm_num [SSP.K2AllStages.renewalM3, SSP.K2AllStages.renewalX3,
      SSP.K2AllStages.kernelM1, SSP.K2AllStages.kernelM2,
      SSP.K2AllStages.kernelM3, SSP.K2AllStages.erlangMixMoment]
    ring

/-- The direct three-stage theorem in the original strict-contraction chart. -/
theorem stageBound_three_direct (X : AbsorptionStart 3) :
    SSP.K2AllStages.StageBound 3 (moment1 3 X) (moment2 3 X) (moment3 3 X) := by
  simpa only [toTransient_moment1, toTransient_moment2, toTransient_moment3] using
    transientStageBound_three_direct X.toTransient

/-- The direct three-stage theorem for an arbitrary subprobability initial distribution;
missing mass is the permitted atom at zero. -/
theorem initialStageBound_three_direct (X : AbsorptionInitial 3) :
    SSP.K2AllStages.StageBound 3
      (initialMoment1 3 X) (initialMoment2 3 X) (initialMoment3 3 X) := by
  exact initialStageBound_of_components X (fun i => stageBound_three_direct (X.component i))

/-- The complete deterministic-start induction with no order-three representation axiom. -/
theorem all_transient_starts_direct :
    ∀ n, 1 ≤ n → ∀ X : TransientStart n,
      SSP.K2AllStages.StageBound n
        (transientMoment1 n X) (transientMoment2 n X) (transientMoment3 n X) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hnpos X
      by_cases hn3 : n ≤ 3
      · have hs : n = 1 ∨ n = 2 ∨ n = 3 := by omega
        rcases hs with rfl | rfl | rfl
        · exact transientStageBound_one X
        · exact transientStageBound_two X
        · exact transientStageBound_three_direct X
      · have hn4 : 4 ≤ n := by omega
        let d := generalTransientStateReturnData hn4 X
        have hU : SSP.K2AllStages.StageBound d.su
            (transientInitialMoment1 d.su d.U) (transientInitialMoment2 d.su d.U)
            (transientInitialMoment3 d.su d.U) := by
          apply transientInitialStageBound_of_components
          intro i
          exact ih d.su d.su_lt d.su_pos (d.U.component i)
        have hV : SSP.K2AllStages.StageBound d.sv
            (transientInitialMoment1 d.sv d.V) (transientInitialMoment2 d.sv d.V)
            (transientInitialMoment3 d.sv d.V) := by
          apply transientInitialStageBound_of_components
          intro i
          exact ih d.sv d.sv_lt d.sv_pos (d.V.component i)
        exact transientStageBound_of_state_return hn4 d hU hV

/-- At every order at least four, equality for a deterministic start forces its first three
moments to be those of an `n`-stage Erlang law with a common stage mean. -/
theorem transient_equality_moments_of_four {n : ℕ} (hn : 4 ≤ n)
    (X : TransientStart n)
    (heq : SSP.K2AllStages.gap n (transientMoment1 n X)
      (transientMoment2 n X) (transientMoment3 n X) = 0) :
    ∃ θ : ℝ, 0 < θ ∧
      transientMoment1 n X = SSP.K2AllStages.erlangMixMoment n 1 θ 1 ∧
      transientMoment2 n X = SSP.K2AllStages.erlangMixMoment n 1 θ 2 ∧
      transientMoment3 n X = SSP.K2AllStages.erlangMixMoment n 1 θ 3 := by
  let d := generalTransientStateReturnData hn X
  have hU0 : SSP.K2AllStages.StageBound d.su
      (transientInitialMoment1 d.su d.U) (transientInitialMoment2 d.su d.U)
      (transientInitialMoment3 d.su d.U) := by
    apply transientInitialStageBound_of_components
    intro i
    exact all_transient_starts_direct d.su d.su_pos (d.U.component i)
  have hV0 : SSP.K2AllStages.StageBound d.sv
      (transientInitialMoment1 d.sv d.V) (transientInitialMoment2 d.sv d.V)
      (transientInitialMoment3 d.sv d.V) := by
    apply transientInitialStageBound_of_components
    intro i
    exact all_transient_starts_direct d.sv d.sv_pos (d.V.component i)
  have hsuN : d.su ≤ n-1 := Nat.le_sub_one_of_lt d.su_lt
  have hsvN : d.sv ≤ n-1 := Nat.le_sub_one_of_lt d.sv_lt
  have hU := SSP.K2AllStages.stageBound_mono d.su_pos hsuN
    (transientInitialMoment1_nonneg d.U) (transientInitialMoment2_nonneg d.U)
    (transientInitialMoment3_nonneg d.U) hU0
  have hV := SSP.K2AllStages.stageBound_mono d.sv_pos hsvN
    (transientInitialMoment1_nonneg d.V) (transientInitialMoment2_nonneg d.V)
    (transientInitialMoment3_nonneg d.V) hV0
  have hUc : (n+1)*(transientInitialMoment2 d.su d.U)^2 ≤
      (n:ℝ)*transientInitialMoment1 d.su d.U*transientInitialMoment3 d.su d.U := by
    unfold SSP.K2AllStages.StageBound at hU
    have hncast : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hncast] at hU
    norm_num at hU
    nlinarith
  have hVc : (n+1)*(transientInitialMoment2 d.sv d.V)^2 ≤
      (n:ℝ)*transientInitialMoment1 d.sv d.V*transientInitialMoment3 d.sv d.V := by
    unfold SSP.K2AllStages.StageBound at hV
    have hncast : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hncast] at hV
    norm_num at hV
    nlinarith
  have hASU := transientInitialAldousSheppForParent d.su_pos d.su_lt d.U
  have hASV := transientInitialAldousSheppForParent d.sv_pos d.sv_lt d.V
  have hreturn : 0 < d.p → 0 < transientInitialMoment1 d.su d.U := by
    intro _
    exact transientInitialMoment1_pos_of_weight_sum_pos d.U d.return_weight_pos
  have hvzero : transientInitialMoment1 d.sv d.V = 0 →
      transientInitialMoment2 d.sv d.V = 0 ∧ transientInitialMoment3 d.sv d.V = 0 :=
    fun h => transientInitial_higher_moments_eq_zero_of_moment1_eq_zero d.V h
  have hiff := SSP.K2AllStages.renewal_equality_iff n hn d.x
    (transientInitialMoment1 d.su d.U) (transientInitialMoment1 d.sv d.V) d.p d.q
    (transientInitialMoment2 d.su d.U) (transientInitialMoment2 d.sv d.V)
    (transientInitialMoment3 d.su d.U) (transientInitialMoment3 d.sv d.V)
    d.x_pos (transientInitialMoment1_nonneg d.U) (transientInitialMoment1_nonneg d.V)
    d.p_nonneg d.q_pos d.prob_sum hreturn hvzero hASU hASV hUc hVc
  have hrenew : SSP.K2AllStages.gap n
      (SSP.K2AllStages.renewalM1 d.x (transientInitialMoment1 d.su d.U)
        (transientInitialMoment1 d.sv d.V) d.p d.q)
      (SSP.K2AllStages.renewalM2 d.x (transientInitialMoment1 d.su d.U)
        (transientInitialMoment1 d.sv d.V) d.p d.q
        (transientInitialMoment2 d.su d.U) (transientInitialMoment2 d.sv d.V))
      (SSP.K2AllStages.renewalM3 d.x (transientInitialMoment1 d.su d.U)
        (transientInitialMoment1 d.sv d.V) d.p d.q
        (transientInitialMoment2 d.su d.U) (transientInitialMoment2 d.sv d.V)
        (transientInitialMoment3 d.su d.U) (transientInitialMoment3 d.sv d.V)) = 0 := by
    rwa [← d.moment1_decomp, ← d.moment2_decomp, ← d.moment3_decomp]
  rcases hiff.mp hrenew with ⟨hp, hB, hD, hv⟩
  have hq : d.q=1 := by linarith [d.prob_sum]
  have hnR : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hn1 : (n:ℝ)-1 ≠ 0 := by linarith
  have hx : 0 < d.x := d.x_pos
  have hB' : transientInitialMoment2 d.sv d.V =
      (n:ℝ)*(n-1)*d.x^2 := by
    rw [hB, hv]
    field_simp [hn1]
  have hD' : transientInitialMoment3 d.sv d.V =
      (n:ℝ)*(n+1)*(n-1)*d.x^3 := by
    rw [hD, hB', hv]
    field_simp [hn0, hn1, ne_of_gt hx]
  refine ⟨d.x, hx, ?_, ?_, ?_⟩
  · rw [d.moment1_decomp, hp, hq, hv]
    simp [SSP.K2AllStages.renewalM1, SSP.K2AllStages.renewalX1,
      SSP.K2AllStages.kernelM1, SSP.K2AllStages.erlangMixMoment]
    ring
  · rw [d.moment2_decomp, hp, hq, hv, hB']
    simp [SSP.K2AllStages.renewalM2, SSP.K2AllStages.renewalX2,
      SSP.K2AllStages.kernelM1, SSP.K2AllStages.kernelM2,
      SSP.K2AllStages.erlangMixMoment]
    ring
  · rw [d.moment3_decomp, hp, hq, hv, hB', hD']
    simp [SSP.K2AllStages.renewalM3, SSP.K2AllStages.renewalX3,
      SSP.K2AllStages.kernelM1, SSP.K2AllStages.kernelM2,
      SSP.K2AllStages.kernelM3, SSP.K2AllStages.erlangMixMoment]
    ring

/-- Uniform deterministic equality-moment classification from order three onward. -/
theorem transient_equality_moments_of_three {n : ℕ} (hn : 3 ≤ n)
    (X : TransientStart n)
    (heq : SSP.K2AllStages.gap n (transientMoment1 n X)
      (transientMoment2 n X) (transientMoment3 n X) = 0) :
    ∃ θ : ℝ, 0 < θ ∧
      transientMoment1 n X = SSP.K2AllStages.erlangMixMoment n 1 θ 1 ∧
      transientMoment2 n X = SSP.K2AllStages.erlangMixMoment n 1 θ 2 ∧
      transientMoment3 n X = SSP.K2AllStages.erlangMixMoment n 1 θ 3 := by
  rcases eq_or_lt_of_le hn with rfl | hn3
  · exact transientStageBound_three_equality_moments X heq
  · exact transient_equality_moments_of_four (by omega) X heq

/-- Uniform deterministic equality-moment classification at every positive order. -/
theorem transient_equality_moments {n : ℕ} (hn : 1 ≤ n)
    (X : TransientStart n)
    (heq : SSP.K2AllStages.gap n (transientMoment1 n X)
      (transientMoment2 n X) (transientMoment3 n X) = 0) :
    ∃ θ : ℝ, 0 < θ ∧
      transientMoment1 n X = SSP.K2AllStages.erlangMixMoment n 1 θ 1 ∧
      transientMoment2 n X = SSP.K2AllStages.erlangMixMoment n 1 θ 2 ∧
      transientMoment3 n X = SSP.K2AllStages.erlangMixMoment n 1 θ 3 := by
  by_cases hn3 : 3 ≤ n
  · exact transient_equality_moments_of_three hn3 X heq
  · have hs : n = 1 ∨ n = 2 := by omega
    rcases hs with rfl | rfl
    · exact transientStageBound_one_equality_moments X
    · exact transientStageBound_two_equality_moments X heq

/-- The direct all-stage inequality for the full transient class with a subprobability initial
vector.  Missing initial mass represents an atom at zero. -/
theorem all_transient_initial_laws_direct {s : ℕ} (hs : 1 ≤ s)
    (X : TransientInitial s) :
    SSP.K2AllStages.StageBound s
      (transientInitialMoment1 s X) (transientInitialMoment2 s X)
      (transientInitialMoment3 s X) := by
  apply transientInitialStageBound_of_components
  intro i
  exact all_transient_starts_direct s hs (X.component i)

/-- Equality classification on the full transient class: the first three moments are those of
an atom-at-zero mixture of a common-scale `s`-stage Erlang law. -/
theorem transientInitial_equality_moments_direct {s : ℕ} (hs : 1 ≤ s)
    (X : TransientInitial s)
    (heq : SSP.K2AllStages.gap s (transientInitialMoment1 s X)
      (transientInitialMoment2 s X) (transientInitialMoment3 s X) = 0) :
    ∃ w θ : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ 0 < θ ∧
      transientInitialMoment1 s X = SSP.K2AllStages.erlangMixMoment s w θ 1 ∧
      transientInitialMoment2 s X = SSP.K2AllStages.erlangMixMoment s w θ 2 ∧
      transientInitialMoment3 s X = SSP.K2AllStages.erlangMixMoment s w θ 3 := by
  classical
  have hcompgap : ∀ i : Fin s, 0 ≤ SSP.K2AllStages.gap s
      (transientMoment1 s (X.component i)) (transientMoment2 s (X.component i))
      (transientMoment3 s (X.component i)) := by
    intro i
    have hb := all_transient_starts_direct s hs (X.component i)
    unfold SSP.K2AllStages.StageBound at hb
    simpa only [SSP.K2AllStages.gap] using sub_nonneg.mpr hb
  have hcomponent : ∀ i : Fin s, 0 < X.weight i →
      SSP.K2AllStages.gap s (transientMoment1 s (X.component i))
        (transientMoment2 s (X.component i)) (transientMoment3 s (X.component i)) = 0 := by
    have h := SSP.K2AllStages.mixture_equality_component_gap s hs Finset.univ X.weight
      (fun i => transientMoment1 s (X.component i))
      (fun i => transientMoment2 s (X.component i))
      (fun i => transientMoment3 s (X.component i))
      (fun i _ => X.weight_nonneg i)
      (fun i _ => transientMoment1_pos (X.component i))
      (fun i _ => hcompgap i)
      (by simpa [transientInitialMoment1, transientInitialMoment2,
        transientInitialMoment3] using heq)
    simpa using h
  have hclass : ∀ i : Fin s, 0 < X.weight i →
      ∃ θ : ℝ, 0 < θ ∧
        transientMoment1 s (X.component i) =
          SSP.K2AllStages.erlangMixMoment s 1 θ 1 ∧
        transientMoment2 s (X.component i) =
          SSP.K2AllStages.erlangMixMoment s 1 θ 2 ∧
        transientMoment3 s (X.component i) =
          SSP.K2AllStages.erlangMixMoment s 1 θ 3 := by
    intro i hwi
    exact transient_equality_moments hs (X.component i) (hcomponent i hwi)
  let θ : Fin s → ℝ := fun i =>
    if h : 0 < X.weight i then Classical.choose (hclass i h) else 1
  have hθpos : ∀ i : Fin s, 0 < θ i := by
    intro i
    dsimp [θ]
    split
    · rename_i hwi
      exact (Classical.choose_spec (hclass i hwi)).1
    · norm_num
  have hmom : ∀ i : Fin s, 0 < X.weight i →
      transientMoment1 s (X.component i) =
        SSP.K2AllStages.erlangMixMoment s 1 (θ i) 1 ∧
      transientMoment2 s (X.component i) =
        SSP.K2AllStages.erlangMixMoment s 1 (θ i) 2 ∧
      transientMoment3 s (X.component i) =
        SSP.K2AllStages.erlangMixMoment s 1 (θ i) 3 := by
    intro i hwi
    dsimp [θ]
    rw [dif_pos hwi]
    exact (Classical.choose_spec (hclass i hwi)).2
  have hM1 : transientInitialMoment1 s X = ∑ i, X.weight i*s*(θ i) := by
    unfold transientInitialMoment1
    apply Finset.sum_congr rfl
    intro i hi
    rcases eq_or_lt_of_le (X.weight_nonneg i) with hwi | hwi
    · rw [← hwi]
      ring
    · rw [(hmom i hwi).1]
      simp [SSP.K2AllStages.erlangMixMoment]
      ring
  have hM2 : transientInitialMoment2 s X =
      ∑ i, X.weight i*s*(s+1)*(θ i)^2 := by
    unfold transientInitialMoment2
    apply Finset.sum_congr rfl
    intro i hi
    rcases eq_or_lt_of_le (X.weight_nonneg i) with hwi | hwi
    · rw [← hwi]
      ring
    · rw [(hmom i hwi).2.1]
      simp [SSP.K2AllStages.erlangMixMoment]
      ring
  have hM3 : transientInitialMoment3 s X =
      ∑ i, X.weight i*s*(s+1)*(s+2)*(θ i)^3 := by
    unfold transientInitialMoment3
    apply Finset.sum_congr rfl
    intro i hi
    rcases eq_or_lt_of_le (X.weight_nonneg i) with hwi | hwi
    · rw [← hwi]
      ring
    · rw [(hmom i hwi).2.2]
      simp [SSP.K2AllStages.erlangMixMoment]
      ring
  have hscales : ∀ i : Fin s, ∀ j : Fin s,
      0 < X.weight i → 0 < X.weight j → θ i = θ j := by
    have h := SSP.K2AllStages.erlang_components_equality_scales s hs Finset.univ
      X.weight θ (fun i _ => X.weight_nonneg i) (fun i _ => hθpos i) (by
        rw [← hM1, ← hM2, ← hM3]
        exact heq)
    simpa using h
  let w : ℝ := ∑ i, X.weight i
  have hw0 : 0 ≤ w := Finset.sum_nonneg (fun i _ => X.weight_nonneg i)
  have hw1 : w ≤ 1 := X.weight_sum_le_one
  rcases eq_or_lt_of_le hw0 with hwzero | hwpos
  · have hallzero : ∀ i : Fin s, X.weight i = 0 := by
      intro i
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin s))) => X.weight_nonneg j)).mp hwzero.symm
      exact hz i (Finset.mem_univ i)
    refine ⟨0, 1, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · unfold transientInitialMoment1
      simp [hallzero, SSP.K2AllStages.erlangMixMoment]
    · unfold transientInitialMoment2
      simp [hallzero, SSP.K2AllStages.erlangMixMoment]
    · unfold transientInitialMoment3
      simp [hallzero, SSP.K2AllStages.erlangMixMoment]
  · have hex : ∃ i ∈ (Finset.univ : Finset (Fin s)), 0 < X.weight i :=
      (Finset.sum_pos_iff_of_nonneg
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin s))) => X.weight_nonneg i)).mp hwpos
    rcases hex with ⟨i, hi, hwi⟩
    refine ⟨w, θ i, hw0, hw1, hθpos i, ?_, ?_, ?_⟩
    · rw [hM1]
      simp only [SSP.K2AllStages.erlangMixMoment]
      dsimp [w]
      calc
        ∑ j, X.weight j*s*θ j = ∑ j, X.weight j*s*θ i := by
          apply Finset.sum_congr rfl
          intro j hj
          rcases eq_or_lt_of_le (X.weight_nonneg j) with hwj | hwj
          · rw [← hwj]
            ring
          · rw [hscales j i hwj hwi]
        _ = (∑ j, X.weight j)*s*θ i := by
          simpa [mul_assoc] using
            (Finset.sum_mul (Finset.univ : Finset (Fin s)) X.weight ((s : ℝ)*θ i)).symm
    · rw [hM2]
      simp only [SSP.K2AllStages.erlangMixMoment]
      dsimp [w]
      calc
        ∑ j, X.weight j*s*(s+1)*(θ j)^2 =
            ∑ j, X.weight j*s*(s+1)*(θ i)^2 := by
          apply Finset.sum_congr rfl
          intro j hj
          rcases eq_or_lt_of_le (X.weight_nonneg j) with hwj | hwj
          · rw [← hwj]
            ring
          · rw [hscales j i hwj hwi]
        _ = (∑ j, X.weight j)*s*(s+1)*(θ i)^2 := by
          calc
            _ = ∑ j, X.weight j*((s : ℝ)*(s+1)*(θ i)^2) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = (∑ j, X.weight j)*((s : ℝ)*(s+1)*(θ i)^2) :=
              (Finset.sum_mul (Finset.univ : Finset (Fin s)) X.weight
                ((s : ℝ)*(s+1)*(θ i)^2)).symm
            _ = _ := by ring
    · rw [hM3]
      simp only [SSP.K2AllStages.erlangMixMoment]
      dsimp [w]
      calc
        ∑ j, X.weight j*s*(s+1)*(s+2)*(θ j)^3 =
            ∑ j, X.weight j*s*(s+1)*(s+2)*(θ i)^3 := by
          apply Finset.sum_congr rfl
          intro j hj
          rcases eq_or_lt_of_le (X.weight_nonneg j) with hwj | hwj
          · rw [← hwj]
            ring
          · rw [hscales j i hwj hwi]
        _ = (∑ j, X.weight j)*s*(s+1)*(s+2)*(θ i)^3 := by
          calc
            _ = ∑ j, X.weight j*((s : ℝ)*(s+1)*(s+2)*(θ i)^3) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = (∑ j, X.weight j)*((s : ℝ)*(s+1)*(s+2)*(θ i)^3) :=
              (Finset.sum_mul (Finset.univ : Finset (Fin s)) X.weight
                ((s : ℝ)*(s+1)*(s+2)*(θ i)^3)).symm
            _ = _ := by ring

/-- Iff form of the equality classification on the full transient class. -/
theorem transientInitial_equality_iff_erlang_moments_direct {s : ℕ} (hs : 1 ≤ s)
    (X : TransientInitial s) :
    SSP.K2AllStages.gap s (transientInitialMoment1 s X)
        (transientInitialMoment2 s X) (transientInitialMoment3 s X) = 0 ↔
      ∃ w θ : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ 0 < θ ∧
        transientInitialMoment1 s X = SSP.K2AllStages.erlangMixMoment s w θ 1 ∧
        transientInitialMoment2 s X = SSP.K2AllStages.erlangMixMoment s w θ 2 ∧
        transientInitialMoment3 s X = SSP.K2AllStages.erlangMixMoment s w θ 3 := by
  constructor
  · exact transientInitial_equality_moments_direct hs X
  · rintro ⟨w, θ, hw0, hw1, hθ, h1, h2, h3⟩
    rw [h1, h2, h3]
    exact SSP.K2AllStages.erlang_mixture_sharp s w θ

/-- Moment-level equality classification for an arbitrary subprobability initial law: its
first three moments are those of an atom at zero mixed with one common-scale Erlang law. -/
theorem initial_equality_moments_direct {s : ℕ} (hs : 1 ≤ s)
    (X : AbsorptionInitial s)
    (heq : SSP.K2AllStages.gap s (initialMoment1 s X)
      (initialMoment2 s X) (initialMoment3 s X) = 0) :
    ∃ w θ : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ 0 < θ ∧
      initialMoment1 s X = SSP.K2AllStages.erlangMixMoment s w θ 1 ∧
      initialMoment2 s X = SSP.K2AllStages.erlangMixMoment s w θ 2 ∧
      initialMoment3 s X = SSP.K2AllStages.erlangMixMoment s w θ 3 := by
  classical
  have hcompgap : ∀ i : Fin s, 0 ≤ SSP.K2AllStages.gap s
      (moment1 s (X.component i)) (moment2 s (X.component i))
      (moment3 s (X.component i)) := by
    intro i
    have hb := all_transient_starts_direct s hs (X.component i).toTransient
    unfold SSP.K2AllStages.StageBound at hb
    simpa only [toTransient_moment1, toTransient_moment2, toTransient_moment3,
      SSP.K2AllStages.gap] using sub_nonneg.mpr hb
  have hcomponent : ∀ i : Fin s, 0 < X.weight i →
      SSP.K2AllStages.gap s (moment1 s (X.component i))
        (moment2 s (X.component i)) (moment3 s (X.component i)) = 0 := by
    have h := SSP.K2AllStages.mixture_equality_component_gap s hs Finset.univ X.weight
      (fun i => moment1 s (X.component i))
      (fun i => moment2 s (X.component i))
      (fun i => moment3 s (X.component i))
      (fun i _ => X.weight_nonneg i)
      (fun i _ => moment1_pos (X.component i))
      (fun i _ => hcompgap i)
      (by simpa [initialMoment1, initialMoment2, initialMoment3] using heq)
    simpa using h
  have hclass : ∀ i : Fin s, 0 < X.weight i →
      ∃ θ : ℝ, 0 < θ ∧
        moment1 s (X.component i) = SSP.K2AllStages.erlangMixMoment s 1 θ 1 ∧
        moment2 s (X.component i) = SSP.K2AllStages.erlangMixMoment s 1 θ 2 ∧
        moment3 s (X.component i) = SSP.K2AllStages.erlangMixMoment s 1 θ 3 := by
    intro i hwi
    have h := transient_equality_moments hs (X.component i).toTransient (by
      simpa only [toTransient_moment1, toTransient_moment2, toTransient_moment3] using
        hcomponent i hwi)
    simpa only [toTransient_moment1, toTransient_moment2, toTransient_moment3] using h
  let θ : Fin s → ℝ := fun i =>
    if h : 0 < X.weight i then Classical.choose (hclass i h) else 1
  have hθpos : ∀ i : Fin s, 0 < θ i := by
    intro i
    dsimp [θ]
    split
    · rename_i hwi
      exact (Classical.choose_spec (hclass i hwi)).1
    · norm_num
  have hmom : ∀ i : Fin s, 0 < X.weight i →
      moment1 s (X.component i) = SSP.K2AllStages.erlangMixMoment s 1 (θ i) 1 ∧
      moment2 s (X.component i) = SSP.K2AllStages.erlangMixMoment s 1 (θ i) 2 ∧
      moment3 s (X.component i) = SSP.K2AllStages.erlangMixMoment s 1 (θ i) 3 := by
    intro i hwi
    dsimp [θ]
    rw [dif_pos hwi]
    exact (Classical.choose_spec (hclass i hwi)).2
  have hM1 : initialMoment1 s X = ∑ i, X.weight i*s*(θ i) := by
    unfold initialMoment1
    apply Finset.sum_congr rfl
    intro i hi
    rcases eq_or_lt_of_le (X.weight_nonneg i) with hwi | hwi
    · rw [← hwi]
      ring
    · rw [(hmom i hwi).1]
      simp [SSP.K2AllStages.erlangMixMoment]
      ring
  have hM2 : initialMoment2 s X = ∑ i, X.weight i*s*(s+1)*(θ i)^2 := by
    unfold initialMoment2
    apply Finset.sum_congr rfl
    intro i hi
    rcases eq_or_lt_of_le (X.weight_nonneg i) with hwi | hwi
    · rw [← hwi]
      ring
    · rw [(hmom i hwi).2.1]
      simp [SSP.K2AllStages.erlangMixMoment]
      ring
  have hM3 : initialMoment3 s X = ∑ i, X.weight i*s*(s+1)*(s+2)*(θ i)^3 := by
    unfold initialMoment3
    apply Finset.sum_congr rfl
    intro i hi
    rcases eq_or_lt_of_le (X.weight_nonneg i) with hwi | hwi
    · rw [← hwi]
      ring
    · rw [(hmom i hwi).2.2]
      simp [SSP.K2AllStages.erlangMixMoment]
      ring
  have hscales : ∀ i : Fin s, ∀ j : Fin s,
      0 < X.weight i → 0 < X.weight j → θ i = θ j := by
    have h := SSP.K2AllStages.erlang_components_equality_scales s hs Finset.univ
      X.weight θ (fun i _ => X.weight_nonneg i) (fun i _ => hθpos i) (by
        rw [← hM1, ← hM2, ← hM3]
        exact heq)
    simpa using h
  let w : ℝ := ∑ i, X.weight i
  have hw0 : 0 ≤ w := Finset.sum_nonneg (fun i _ => X.weight_nonneg i)
  have hw1 : w ≤ 1 := X.weight_sum_le_one
  rcases eq_or_lt_of_le hw0 with hwzero | hwpos
  · have hallzero : ∀ i : Fin s, X.weight i = 0 := by
      intro i
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin s))) => X.weight_nonneg j)).mp hwzero.symm
      exact hz i (Finset.mem_univ i)
    refine ⟨0, 1, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · unfold initialMoment1
      simp [hallzero, SSP.K2AllStages.erlangMixMoment]
    · unfold initialMoment2
      simp [hallzero, SSP.K2AllStages.erlangMixMoment]
    · unfold initialMoment3
      simp [hallzero, SSP.K2AllStages.erlangMixMoment]
  · have hex : ∃ i ∈ (Finset.univ : Finset (Fin s)), 0 < X.weight i :=
      (Finset.sum_pos_iff_of_nonneg
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin s))) => X.weight_nonneg i)).mp hwpos
    rcases hex with ⟨i, hi, hwi⟩
    refine ⟨w, θ i, hw0, hw1, hθpos i, ?_, ?_, ?_⟩
    · rw [hM1]
      simp only [SSP.K2AllStages.erlangMixMoment]
      dsimp [w]
      calc
        ∑ j, X.weight j*s*θ j = ∑ j, X.weight j*s*θ i := by
          apply Finset.sum_congr rfl
          intro j hj
          rcases eq_or_lt_of_le (X.weight_nonneg j) with hwj | hwj
          · rw [← hwj]
            ring
          · rw [hscales j i hwj hwi]
        _ = (∑ j, X.weight j)*s*θ i := by
          simpa [mul_assoc] using
            (Finset.sum_mul (Finset.univ : Finset (Fin s)) X.weight ((s : ℝ)*θ i)).symm
    · rw [hM2]
      simp only [SSP.K2AllStages.erlangMixMoment]
      dsimp [w]
      calc
        ∑ j, X.weight j*s*(s+1)*(θ j)^2 =
            ∑ j, X.weight j*s*(s+1)*(θ i)^2 := by
          apply Finset.sum_congr rfl
          intro j hj
          rcases eq_or_lt_of_le (X.weight_nonneg j) with hwj | hwj
          · rw [← hwj]
            ring
          · rw [hscales j i hwj hwi]
        _ = (∑ j, X.weight j)*s*(s+1)*(θ i)^2 := by
          calc
            _ = ∑ j, X.weight j*((s : ℝ)*(s+1)*(θ i)^2) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = (∑ j, X.weight j)*((s : ℝ)*(s+1)*(θ i)^2) :=
              (Finset.sum_mul (Finset.univ : Finset (Fin s)) X.weight
                ((s : ℝ)*(s+1)*(θ i)^2)).symm
            _ = _ := by ring
    · rw [hM3]
      simp only [SSP.K2AllStages.erlangMixMoment]
      dsimp [w]
      calc
        ∑ j, X.weight j*s*(s+1)*(s+2)*(θ j)^3 =
            ∑ j, X.weight j*s*(s+1)*(s+2)*(θ i)^3 := by
          apply Finset.sum_congr rfl
          intro j hj
          rcases eq_or_lt_of_le (X.weight_nonneg j) with hwj | hwj
          · rw [← hwj]
            ring
          · rw [hscales j i hwj hwi]
        _ = (∑ j, X.weight j)*s*(s+1)*(s+2)*(θ i)^3 := by
          calc
            _ = ∑ j, X.weight j*((s : ℝ)*(s+1)*(s+2)*(θ i)^3) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = (∑ j, X.weight j)*((s : ℝ)*(s+1)*(s+2)*(θ i)^3) :=
              (Finset.sum_mul (Finset.univ : Finset (Fin s)) X.weight
                ((s : ℝ)*(s+1)*(s+2)*(θ i)^3)).symm
            _ = _ := by ring

/-- Equality in the arbitrary-initial `k = 2` bound is equivalent, at the level of the first
three moments, to being an atom-at-zero mixture of a common-scale `s`-stage Erlang law. -/
theorem initial_equality_iff_erlang_moments_direct {s : ℕ} (hs : 1 ≤ s)
    (X : AbsorptionInitial s) :
    SSP.K2AllStages.gap s (initialMoment1 s X)
        (initialMoment2 s X) (initialMoment3 s X) = 0 ↔
      ∃ w θ : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ 0 < θ ∧
        initialMoment1 s X = SSP.K2AllStages.erlangMixMoment s w θ 1 ∧
        initialMoment2 s X = SSP.K2AllStages.erlangMixMoment s w θ 2 ∧
        initialMoment3 s X = SSP.K2AllStages.erlangMixMoment s w θ 3 := by
  constructor
  · exact initial_equality_moments_direct hs X
  · rintro ⟨w, θ, hw0, hw1, hθ, h1, h2, h3⟩
    rw [h1, h2, h3]
    exact SSP.K2AllStages.erlang_mixture_sharp s w θ

/-- All-stage inequality for arbitrary subprobability initial distributions, now independent
of the He--Zhang order-three representation. -/
theorem all_absorption_initial_laws_direct {s : ℕ} (hs : 1 ≤ s)
    (X : AbsorptionInitial s) :
    SSP.K2AllStages.StageBound s
      (initialMoment1 s X) (initialMoment2 s X) (initialMoment3 s X) := by
  apply initialStageBound_of_components
  intro i
  simpa only [toTransient_moment1, toTransient_moment2, toTransient_moment3] using
    all_transient_starts_direct s hs (X.component i).toTransient

/-- Resolvent form of the unconditional all-stage theorem. -/
theorem all_initial_resolvent_bound_direct {s : ℕ} (hs : 1 ≤ s)
    (X : AbsorptionInitial s) :
    ((s : ℝ) + 2) *
        (∑ i, X.weight i *
          (2 * ((1 - X.model.Q)⁻¹.mulVec ((1 - X.model.Q)⁻¹.mulVec
            (fun _ => (1 : ℝ)))) i)) ^ 2
      ≤ ((s : ℝ) + 1) *
        ((∑ i, X.weight i *
          ((1 - X.model.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) i) *
        (∑ i, X.weight i *
          (6 * ((1 - X.model.Q)⁻¹.mulVec ((1 - X.model.Q)⁻¹.mulVec
            ((1 - X.model.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i))) := by
  have h := all_absorption_initial_laws_direct hs X
  unfold SSP.K2AllStages.StageBound at h
  simpa [initialMoment1, initialMoment2, initialMoment3,
    AbsorptionInitial.component, withStart, moment1_eq, moment2_eq, moment3_eq,
    mul_assoc] using h

end SSP.K2Concrete
