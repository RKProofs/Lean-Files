import SSPLean.K3S3ReturnFace
import SSPLean.K3S3Interior

/-!
# The genuinely cyclic three-state `k = 3` case

This file supplies the low-order polynomial certificates which cannot be
obtained by specializing the uniform (`n ≥ 4`) certificate.  The first part
proves the sharp-corner certificate at `n = 3`.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

private theorem n3_cubic_with_negative_terms_nonneg
    (y A B C D : ℝ) (hy : 0 ≤ y) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hsmall : B + C ≤ D)
    (hlarge : B + C ≤ A) :
    0 ≤ A*y^3-B*y^2-C*y+D := by
  rcases le_total y 1 with hy1 | h1y
  · have hy2le : y^2 ≤ 1 := by nlinarith [sq_nonneg (1-y)]
    have hBy2 : B*y^2 ≤ B := by nlinarith [mul_nonneg hB (sub_nonneg.mpr hy2le)]
    have hCy : C*y ≤ C := by nlinarith [mul_nonneg hC (sub_nonneg.mpr hy1)]
    nlinarith [mul_nonneg hA (mul_nonneg (sq_nonneg y) hy)]
  · have hy2ley3 : y^2 ≤ y^3 := by
      have := mul_nonneg (sq_nonneg y) (sub_nonneg.mpr h1y)
      nlinarith
    have hyley3 : y ≤ y^3 := by
      have hy2 : y ≤ y^2 := by
        have := mul_nonneg hy (sub_nonneg.mpr h1y)
        nlinarith
      linarith
    have hneg : B*y^2+C*y ≤ (B+C)*y^3 := by
      nlinarith [mul_nonneg hB (sub_nonneg.mpr hy2ley3),
        mul_nonneg hC (sub_nonneg.mpr hyley3)]
    have hlead : (B+C)*y^3 ≤ A*y^3 := by
      exact mul_le_mul_of_nonneg_right hlarge (by positivity)
    nlinarith

private theorem n3_corner_high_coefficients_nonneg (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ 25*y^3-8*y^2-2*y+40 ∧
    0 ≤ 425*y^3-28*y^2-78*y+315 ∧
    0 ≤ 975*y^3+176*y^2-177*y+360 ∧
    0 ≤ 225*y^3+92*y^2-21*y+30 ∧
    0 ≤ 25*y^3-8*y^2-2*y+20 ∧
    0 ≤ 3*y^4+1604*y^3-4*y^2-312*y+630 ∧
    0 ≤ 6*y^4+1710*y^3+541*y^2-354*y+360 ∧
    0 ≤ 9*y^4+1818*y^3+1172*y^2-210*y+150 ∧
    0 ≤ 75*y^3-24*y^2-6*y+40 ∧
    0 ≤ 3*y^4+754*y^3+52*y^2-156*y+210 ∧
    0 ≤ 24*y^4+3075*y^3+1460*y^2-708*y+480 ∧
    0 ≤ 36*y^4+3177*y^3+2848*y^2-420*y+200 := by
  have h1 := n3_cubic_with_negative_terms_nonneg y 25 8 2 40 hy
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := n3_cubic_with_negative_terms_nonneg y 425 28 78 315 hy
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := n3_cubic_with_negative_terms_nonneg y 975 0 177 360 hy
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 := n3_cubic_with_negative_terms_nonneg y 225 0 21 30 hy
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := n3_cubic_with_negative_terms_nonneg y 25 8 2 20 hy
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 := n3_cubic_with_negative_terms_nonneg y 1604 4 312 630 hy
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := n3_cubic_with_negative_terms_nonneg y 1710 0 354 360 hy
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 : 0 ≤ 1818*y^3+1172*y^2-210*y+150 := by
    nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 1818)
      (mul_nonneg (sq_nonneg y) hy), sq_nonneg (1172*y-105)]
  have h9 := n3_cubic_with_negative_terms_nonneg y 75 24 6 40 hy
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h10 := n3_cubic_with_negative_terms_nonneg y 754 0 156 210 hy
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 : 0 ≤ 24*y^4+3075*y^3+1460*y^2-708*y+480 := by
    nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 24) (sq_nonneg (y^2)),
      mul_nonneg (by norm_num : (0:ℝ) ≤ 3075) (mul_nonneg (sq_nonneg y) hy),
      sq_nonneg (1460*y-354)]
  have h12 : 0 ≤ 36*y^4+3177*y^3+2848*y^2-420*y+200 := by
    nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 36) (sq_nonneg (y^2)),
      mul_nonneg (by norm_num : (0:ℝ) ≤ 3177) (mul_nonneg (sq_nonneg y) hy),
      sq_nonneg (2848*y-210)]
  constructor
  · exact h1
  constructor
  · exact h2
  constructor
  · nlinarith [h3, mul_nonneg (by norm_num : (0:ℝ) ≤ 176) (sq_nonneg y)]
  constructor
  · nlinarith [h4, mul_nonneg (by norm_num : (0:ℝ) ≤ 92) (sq_nonneg y)]
  constructor
  · exact h5
  constructor
  · nlinarith [h6, mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (sq_nonneg (y^2))]
  constructor
  · nlinarith [h7, mul_nonneg (by norm_num : (0:ℝ) ≤ 6) (sq_nonneg (y^2)),
      mul_nonneg (by norm_num : (0:ℝ) ≤ 541) (sq_nonneg y)]
  constructor
  · nlinarith [h8, mul_nonneg (by norm_num : (0:ℝ) ≤ 9) (sq_nonneg (y^2)),
      mul_nonneg (by norm_num : (0:ℝ) ≤ 1172) (sq_nonneg y)]
  constructor
  · exact h9
  constructor
  · nlinarith [h10, mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (sq_nonneg (y^2)),
      mul_nonneg (by norm_num : (0:ℝ) ≤ 52) (sq_nonneg y)]
  constructor
  · nlinarith [h11, mul_nonneg (by norm_num : (0:ℝ) ≤ 24) (sq_nonneg (y^2)),
      mul_nonneg (by norm_num : (0:ℝ) ≤ 1460) (sq_nonneg y)]
  · nlinarith [h12, mul_nonneg (by norm_num : (0:ℝ) ≤ 36) (sq_nonneg (y^2)),
      mul_nonneg (by norm_num : (0:ℝ) ≤ 2848) (sq_nonneg y)]

private theorem n3_corner_qzero_nonneg (a T Y : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerPoly 3 a T Y 0 := by
  have hid : uniformCornerPoly 3 a T Y 0 =
      cornerBern3 384
        (16*(25*Y^3+8*Y^2+24*Y+24))
        (4*(3*Y^4+8*Y^3+136*Y^2+192*Y+96))
        (12*(Y+1)*(3*Y^3+40*Y^2+64*Y+32)) a := by
    unfold uniformCornerPoly uniformCornerM2Num uniformCornerM3Num
      uniformCornerM4Num cornerBern3
    ring
  rw [hid]
  exact cornerBern3_nonneg _ _ _ _ a (by norm_num) (by positivity)
    (by positivity) (by positivity) ha ha1

private theorem n3_corner_qone_low_nonneg (a T Y : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hT : 0 ≤ T) (hT2 : T ≤ 2)
    (hY : 0 ≤ Y) : 0 ≤ uniformCornerPoly 3 a T Y 1 := by
  let t := T/2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have h0 : 0 ≤ uniformCornerAOneB0 3 T Y := by
    rw [show uniformCornerAOneB0 3 T Y =
      12*(T-2)^2*(3*T^4+16*T^3+42*T^2+24*T+8) by
        unfold uniformCornerAOneB0 uniformCornerQOne uniformCornerPoly
          uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num
        ring]
    positivity
  have h1 : 0 ≤ uniformCornerAOneB1 3 T Y := by
    have hid : uniformCornerAOneB1 3 (2*t) Y = cornerBern6
        (16*(25*Y^3+8*Y^2+24*Y+24))
        (64*(25*Y^3+18*Y^2+27*Y+30)/3)
        (64*(175*Y^3+196*Y^2+255*Y+270)/15)
        (16*(325*Y^3+452*Y^2+552*Y+480)/5)
        (16*(265*Y^3+408*Y^2+456*Y+240)/3)
        (160*Y*(35*Y^2+56*Y+54)/3)
        (480*Y*(5*Y^2+8*Y+6)) t := by
      unfold uniformCornerAOneB1 uniformCornerQOne uniformCornerPoly
        uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num cornerBern6
      ring
    rw [show (2:ℝ)*t=T by dsimp [t]; ring] at hid
    rw [hid]
    apply cornerBern6_nonneg <;> first | assumption | positivity
  have h2 : 0 ≤ uniformCornerAOneB2 3 T Y := by
    have hid : uniformCornerAOneB2 3 (2*t) Y = cornerBern6
        (4*(3*Y^4+8*Y^3+136*Y^2+192*Y+96))
        (4*(9*Y^4+128*Y^3+684*Y^2+864*Y+480)/3)
        (4*(45*Y^4+1760*Y^3+6704*Y^2+8160*Y+4320)/15)
        (4*(15*Y^4+1160*Y^3+3868*Y^2+4416*Y+1920)/5)
        (4*(45*Y^4+5800*Y^3+17832*Y^2+18240*Y+4800)/15)
        (4*Y*(9*Y^3+1744*Y^2+5020*Y+4320)/3)
        (12*Y*(Y^3+272*Y^2+736*Y+480)) t := by
      unfold uniformCornerAOneB2 uniformCornerQOne uniformCornerPoly
        uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num cornerBern6
      ring
    rw [show (2:ℝ)*t=T by dsimp [t]; ring] at hid
    rw [hid]
    apply cornerBern6_nonneg <;> first | assumption | positivity
  have h3 : 0 ≤ uniformCornerAOneB3 3 T Y := by
    have hid : uniformCornerAOneB3 3 (2*t) Y = cornerBern6
        (12*(Y+1)*(3*Y^3+40*Y^2+64*Y+32))
        (4*(Y+1)*(9*Y^3+124*Y^2+272*Y+160))
        (4*(45*Y^4+985*Y^3+3568*Y^2+4080*Y+1440)/5)
        (12*(15*Y^4+535*Y^3+2060*Y^2+2208*Y+640)/5)
        (4*(45*Y^4+2525*Y^3+9672*Y^2+9120*Y+1600)/5)
        (4*Y*(9*Y^3+749*Y^2+2780*Y+2160))
        (36*Y*(Y^3+117*Y^2+416*Y+240)) t := by
      unfold uniformCornerAOneB3 uniformCornerQOne uniformCornerPoly
        uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num cornerBern6
      ring
    rw [show (2:ℝ)*t=T by dsimp [t]; ring] at hid
    rw [hid]
    apply cornerBern6_nonneg <;> first | assumption | positivity
  rw [show uniformCornerPoly 3 a T Y 1 = uniformCornerQOne 3 a T Y by rfl,
    uniformCornerQOne_bernstein_a]
  positivity

private theorem n3_corner_qone_high_nonneg (a T Y : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hT2 : 2 ≤ T) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerPoly 3 a T Y 1 := by
  have hTp : 0 < T := by linarith
  let t := 2/T
  let y := Y/T
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; rw [div_le_one hTp]; linarith
  have hy : 0 ≤ y := by dsimp [y]; positivity
  obtain ⟨hc11, hc12, hc13, hc14, hc21, hc22, hc23, hc24,
      hc31, hc32, hc33, hc34⟩ := n3_corner_high_coefficients_nonneg y hy
  have hT' : 2/t = T := by dsimp [t]; field_simp [hTp.ne']
  have hY' : 2*y/t = Y := by dsimp [t, y]; field_simp [hTp.ne']
  have ht6 : 0 < t^6 := by positivity
  have h0 : 0 ≤ uniformCornerAOneB0 3 T Y := by
    rw [show uniformCornerAOneB0 3 T Y =
      12*(T-2)^2*(3*T^4+16*T^3+42*T^2+24*T+8) by
        unfold uniformCornerAOneB0 uniformCornerQOne uniformCornerPoly
          uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num
        ring]
    positivity
  have h1 : 0 ≤ uniformCornerAOneB1 3 T Y := by
    have hid : t^6*uniformCornerAOneB1 3 (2/t) (2*y/t) = cornerBern6
        2304
        (64*(25*y^3-8*y^2-2*y+40))
        (128*(425*y^3-28*y^2-78*y+315)/15)
        (32*(975*y^3+176*y^2-177*y+360)/5)
        (128*(225*y^3+92*y^2-21*y+30)/3)
        (320*y*(130*y^2+80*y+9)/3)
        (1920*y*(10*y^2+8*y+3)) t := by
      unfold uniformCornerAOneB1 uniformCornerQOne uniformCornerPoly
        uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num cornerBern6
      field_simp [ht.ne']
      ring
    have hb : 0 ≤ cornerBern6
        2304
        (64*(25*y^3-8*y^2-2*y+40))
        (128*(425*y^3-28*y^2-78*y+315)/15)
        (32*(975*y^3+176*y^2-177*y+360)/5)
        (128*(225*y^3+92*y^2-21*y+30)/3)
        (320*y*(130*y^2+80*y+9)/3)
        (1920*y*(10*y^2+8*y+3)) t := by
      apply cornerBern6_nonneg <;> first | assumption | positivity
    rw [hT', hY'] at hid
    have : 0 ≤ t^6*uniformCornerAOneB1 3 T Y := by linarith
    exact (mul_nonneg_iff_of_pos_left ht6).mp this
  have h2 : 0 ≤ uniformCornerAOneB2 3 T Y := by
    have hid : t^6*uniformCornerAOneB2 3 (2/t) (2*y/t) = cornerBern6
        2304
        (128*(25*y^3-8*y^2-2*y+20))
        (64*(3*y^4+1604*y^3-4*y^2-312*y+630)/15)
        (32*(6*y^4+1710*y^3+541*y^2-354*y+360)/5)
        (128*(9*y^4+1818*y^3+1172*y^2-210*y+150)/15)
        (64*y*(6*y^3+964*y^2+953*y+90)/3)
        (192*y*(y^3+136*y^2+184*y+60)) t := by
      unfold uniformCornerAOneB2 uniformCornerQOne uniformCornerPoly
        uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num cornerBern6
      field_simp [ht.ne']
      ring
    have hb : 0 ≤ cornerBern6
        2304
        (128*(25*y^3-8*y^2-2*y+20))
        (64*(3*y^4+1604*y^3-4*y^2-312*y+630)/15)
        (32*(6*y^4+1710*y^3+541*y^2-354*y+360)/5)
        (128*(9*y^4+1818*y^3+1172*y^2-210*y+150)/15)
        (64*y*(6*y^3+964*y^2+953*y+90)/3)
        (192*y*(y^3+136*y^2+184*y+60)) t := by
      apply cornerBern6_nonneg <;> first | assumption | positivity
    rw [hT', hY'] at hid
    have : 0 ≤ t^6*uniformCornerAOneB2 3 T Y := by linarith
    exact (mul_nonneg_iff_of_pos_left ht6).mp this
  have h3 : 0 ≤ uniformCornerAOneB3 3 T Y := by
    have hid : t^6*uniformCornerAOneB3 3 (2/t) (2*y/t) = cornerBern6
        2304
        (64*(75*y^3-24*y^2-6*y+40))
        (64*(3*y^4+754*y^3+52*y^2-156*y+210)/5)
        (24*(24*y^4+3075*y^3+1460*y^2-708*y+480)/5)
        (32*(36*y^4+3177*y^3+2848*y^2-420*y+200)/5)
        (16*y*(24*y^3+1661*y^2+2212*y+180))
        (288*y*(2*y^3+117*y^2+208*y+60)) t := by
      unfold uniformCornerAOneB3 uniformCornerQOne uniformCornerPoly
        uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num cornerBern6
      field_simp [ht.ne']
      ring
    have hb : 0 ≤ cornerBern6
        2304
        (64*(75*y^3-24*y^2-6*y+40))
        (64*(3*y^4+754*y^3+52*y^2-156*y+210)/5)
        (24*(24*y^4+3075*y^3+1460*y^2-708*y+480)/5)
        (32*(36*y^4+3177*y^3+2848*y^2-420*y+200)/5)
        (16*y*(24*y^3+1661*y^2+2212*y+180))
        (288*y*(2*y^3+117*y^2+208*y+60)) t := by
      apply cornerBern6_nonneg <;> first | assumption | positivity
    rw [hT', hY'] at hid
    have : 0 ≤ t^6*uniformCornerAOneB3 3 T Y := by linarith
    exact (mul_nonneg_iff_of_pos_left ht6).mp this
  rw [show uniformCornerPoly 3 a T Y 1 = uniformCornerQOne 3 a T Y by rfl,
    uniformCornerQOne_bernstein_a]
  positivity

private theorem n3_corner_qone_nonneg (a T Y : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hT : 0 ≤ T) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerPoly 3 a T Y 1 := by
  by_cases hT2 : T ≤ 2
  · exact n3_corner_qone_low_nonneg a T Y ha ha1 hT hT2 hY
  · exact n3_corner_qone_high_nonneg a T Y ha ha1 (by linarith) hY

/-- The sharp-corner certificate for the exceptional stage parameter `n = 3`. -/
theorem uniformSharpGap_three_nonneg (a T Y q : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hT : 0 < T) (hY : 0 < Y)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    0 ≤ uniformSharpGap 3 a T Y q := by
  have hzero := n3_corner_qzero_nonneg a T Y ha ha1 hY.le
  have hone := n3_corner_qone_nonneg a T Y ha ha1 hT.le hY.le
  obtain ⟨⟨h20, h30, h40⟩, ⟨h21, h31, h41⟩⟩ :
      (0 ≤ uniformCornerM2Num 3 a T Y 0 ∧
        0 ≤ uniformCornerM3Num 3 a T Y 0 ∧
        0 ≤ uniformCornerM4Num 3 a T Y 0) ∧
      (0 ≤ uniformCornerM2Num 3 a T Y 1 ∧
        0 ≤ uniformCornerM3Num 3 a T Y 1 ∧
        0 ≤ uniformCornerM4Num 3 a T Y 1) := by
    constructor
    · constructor
      · rw [show uniformCornerM2Num 3 a T Y 0 = 3*Y*a+4 by
          unfold uniformCornerM2Num; ring]
        positivity
      constructor
      · rw [show uniformCornerM3Num 3 a T Y 0 =
          12*Y^2*a+36*Y*a+24 by unfold uniformCornerM3Num; ring]
        positivity
      · rw [show uniformCornerM4Num 3 a T Y 0 =
          60*Y^3*a+108*Y^2*a^2+192*Y^2*a+432*Y*a+192 by
            unfold uniformCornerM4Num; ring]
        positivity
    · constructor
      · rw [show uniformCornerM2Num 3 a T Y 1 =
          3*T^2+4*T+3*Y*a+4 by unfold uniformCornerM2Num; ring]
        positivity
      constructor
      · rw [show uniformCornerM3Num 3 a T Y 1 =
          12*T^3+18*T^2+18*T*Y*a+24*T+12*Y^2*a+36*Y*a+24 by
            unfold uniformCornerM3Num; ring]
        positivity
      · rw [show uniformCornerM4Num 3 a T Y 1 =
          60*T^4+96*T^3+108*T^2*Y*a+144*T^2+96*T*Y^2*a+
            288*T*Y*a+192*T+60*Y^3*a+108*Y^2*a^2+192*Y^2*a+
            432*Y*a+192 by unfold uniformCornerM4Num; ring]
        positivity
  have hmix := momentGap_convex_mixture 5 6
    (uniformCornerM2Num 3 a T Y 0) (uniformCornerM3Num 3 a T Y 0)
      (uniformCornerM4Num 3 a T Y 0)
    (uniformCornerM2Num 3 a T Y 1) (uniformCornerM3Num 3 a T Y 1)
      (uniformCornerM4Num 3 a T Y 1) q
    (by norm_num) (by norm_num) h20 h30 h40 h21 h31 h41
    (by norm_num [uniformCornerPoly] at hzero ⊢; exact hzero)
    (by norm_num [uniformCornerPoly] at hone ⊢; exact hone) hq.le hq1
  have hpoly : 0 ≤ uniformCornerPoly 3 a T Y q := by
    unfold uniformCornerPoly
    rw [uniformCornerM2Num_affine, uniformCornerM3Num_affine,
      uniformCornerM4Num_affine]
    norm_num at hmix ⊢
    exact hmix
  have hid := uniformSharpGap_eq_cornerPoly 3 a T Y q
    (by norm_num) (by norm_num) (by norm_num) hT.ne' hY.ne' hq.ne' (by positivity)
  norm_num at hid
  nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem sharpGap_three_scale
    (L r x u A v B : ℝ) (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    sharpGap 3 r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^6*sharpGap 3 r x u A v B := by
  unfold sharpGap sharpThird excursionReducedGap stageGap
  unfold SSP.K3S4Renewal.geomM4 SSP.K3S4Renewal.geomM3
    SSP.K3S4Renewal.geomM2 SSP.K3S4Renewal.geomM1
  unfold SSP.K3S4Renewal.kernelM1 SSP.K3S4Renewal.kernelM2
    SSP.K3S4Renewal.kernelM3 SSP.K3S4Renewal.kernelM4
  field_simp [hL, hu, hv, hA, hB]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem sharpGap_three_mixture_coordinates
    (a T Y p q : ℝ) (hT : T ≠ 0) (hY : Y ≠ 0) (hp : p ≠ 0)
    (hq : q ≠ 0) (hsum : p*Y+a ≠ 0) (hsum1 : Y+a ≠ 0) :
    sharpGap 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) =
      uniformSharpGap 3 a T Y q := by
  unfold uniformSharpGap sharpGap sharpThird excursionReducedGap stageGap
  unfold SSP.K3S4Renewal.geomM4 SSP.K3S4Renewal.geomM3
    SSP.K3S4Renewal.geomM2 SSP.K3S4Renewal.geomM1
  unfold SSP.K3S4Renewal.kernelM1 SSP.K3S4Renewal.kernelM2
    SSP.K3S4Renewal.kernelM3 SSP.K3S4Renewal.kernelM4
  field_simp [hT, hY, hp, hq, hsum, hsum1]
  ring

/-- The sharp-corner certificate in the original excursion coordinates at
the exceptional stage parameter `n = 3`. -/
theorem sharpGap_three_nonneg_general
    (r x u A v B : ℝ) (hr : 0 < r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v)
    (hA : 3*u^2 ≤ 2*A) (hB : 3*v^2 ≤ 2*B) :
    0 ≤ sharpGap 3 r x u A v B := by
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBp : 0 < B := by nlinarith [sq_pos_of_pos hv]
  let p := mixtureWeight 3 u A
  let q := mixtureWeight 3 v B
  let L := r*u+(r+1)*x
  obtain ⟨hp, hp1⟩ := mixtureWeight_pos_le_one 3 u A (by norm_num) hu (by
    norm_num at hA ⊢
    exact hA)
  obtain ⟨hq, hq1⟩ := mixtureWeight_pos_le_one 3 v B (by norm_num) hv (by
    norm_num at hB ⊢
    exact hB)
  have hp' : 0 < p := by simpa [p] using hp
  have hq' : 0 < q := by simpa [q] using hq
  have hp1' : p ≤ 1 := by simpa [p] using hp1
  have hq1' : q ≤ 1 := by simpa [q] using hq1
  have hL : 0 < L := by
    dsimp [L]
    have : 0 < r*u := mul_pos hr hu
    positivity
  let a := r*u/L
  let Y := u/(p*L)
  let T := v/(q*L)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one hL]
    dsimp [L]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r+1) hx]
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hrid : a/(p*Y) = r := by
    dsimp [a, Y]
    field_simp [hp'.ne', hL.ne', hu.ne']
  have hxid : L*(p*Y*(1-a)/(p*Y+a)) = x := by
    dsimp [a, Y, L]
    field_simp [hp'.ne', hL.ne', hu.ne']
    simp
    ring
  have huid : L*(p*Y) = u := by
    dsimp [Y]
    field_simp [hp'.ne', hL.ne']
  have hvid : L*(q*T) = v := by
    dsimp [T]
    field_simp [hq'.ne', hL.ne']
  have hAid : L^2*(3*p*Y^2/2) = A := by
    dsimp [Y, p, mixtureWeight]
    norm_num
    field_simp [hu.ne', hAp.ne', hL.ne']
  have hBid : L^2*(3*q*T^2/2) = B := by
    dsimp [T, q, mixtureWeight]
    field_simp [hv.ne', hBp.ne', hL.ne']
    ring
  have hcertU := uniformSharpGap_three_nonneg a T Y q ha.le ha1 hT hY hq' hq1'
  have hmix := sharpGap_three_mixture_coordinates a T Y p q hT.ne' hY.ne'
    hp'.ne' hq'.ne' (by positivity) (by positivity)
  have hcert : 0 ≤ sharpGap 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) := by
    rw [hmix]
    exact hcertU
  rw [hrid] at hcert
  have hscale := sharpGap_three_scale L (a/(p*Y))
    (p*Y*(1-a)/(p*Y+a)) (p*Y) (3*p*Y^2/2)
    (q*T) (3*q*T^2/2) hL.ne' (by positivity) (by positivity)
      (by positivity) (by positivity)
  rw [hrid, hxid, huid, hAid, hvid, hBid] at hscale
  rw [hscale]
  exact mul_nonneg (by positivity) hcert

end SSP.K3AllStages
