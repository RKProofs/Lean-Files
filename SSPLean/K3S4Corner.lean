import SSPLean.K3S4Renewal

/-!
# The lower moment corner of the `k = 3`, four-stage renewal problem

Both order-three excursions are put at their sharp moment endpoints, so their first four
moments are those of Erlang-three laws (with possibly different means).  The resulting full
geometric-return inequality is proved here.  This is the lower corner required by a KKT proof
of the remaining scalar renewal inequality.
-/

set_option autoImplicit false

namespace SSP.K3S4Corner

open SSP.K3S4Renewal

noncomputable def bad (y : ℝ) : ℝ :=
  2*y^4+10*y^3-135*y^2-81*y-54

noncomputable def lastCoeff (y : ℝ) : ℝ :=
  (y-3)^2*(20*y^4+120*y^3+324*y^2+216*y+81)

noncomputable def coeff0 (b z : ℝ) : ℝ :=
  -7*b^6-54*b^5*z+136*b^5-171*b^4*z^2+108*b^4*z+12*b^4
    -248*b^3*z^3-396*b^3*z^2+1404*b^3*z+568*b^3
    -144*b^2*z^4-440*b^2*z^3+1548*b^2*z^2+20*b^2
    -72*b*z^4+40*b*z^3+720*b*z^2+20*z^6

noncomputable def coeff1 (b z : ℝ) : ℝ :=
  (695*b^6+1566*b^5*z-944*b^5+171*b^4*z^2+864*b^4*z+2496*b^4
    -1144*b^3*z^3+1584*b^3*z^2+864*b^3*z-80*b^3
    -504*b^2*z^4-880*b^2*z^3+1908*b^2*z^2+1080*b^2*z+20*b^2
    -144*b*z^4+80*b*z^3+1440*b*z^2+60*z^6)/3

noncomputable def coeff2 (b z : ℝ) : ℝ :=
  (-297*b^6+3078*b^5*z+4104*b^5+2043*b^4*z^2+756*b^4*z-2700*b^4
    -1544*b^3*z^3+1980*b^3*z^2-540*b^3*z+1080*b^3
    -576*b^2*z^4-440*b^2*z^3+360*b^2*z^2+1080*b^2*z
    -72*b*z^4+40*b*z^3+720*b*z^2+60*z^6)/3

noncomputable def coeff3 (b z : ℝ) : ℝ :=
  (z-3*b)^2*(81*b^4+216*b^3*z+324*b^2*z^2+120*b*z^3+20*z^4)

private theorem bad_pos_imp_six_lt (y : ℝ) (hy : 0 ≤ y) (hbad : 0 < bad y) : 6 < y := by
  by_contra h
  have hy6 : y ≤ 6 := by linarith
  have h43 : y^4 ≤ 6*y^3 := by
    have := mul_nonneg (pow_nonneg hy 3) (sub_nonneg.mpr hy6)
    nlinarith
  have h32 : y^3 ≤ 6*y^2 := by
    have := mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hy6)
    nlinarith
  unfold bad at hbad
  nlinarith

private theorem discPoly0_nonneg (y : ℝ) (hy : 6 ≤ y) :
    0 ≤ 200*y^9+18216*y^8+1620*y^7-161892*y^6-414558*y^5
      -62694*y^4-25515*y^3+255879*y^2+216513*y+98415 := by
  have h : 0 ≤ y-6 := by linarith
  have hid :
      200*y^9+18216*y^8+1620*y^7-161892*y^6-414558*y^5
          -62694*y^4-25515*y^3+255879*y^2+216513*y+98415 =
        22211930889 + 34053696081*(y-6) + 22020507153*(y-6)^2
          +7939426005*(y-6)^3+1760836806*(y-6)^4+247981986*(y-6)^5
          +21896676*(y-6)^6+1135188*(y-6)^7+29016*(y-6)^8
          +200*(y-6)^9 := by ring
  rw [hid]
  positivity

private theorem discPoly1_nonneg (y : ℝ) (hy : 6 ≤ y) :
    0 ≤ 400*y^9+30708*y^8+11880*y^7-289872*y^6-869940*y^5
      +114453*y^4+1399680*y^3+1358127*y^2+669222*y+118098 := by
  have h : 0 ≤ y-6 := by linarith
  have hid :
      400*y^9+30708*y^8+11880*y^7-289872*y^6-869940*y^5
          +114453*y^4+1399680*y^3+1358127*y^2+669222*y+118098 =
        39149132706+59802268410*(y-6)+38624075559*(y-6)^2
          +13917222360*(y-6)^3+3085038333*(y-6)^4+434438316*(y-6)^5
          +38420352*(y-6)^6+2004264*(y-6)^7+52308*(y-6)^8
          +400*(y-6)^9 := by ring
  rw [hid]
  positivity

private theorem discPoly2_nonneg (y : ℝ) (hy : 6 ≤ y) :
    0 ≤ 200*y^9+12492*y^8+10260*y^7-127980*y^6-455382*y^5
      +177147*y^4+1425195*y^3+1102248*y^2+452709*y+19683 := by
  have h : 0 ≤ y-6 := by linarith
  have hid :
      200*y^9+12492*y^8+10260*y^7-127980*y^6-455382*y^5
          +177147*y^4+1425195*y^3+1102248*y^2+452709*y+19683 =
        16937201817+25748572329*(y-6)+16603568406*(y-6)^2
          +5977796355*(y-6)^3+1324201527*(y-6)^4+186456330*(y-6)^5
          +16523676*(y-6)^6+869076*(y-6)^7+23292*(y-6)^8
          +200*(y-6)^9 := by ring
  rw [hid]
  positivity

/-- A quartic Bernstein polynomial with one possibly negative next-to-last coefficient.
The final three terms are controlled by their quadratic discriminant. -/
private theorem bern4_one_bad (b c0 c1 c2 c3 c4 : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hc2 : 0 < c2) (hc4 : 0 ≤ c4)
    (hcase : 0 ≤ c3 ∨ 16*c3^2 ≤ 24*c2*c4) :
    0 ≤ c0*(1-b)^4+4*c1*b*(1-b)^3+6*c2*b^2*(1-b)^2
      +4*c3*b^3*(1-b)+c4*b^4 := by
  have hbm : 0 ≤ 1-b := sub_nonneg.mpr hb1
  rcases hcase with hc3 | hdisc
  · positivity
  · let Q := 6*c2*(1-b)^2+4*c3*b*(1-b)+c4*b^2
    have hid : 24*c2*Q =
        (12*c2*(1-b)+4*c3*b)^2+(24*c2*c4-16*c3^2)*b^2 := by
      dsimp [Q]
      ring
    have hscaled : 0 ≤ 24*c2*Q := by
      rw [hid]
      positivity
    have hQ : 0 ≤ Q := (mul_nonneg_iff_of_pos_left (by positivity : 0 < 24*c2)).mp hscaled
    have hrewrite :
        c0*(1-b)^4+4*c1*b*(1-b)^3+6*c2*b^2*(1-b)^2
            +4*c3*b^3*(1-b)+c4*b^4 =
          c0*(1-b)^4+4*c1*b*(1-b)^3+b^2*Q := by
      dsimp [Q]
      ring
    rw [hrewrite]
    positivity

private theorem coeff0_nonneg (b z : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z) :
    0 ≤ coeff0 b z := by
  by_cases hb : b = 0
  · subst b
    norm_num [coeff0]
    positivity
  · have hbp : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    let y := z/b
    have hy : 0 ≤ y := by dsimp [y]; positivity
    let c0 : ℝ := 20
    let c1 := 18*(10*y^2+9)
    let c2 := 2/3*(10*y^3+927*y^2+351*y+459)
    let c3 := -9*bad y
    let c4 := lastCoeff y
    have hc0 : 0 ≤ c0 := by norm_num [c0]
    have hc1 : 0 ≤ c1 := by dsimp [c1]; positivity
    have hc2 : 0 < c2 := by dsimp [c2]; positivity
    have hc4 : 0 ≤ c4 := by dsimp [c4, lastCoeff]; positivity
    have hcase : 0 ≤ c3 ∨ 16*c3^2 ≤ 24*c2*c4 := by
      by_cases hp : 0 < bad y
      · right
        have hy6 : 6 ≤ y := (bad_pos_imp_six_lt y hy hp).le
        have hq := discPoly0_nonneg y hy6
        have hid : 24*c2*c4-16*c3^2 =
            16*(200*y^9+18216*y^8+1620*y^7-161892*y^6-414558*y^5
              -62694*y^4-25515*y^3+255879*y^2+216513*y+98415) := by
          dsimp [c2, c3, c4, lastCoeff]
          unfold bad
          ring
        nlinarith [hid, hq]
      · left
        dsimp [c3]
        linarith
    have hbern := bern4_one_bad b c0 c1 c2 c3 c4 hb0 hb1 hc0 hc1 hc2 hc4 hcase
    have hid : coeff0 b z = b^2 *
        (c0*(1-b)^4+4*c1*b*(1-b)^3+6*c2*b^2*(1-b)^2
          +4*c3*b^3*(1-b)+c4*b^4) := by
      dsimp [y, c0, c1, c2, c3, c4]
      unfold coeff0 bad lastCoeff
      field_simp [hb]
      ring
    rw [hid]
    positivity

private theorem coeff1_nonneg (b z : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z) :
    0 ≤ coeff1 b z := by
  by_cases hb : b = 0
  · subst b
    norm_num [coeff1]
    positivity
  · have hbp : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    let y := z/b
    have hy : 0 ≤ y := by dsimp [y]; positivity
    let c0 : ℝ := 20/3
    let c1 := 30*y*(4*y+3)
    let c2 := 2/9*(20*y^3+1557*y^2+1026*y+594)
    let c3 := -6*bad y
    let c4 := lastCoeff y
    have hc0 : 0 ≤ c0 := by norm_num [c0]
    have hc1 : 0 ≤ c1 := by dsimp [c1]; positivity
    have hc2 : 0 < c2 := by dsimp [c2]; positivity
    have hc4 : 0 ≤ c4 := by dsimp [c4, lastCoeff]; positivity
    have hcase : 0 ≤ c3 ∨ 16*c3^2 ≤ 24*c2*c4 := by
      by_cases hp : 0 < bad y
      · right
        have hy6 : 6 ≤ y := (bad_pos_imp_six_lt y hy hp).le
        have hq := discPoly1_nonneg y hy6
        have hid : 24*c2*c4-16*c3^2 =
            16/3*(400*y^9+30708*y^8+11880*y^7-289872*y^6-869940*y^5
              +114453*y^4+1399680*y^3+1358127*y^2+669222*y+118098) := by
          dsimp [c2, c3, c4, lastCoeff]
          unfold bad
          ring
        nlinarith [hid, hq]
      · left
        dsimp [c3]
        linarith
    have hbern := bern4_one_bad b c0 c1 c2 c3 c4 hb0 hb1 hc0 hc1 hc2 hc4 hcase
    have hid : coeff1 b z = b^2 *
        (c0*(1-b)^4+4*c1*b*(1-b)^3+6*c2*b^2*(1-b)^2
          +4*c3*b^3*(1-b)+c4*b^4) := by
      dsimp [y, c0, c1, c2, c3, c4]
      unfold coeff1 bad lastCoeff
      field_simp [hb]
      ring
    rw [hid]
    positivity

private theorem coeff2_nonneg (b z : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z) :
    0 ≤ coeff2 b z := by
  by_cases hb : b = 0
  · subst b
    norm_num [coeff2]
    positivity
  · have hbp : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    let y := z/b
    have hy : 0 ≤ y := by dsimp [y]; positivity
    let c0 : ℝ := 0
    let c1 := 30*(2*y^2+3*y+3)
    let c2 := 10/9*(2*y^3+126*y^2+135*y+27)
    let c3 := -3*bad y
    let c4 := lastCoeff y
    have hc0 : 0 ≤ c0 := by norm_num [c0]
    have hc1 : 0 ≤ c1 := by dsimp [c1]; positivity
    have hc2 : 0 < c2 := by dsimp [c2]; positivity
    have hc4 : 0 ≤ c4 := by dsimp [c4, lastCoeff]; positivity
    have hcase : 0 ≤ c3 ∨ 16*c3^2 ≤ 24*c2*c4 := by
      by_cases hp : 0 < bad y
      · right
        have hy6 : 6 ≤ y := (bad_pos_imp_six_lt y hy hp).le
        have hq := discPoly2_nonneg y hy6
        have hid : 24*c2*c4-16*c3^2 =
            16/3*(200*y^9+12492*y^8+10260*y^7-127980*y^6-455382*y^5
              +177147*y^4+1425195*y^3+1102248*y^2+452709*y+19683) := by
          dsimp [c2, c3, c4, lastCoeff]
          unfold bad
          ring
        nlinarith [hid, hq]
      · left
        dsimp [c3]
        linarith
    have hbern := bern4_one_bad b c0 c1 c2 c3 c4 hb0 hb1 hc0 hc1 hc2 hc4 hcase
    have hid : coeff2 b z = b^2 *
        (c0*(1-b)^4+4*c1*b*(1-b)^3+6*c2*b^2*(1-b)^2
          +4*c3*b^3*(1-b)+c4*b^4) := by
      dsimp [y, c0, c1, c2, c3, c4]
      unfold coeff2 bad lastCoeff
      field_simp [hb]
      ring
    rw [hid]
    positivity

theorem coeff3_nonneg (b z : ℝ) (hb : 0 ≤ b) (hz : 0 ≤ z) :
    0 ≤ coeff3 b z := by
  unfold coeff3
  positivity

/-- Cubic Bernstein certificate in the normalized holding fraction `R`. -/
theorem cornerBernstein_nonneg (R b z : ℝ) (hR : 0 ≤ R) (hRb : R ≤ b)
    (hb1 : b ≤ 1) (hz : 0 ≤ z) :
    0 ≤ coeff0 b z*(b-R)^3 + 3*coeff1 b z*R*(b-R)^2
      +3*coeff2 b z*R^2*(b-R)+coeff3 b z*R^3 := by
  have hb0 : 0 ≤ b := le_trans hR hRb
  have hd : 0 ≤ b-R := sub_nonneg.mpr hRb
  have h0 := coeff0_nonneg b z hb0 hb1 hz
  have h1 := coeff1_nonneg b z hb0 hb1 hz
  have h2 := coeff2_nonneg b z hb0 hb1 hz
  have h3 := coeff3_nonneg b z hb0 hz
  positivity

set_option maxHeartbeats 2000000 in
-- Clearing the compactification denominators expands four nested renewal moments.
/-- The full geometric-return gap at the simultaneous lower moment corner.  The variables are
the compact state-return coordinates

`R = x/(x+u)`, `b = p+(1-p)R`, and `z = (1-p)v/(x+u)`.

Thus `0 ≤ R ≤ b < 1`.  Both excursions have the sharp Erlang-three moment quadruple. -/
theorem transformed_lowerCorner_k3 (R b z : ℝ) (hR : 0 ≤ R) (hRb : R ≤ b)
    (hb1 : b < 1) (hz : 0 ≤ z) :
    let u := 1-R
    let q := (1-b)/(1-R)
    let v := z/q
    let r := (b-R)/(1-b)
    0 ≤ geomGap r
      (kernelM1 R u) (kernelM2 R u (4/3*u^2))
        (kernelM3 R u (4/3*u^2) (20/9*u^3))
        (kernelM4 R u (4/3*u^2) (20/9*u^3) (40/9*u^4))
      (kernelM1 R v) (kernelM2 R v (4/3*v^2))
        (kernelM3 R v (4/3*v^2) (20/9*v^3))
        (kernelM4 R v (4/3*v^2) (20/9*v^3) (40/9*v^4)) := by
  dsimp only
  have hR1 : R < 1 := lt_of_le_of_lt hRb hb1
  have h1R : 0 < 1-R := sub_pos.mpr hR1
  have h1b : 0 < 1-b := sub_pos.mpr hb1
  have hb0 : 0 ≤ b := le_trans hR hRb
  by_cases hb : b = 0
  · have hR0 : R = 0 := by linarith
    subst R
    subst b
    norm_num [geomGap, geomM4, geomM3, geomM2, geomM1,
      kernelM1, kernelM2, kernelM3, kernelM4]
    ring_nf
    nlinarith [pow_nonneg hz 6]
  · have hbp : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    let T := coeff0 b z*(b-R)^3 + 3*coeff1 b z*R*(b-R)^2
      +3*coeff2 b z*R^2*(b-R)+coeff3 b z*R^3
    have hT : 0 ≤ T := by
      dsimp [T]
      exact cornerBernstein_nonneg R b z hR hRb hb1.le hz
    have hid :
        81*b^3*(1-b)^6 * geomGap ((b-R)/(1-b))
          (kernelM1 R (1-R)) (kernelM2 R (1-R) (4/3*(1-R)^2))
          (kernelM3 R (1-R) (4/3*(1-R)^2) (20/9*(1-R)^3))
          (kernelM4 R (1-R) (4/3*(1-R)^2) (20/9*(1-R)^3)
            (40/9*(1-R)^4))
          (kernelM1 R (z/((1-b)/(1-R))))
          (kernelM2 R (z/((1-b)/(1-R))) (4/3*(z/((1-b)/(1-R)))^2))
          (kernelM3 R (z/((1-b)/(1-R))) (4/3*(z/((1-b)/(1-R)))^2)
            (20/9*(z/((1-b)/(1-R)))^3))
          (kernelM4 R (z/((1-b)/(1-R))) (4/3*(z/((1-b)/(1-R)))^2)
            (20/9*(z/((1-b)/(1-R)))^3) (40/9*(z/((1-b)/(1-R)))^4)) =
        4*(1-R)^6*T := by
      dsimp [T]
      unfold coeff0 coeff1 coeff2 coeff3
      unfold geomGap geomM4 geomM3 geomM2 geomM1
      unfold kernelM1 kernelM2 kernelM3 kernelM4
      field_simp [hb, ne_of_gt h1b, ne_of_gt h1R]
      ring
    have hscaled : 0 ≤
        81*b^3*(1-b)^6 * geomGap ((b-R)/(1-b))
          (kernelM1 R (1-R)) (kernelM2 R (1-R) (4/3*(1-R)^2))
          (kernelM3 R (1-R) (4/3*(1-R)^2) (20/9*(1-R)^3))
          (kernelM4 R (1-R) (4/3*(1-R)^2) (20/9*(1-R)^3)
            (40/9*(1-R)^4))
          (kernelM1 R (z/((1-b)/(1-R))))
          (kernelM2 R (z/((1-b)/(1-R))) (4/3*(z/((1-b)/(1-R)))^2))
          (kernelM3 R (z/((1-b)/(1-R))) (4/3*(z/((1-b)/(1-R)))^2)
            (20/9*(z/((1-b)/(1-R)))^3))
          (kernelM4 R (z/((1-b)/(1-R))) (4/3*(z/((1-b)/(1-R)))^2)
            (20/9*(z/((1-b)/(1-R)))^3) (40/9*(z/((1-b)/(1-R)))^4)) := by
      rw [hid]
      positivity
    exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 81*b^3*(1-b)^6)).mp hscaled

/-- Scale-free version of the simultaneous lower-corner theorem in the original renewal
coordinates. -/
theorem lowerCorner_k3 (r x u v : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x)
    (hu : 0 < u) (hv : 0 ≤ v) :
    0 ≤ geomGap r
      (kernelM1 x u) (kernelM2 x u (4/3*u^2))
        (kernelM3 x u (4/3*u^2) (20/9*u^3))
        (kernelM4 x u (4/3*u^2) (20/9*u^3) (40/9*u^4))
      (kernelM1 x v) (kernelM2 x v (4/3*v^2))
        (kernelM3 x v (4/3*v^2) (20/9*v^3))
        (kernelM4 x v (4/3*v^2) (20/9*v^3) (40/9*v^4)) := by
  let l := x+u
  let R := x/l
  let b := (r+R)/(1+r)
  let z := v/((1+r)*l)
  have hl : 0 < l := by dsimp [l]; linarith
  have hr1 : 0 < 1+r := by linarith
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R < 1 := by
    dsimp [R, l]
    rw [div_lt_one hl]
    linarith
  have hRb : R ≤ b := by
    have hprod : 0 ≤ r*(1-R) := mul_nonneg hr (sub_nonneg.mpr hR1.le)
    dsimp [b]
    rw [le_div_iff₀ hr1]
    nlinarith
  have hb1 : b < 1 := by
    dsimp [b]
    rw [div_lt_one hr1]
    linarith
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hcorner := transformed_lowerCorner_k3 R b z hR0 hRb hb1 hz
  have hq : (1-b)/(1-R) = 1/(1+r) := by
    dsimp [b]
    field_simp [ne_of_gt hr1, ne_of_gt (sub_pos.mpr hR1)]
    ring
  have hvnorm : z/((1-b)/(1-R)) = v/l := by
    rw [hq]
    dsimp [z]
    field_simp [ne_of_gt hr1, ne_of_gt hl]
  have hrnorm : (b-R)/(1-b) = r := by
    rw [div_eq_iff (ne_of_gt (sub_pos.mpr hb1))]
    dsimp [b]
    field_simp [ne_of_gt hr1]
    ring
  have huNorm : 1-R = u/l := by
    dsimp [R, l]
    field_simp [ne_of_gt hl]
    ring
  dsimp only at hcorner
  rw [hvnorm, hrnorm, huNorm] at hcorner
  have hid : l^6 * geomGap r
      (kernelM1 R (u/l)) (kernelM2 R (u/l) (4/3*(u/l)^2))
        (kernelM3 R (u/l) (4/3*(u/l)^2) (20/9*(u/l)^3))
        (kernelM4 R (u/l) (4/3*(u/l)^2) (20/9*(u/l)^3) (40/9*(u/l)^4))
      (kernelM1 R (v/l)) (kernelM2 R (v/l) (4/3*(v/l)^2))
        (kernelM3 R (v/l) (4/3*(v/l)^2) (20/9*(v/l)^3))
        (kernelM4 R (v/l) (4/3*(v/l)^2) (20/9*(v/l)^3) (40/9*(v/l)^4)) =
    geomGap r
      (kernelM1 x u) (kernelM2 x u (4/3*u^2))
        (kernelM3 x u (4/3*u^2) (20/9*u^3))
        (kernelM4 x u (4/3*u^2) (20/9*u^3) (40/9*u^4))
      (kernelM1 x v) (kernelM2 x v (4/3*v^2))
        (kernelM3 x v (4/3*v^2) (20/9*v^3))
        (kernelM4 x v (4/3*v^2) (20/9*v^3) (40/9*v^4)) := by
    dsimp [R, l]
    unfold geomGap geomM4 geomM3 geomM2 geomM1
    unfold kernelM1 kernelM2 kernelM3 kernelM4
    field_simp [ne_of_gt hl]
  rw [← hid]
  positivity

/-! ## Convexity of the first KKT layer -/

/-- Renewal gap after replacing both kernel fourth moments by their sharp lower bounds. -/
noncomputable def reducedGeomGap
    (r a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  geomGap r a1 a2 a3 (7*a3^2/(6*a2)) b1 b2 b3 (7*b3^2/(6*b2))

noncomputable def hAA (r a1 a2 b1 b2 : ℝ) : ℝ :=
  14*r*(2*a1^2*r^2+2*a1*b1*r+b2)/a2

noncomputable def hAB (r : ℝ) : ℝ := -14*r

noncomputable def hBB (r a1 a2 b1 b2 : ℝ) : ℝ :=
  14*r*(2*a1^2*r+2*a1*b1+a2)/b2

/-- Determinant of the Hessian in the two third moments. -/
theorem hessian_det (r a1 a2 b1 b2 : ℝ) (ha2 : a2 ≠ 0) (hb2 : b2 ≠ 0) :
    hAA r a1 a2 b1 b2*hBB r a1 a2 b1 b2-(hAB r)^2 =
      392*a1*r^2*(a1*r+b1)*(2*a1^2*r^2+2*a1*b1*r+a2*r+b2)/(a2*b2) := by
  unfold hAA hAB hBB
  field_simp [ha2, hb2]
  ring

/-- Under the natural strict positivity hypotheses, the Hessian is positive definite. -/
theorem hessian_quadratic_pos (r a1 a2 b1 b2 s t : ℝ)
    (hr : 0 < r) (ha1 : 0 < a1) (ha2 : 0 < a2) (hb1 : 0 ≤ b1) (hb2 : 0 < b2)
    (hst : s ≠ 0 ∨ t ≠ 0) :
    0 < hAA r a1 a2 b1 b2*s^2 + 2*hAB r*s*t + hBB r a1 a2 b1 b2*t^2 := by
  have hU : 0 < 2*a1^2*r^2+2*a1*b1*r+b2 := by positivity
  have hV : 0 < 2*a1^2*r+2*a1*b1+a2 := by positivity
  have hhaa : 0 < hAA r a1 a2 b1 b2 := by unfold hAA; positivity
  have hhbb : 0 < hBB r a1 a2 b1 b2 := by unfold hBB; positivity
  have hdetid := hessian_det r a1 a2 b1 b2 ha2.ne' hb2.ne'
  have hdet : 0 < hAA r a1 a2 b1 b2*hBB r a1 a2 b1 b2-(hAB r)^2 := by
    rw [hdetid]
    positivity
  let Q := hAA r a1 a2 b1 b2*s^2 + 2*hAB r*s*t + hBB r a1 a2 b1 b2*t^2
  have hid : hAA r a1 a2 b1 b2*Q =
      (hAA r a1 a2 b1 b2*s+hAB r*t)^2
        +(hAA r a1 a2 b1 b2*hBB r a1 a2 b1 b2-(hAB r)^2)*t^2 := by
    dsimp [Q]
    ring
  change 0 < Q
  rcases hst with hs | ht
  · by_cases ht0 : t = 0
    · subst t
      dsimp [Q]
      have hs2 : 0 < s^2 := sq_pos_of_ne_zero hs
      simpa using mul_pos hhaa hs2
    · have ht2 : 0 < t^2 := sq_pos_of_ne_zero ht0
      have hscaled : 0 < hAA r a1 a2 b1 b2*Q := by
        rw [hid]
        positivity
      exact (mul_pos_iff_of_pos_left hhaa).mp hscaled
  · have ht2 : 0 < t^2 := sq_pos_of_ne_zero ht
    have hscaled : 0 < hAA r a1 a2 b1 b2*Q := by
      rw [hid]
      positivity
    exact (mul_pos_iff_of_pos_left hhaa).mp hscaled

/-- Exact second-difference formula showing that `reducedGeomGap` has the Hessian above. -/
theorem reducedGeomGap_secondDifference
    (r a1 a2 a3 b1 b2 b3 s t : ℝ) (ha2 : a2 ≠ 0) (hb2 : b2 ≠ 0) :
    reducedGeomGap r a1 a2 (a3+s) b1 b2 (b3+t)
      +reducedGeomGap r a1 a2 (a3-s) b1 b2 (b3-t)
      -2*reducedGeomGap r a1 a2 a3 b1 b2 b3 =
    hAA r a1 a2 b1 b2*s^2+2*hAB r*s*t+hBB r a1 a2 b1 b2*t^2 := by
  unfold reducedGeomGap hAA hAB hBB
  unfold geomGap geomM4 geomM3 geomM2 geomM1
  field_simp [ha2, hb2]
  ring

end SSP.K3S4Corner
