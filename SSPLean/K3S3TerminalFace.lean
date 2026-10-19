import SSPLean.K3S3Cyclic

/-!
# The terminal face in the exceptional three-stage case

The terminal-face numerator is a quadratic in the terminal mixture weight.
Its middle Bernstein coefficient is controlled either by the gradient at
`q = 0` or by the increase of the gradient from `q = 0` to `q = 1`; its last
coefficient is controlled by the gradient at `q = 1`.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

private noncomputable def faceBThreeCore (T X Z q : ℝ) : ℝ :=
  27*T^4*X*q^2-150*T^4*q^2+24*T^3*X^2*q^2+24*T^3*X*Z*q^2
    +216*T^3*X*q^2-80*T^3*q^2+15*T^2*X^3*q+30*T^2*X^2*Z*q
    -10*T^2*X^2*q^2+246*T^2*X^2*q+15*T^2*X*Z^2*q
    +800*T^2*X*Z*q^2-456*T^2*X*Z*q+240*T^2*X*q^2
    +156*T^2*X*q+160*T^2*q^2-80*T^2*q+20*T*X^3*q
    +520*T*X^2*Z*q+420*T*X^2*q+500*T*X*Z^2*q+960*T*X*Z*q
    +720*T*X*q+320*T*q+15*X^4+30*X^3*Z+215*X^3+15*X^2*Z^2
    +40*X^2*Z+520*X^2+500*X*Z^2+160*X*Z+480*X+160

private noncomputable def faceBThreeB0 (X Z : ℝ) : ℝ :=
  5*(3*X^4+6*X^3*Z+43*X^3+3*X^2*Z^2+8*X^2*Z+104*X^2
    +100*X*Z^2+32*X*Z+96*X+32)

/-- Twice the middle Bernstein coefficient. -/
private noncomputable def faceBThreeMid (T X Z : ℝ) : ℝ :=
  15*T^2*X^3+30*T^2*X^2*Z+246*T^2*X^2+15*T^2*X*Z^2
    -456*T^2*X*Z+156*T^2*X-80*T^2+20*T*X^3+520*T*X^2*Z
    +420*T*X^2+500*T*X*Z^2+960*T*X*Z+720*T*X+320*T
    +30*X^4+60*X^3*Z+430*X^3+30*X^2*Z^2+80*X^2*Z
    +1040*X^2+1000*X*Z^2+320*X*Z+960*X+320

private noncomputable def faceBThreeB2 (T X Z : ℝ) : ℝ :=
  27*T^4*X-150*T^4+24*T^3*X^2+24*T^3*X*Z+216*T^3*X-80*T^3
    +15*T^2*X^3+30*T^2*X^2*Z+236*T^2*X^2+15*T^2*X*Z^2
    +344*T^2*X*Z+396*T^2*X+80*T^2+20*T*X^3+520*T*X^2*Z
    +420*T*X^2+500*T*X*Z^2+960*T*X*Z+720*T*X+320*T
    +15*X^4+30*X^3*Z+215*X^3+15*X^2*Z^2+40*X^2*Z
    +520*X^2+500*X*Z^2+160*X*Z+480*X+160

private noncomputable def faceBThreeGrad0 (T X Z : ℝ) : ℝ :=
  -75*T*X-100*T+72*X^2+72*X*Z+156*X+64

private noncomputable def faceBThreeGrad1 (T X Z : ℝ) : ℝ :=
  -3*T^3-52*T^2+33*T*X-36*T+72*X^2+72*X*Z+156*X+64

private theorem faceBThreeCore_bernstein (T X Z q : ℝ) :
    faceBThreeCore T X Z q =
      faceBThreeB0 X Z*(1-q)^2+faceBThreeMid T X Z*q*(1-q)
        +faceBThreeB2 T X Z*q^2 := by
  unfold faceBThreeCore faceBThreeB0 faceBThreeMid faceBThreeB2
  ring

private theorem faceBThreeGrad_affine (a T Y q : ℝ) :
    uniformGradB 3 a T Y q =
      (1-q)*faceBThreeGrad0 T (a*Y) ((1-a)*Y)
        +q*faceBThreeGrad1 T (a*Y) ((1-a)*Y) := by
  unfold uniformGradB faceBThreeGrad0 faceBThreeGrad1
  ring

private theorem faceBThreeB0_nonneg (X Z : ℝ) (hX : 0 ≤ X) (hZ : 0 ≤ Z) :
    0 ≤ faceBThreeB0 X Z := by
  unfold faceBThreeB0
  positivity

private noncomputable def faceBThreeMidA (X Z : ℝ) : ℝ :=
  15*X^3+30*X^2*Z+246*X^2+15*X*Z^2-456*X*Z+156*X-80

private noncomputable def faceBThreeMidB (X Z : ℝ) : ℝ :=
  20*(X^3+26*X^2*Z+21*X^2+25*X*Z^2+48*X*Z+36*X+16)

private noncomputable def faceBThreeMidC (X Z : ℝ) : ℝ :=
  10*(3*X^4+6*X^3*Z+43*X^3+3*X^2*Z^2+8*X^2*Z+104*X^2
    +100*X*Z^2+32*X*Z+96*X+32)

private theorem faceBThreeMid_of_grad0_nonneg
    (T X Z : ℝ) (hT : 0 ≤ T) (hX : 0 < X) (hZ : 0 ≤ Z)
    (hg : 0 ≤ faceBThreeGrad0 T X Z) :
    0 ≤ faceBThreeMid T X Z := by
  let A := faceBThreeMidA X Z
  let B := faceBThreeMidB X Z
  let C := faceBThreeMidC X Z
  let D := 72*X^2+72*X*Z+156*X+64
  let K := 75*X+100
  have hB : 0 ≤ B := by dsimp [B, faceBThreeMidB]; positivity
  have hC : 0 ≤ C := by dsimp [C, faceBThreeMidC]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hKT : K*T ≤ D := by
    dsimp [K, D, faceBThreeGrad0] at hg ⊢
    linarith
  have hform : faceBThreeMid T X Z = A*T^2+B*T+C := by
    dsimp [A, B, C, faceBThreeMidA, faceBThreeMidB, faceBThreeMidC]
    unfold faceBThreeMid
    ring
  by_cases hA : 0 ≤ A
  · rw [hform]
    positivity
  · have hA' : A < 0 := lt_of_not_ge hA
    have hE : 0 ≤ A*D^2+B*D*K+C*K^2 := by
      rw [show A*D^2+B*D*K+C*K^2 = 2*(
        38880*X^7+155520*X^6*Z+944487*X^6+233280*X^5*Z^2
          +2225502*X^5*Z+6176439*X^5+155520*X^4*Z^3
          +1617543*X^4*Z^2+8409384*X^4*Z+18238488*X^4
          +38880*X^3*Z^4+336528*X^3*Z^3+7898940*X^3*Z^2
          +14752704*X^3*Z+28871280*X^3+1869120*X^2*Z^3
          +14047152*X^2*Z^2+13041024*X^2*Z+25731232*X^2
          +6630720*X*Z^2+4521472*X*Z+12288768*X+2460160) by
        dsimp [A, B, C, D, K, faceBThreeMidA, faceBThreeMidB,
          faceBThreeMidC]
        ring]
      positivity
    have hlast : 0 ≤ A*D*K*T*(K*T-D) := by
      have hAK : A*(K*T-D) ≥ 0 := mul_nonneg_of_nonpos_of_nonpos hA'.le (by linarith)
      have hDKT : 0 ≤ D*K*T := by positivity
      nlinarith [mul_nonneg hAK hDKT]
    have hscaled : 0 ≤ D*K^2*(A*T^2+B*T+C) := by
      rw [show D*K^2*(A*T^2+B*T+C) =
          (D-K*T)*K^2*C+K*T*(A*D^2+B*D*K+C*K^2)
            +A*D*K*T*(K*T-D) by ring]
      positivity
    rw [hform]
    exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < D*K^2)).mp hscaled

private noncomputable def faceBThreeMidLinear (T X : ℝ) : ℝ :=
  30*T^2*X-456*T^2+520*T*X+960*T+60*X^2+80*X+320

private noncomputable def faceBThreeMidConst (T X : ℝ) : ℝ :=
  15*T^2*X^3+246*T^2*X^2+156*T^2*X-80*T^2
    +20*T*X^3+420*T*X^2+720*T*X+320*T
    +30*X^4+430*X^3+1040*X^2+960*X+320

private theorem faceBThreeMid_of_grad_slope
    (T X Z : ℝ) (hT : 0 < T) (hX : 0 < X) (hZ : 0 ≤ Z)
    (hslope : faceBThreeGrad0 T X Z < faceBThreeGrad1 T X Z) :
    0 ≤ faceBThreeMid T X Z := by
  have hs : 3*T^2+52*T < 108*X+64 := by
    have hm : 0 < T*(108*X+64-3*T^2-52*T) := by
      dsimp [faceBThreeGrad0, faceBThreeGrad1] at hslope
      nlinarith
    rcases (mul_pos_iff.mp hm) with hpp | hnn
    · linarith [hpp.2]
    · linarith [hnn.1]
  have hlin : 0 ≤ faceBThreeMidLinear T X := by
    let H := 3*T^2+52*T-64
    by_cases hH : H ≤ 0
    · have hT2 : T ≤ 2 := by
        dsimp [H] at hH
        nlinarith [sq_nonneg T]
      have hsq : 0 ≤ 2*T-T^2 := by nlinarith [mul_nonneg hT.le (sub_nonneg.mpr hT2)]
      rw [show faceBThreeMidLinear T X =
          30*T^2*X+520*T*X+60*X^2+80*X+320
            +456*(2*T-T^2)+48*T by
        unfold faceBThreeMidLinear; ring]
      positivity
    · have hHp : 0 < H := lt_of_not_ge hH
      let x0 := H/108
      have hx0 : 0 < x0 := by dsimp [x0]; positivity
      have hx0X : x0 ≤ X := by dsimp [x0, H]; linarith
      have hquad : 0 ≤ 29640*T^2-203392*T+637760 := by
        nlinarith [sq_nonneg (59280*T-203392)]
      have hpoly : 0 ≤ 855*T^4+29640*T^3-203392*T^2
          +637760*T+285440 := by
        have : 0 ≤ T*(29640*T^2-203392*T+637760) := mul_nonneg hT.le hquad
        rw [show 855*T^4+29640*T^3-203392*T^2+637760*T+285440 =
            855*T^4+T*(29640*T^2-203392*T+637760)+285440 by ring]
        positivity
      have hbase : 0 ≤ faceBThreeMidLinear T x0 := by
        have hid : 108^2*faceBThreeMidLinear T x0 =
            12*(855*T^4+29640*T^3-203392*T^2+637760*T+285440) := by
          dsimp [x0, H]
          unfold faceBThreeMidLinear
          ring
        have hscl : 0 ≤ 108^2*faceBThreeMidLinear T x0 := by rw [hid]; positivity
        norm_num at hscl ⊢
        linarith
      have hdiff : 0 ≤ faceBThreeMidLinear T X-faceBThreeMidLinear T x0 := by
        rw [show faceBThreeMidLinear T X-faceBThreeMidLinear T x0 =
            (X-x0)*(60*(X+x0)+30*T^2+520*T+80) by
          unfold faceBThreeMidLinear; ring]
        positivity
      linarith
  have hconst : 0 ≤ faceBThreeMidConst T X := by
    let H := 3*T^2+52*T-64
    by_cases hH : H ≤ 0
    · have hT2 : T ≤ 2 := by
        dsimp [H] at hH
        nlinarith [sq_nonneg T]
      have hsq : 0 ≤ 2*T-T^2 := by nlinarith [mul_nonneg hT.le (sub_nonneg.mpr hT2)]
      rw [show faceBThreeMidConst T X =
          15*T^2*X^3+246*T^2*X^2+156*T^2*X
            +20*T*X^3+420*T*X^2+720*T*X+160*T
            +30*X^4+430*X^3+1040*X^2+960*X+320
            +80*(2*T-T^2) by
        unfold faceBThreeMidConst; ring]
      positivity
    · have hHp : 0 < H := lt_of_not_ge hH
      let x0 := H/108
      have hx0 : 0 < x0 := by dsimp [x0]; positivity
      have hx0X : x0 ≤ X := by dsimp [x0, H]; linarith
      have hpoly : 0 ≤
          7695*T^8+416880*T^7+11818116*T^6+203989488*T^5
            +1561006016*T^4+1980494080*T^3+2512674816*T^2
            +2528296960*T+692510720 := by positivity
      have hbase : 0 ≤ faceBThreeMidConst T x0 := by
        have hid : 108^4*faceBThreeMidConst T x0 = 6*(
            7695*T^8+416880*T^7+11818116*T^6+203989488*T^5
              +1561006016*T^4+1980494080*T^3+2512674816*T^2
              +2528296960*T+692510720) := by
          dsimp [x0, H]
          unfold faceBThreeMidConst
          ring
        have hscl : 0 ≤ 108^4*faceBThreeMidConst T x0 := by rw [hid]; positivity
        norm_num at hscl ⊢
        linarith
      have hdiff : 0 ≤ faceBThreeMidConst T X-faceBThreeMidConst T x0 := by
        rw [show faceBThreeMidConst T X-faceBThreeMidConst T x0 =
            (X-x0)*(30*(X^3+X^2*x0+X*x0^2+x0^3)
              +(15*T^2+20*T+430)*(X^2+X*x0+x0^2)
              +(246*T^2+420*T+1040)*(X+x0)
              +(156*T^2+720*T+960)) by
          unfold faceBThreeMidConst; ring]
        positivity
      linarith
  rw [show faceBThreeMid T X Z = faceBThreeMidConst T X
      +X*Z*faceBThreeMidLinear T X
      +5*X*(3*T^2+100*T+6*X+200)*Z^2 by
    unfold faceBThreeMid faceBThreeMidConst faceBThreeMidLinear
    ring]
  positivity

private theorem faceBThreeB2_of_grad1_pos
    (T X Z : ℝ) (hT : 0 ≤ T) (hX : 0 ≤ X) (hZ : 0 ≤ Z)
    (hg : 0 < faceBThreeGrad1 T X Z) :
    0 ≤ faceBThreeB2 T X Z := by
  let L := 2+X/2+T/10+8*T^2/3+T^3/3
  have hL : 0 < L := by dsimp [L]; positivity
  have hrem : 0 ≤
      30*T^6+760*T^5+480*T^4*X+29*T^4+2325*T^3*X+176*T^3
        +450*T^2*X^3+900*T^2*X^2*Z+1320*T^2*X^2+450*T^2*X*Z^2
        +4560*T^2*X*Z+81*T^2*X+508*T^2+600*T*X^3
        +15600*T*X^2*Z+11889*T*X^2+15000*T*X*Z^2
        +28584*T*X*Z+19692*T*X+11568*T+450*X^4+900*X^3*Z
        +5370*X^3+450*X^2*Z^2+120*X^2*Z+8940*X^2
        +15000*X*Z^2+480*X*Z+4080*X+960 := by positivity
  rw [show faceBThreeB2 T X Z = L*faceBThreeGrad1 T X Z + (1/30)*(
      30*T^6+760*T^5+480*T^4*X+29*T^4+2325*T^3*X+176*T^3
        +450*T^2*X^3+900*T^2*X^2*Z+1320*T^2*X^2+450*T^2*X*Z^2
        +4560*T^2*X*Z+81*T^2*X+508*T^2+600*T*X^3
        +15600*T*X^2*Z+11889*T*X^2+15000*T*X*Z^2
        +28584*T*X*Z+19692*T*X+11568*T+450*X^4+900*X^3*Z
        +5370*X^3+450*X^2*Z^2+120*X^2*Z+8940*X^2
        +15000*X*Z^2+480*X*Z+4080*X+960) by
    dsimp [L]
    unfold faceBThreeB2 faceBThreeGrad1
    ring]
  positivity

private theorem faceBThree_factor (a T Y q : ℝ) :
    uniformFaceBNum 3 a T Y q =
      60*uniformSideFactor 3 a T Y q*
        faceBThreeCore T (a*Y) ((1-a)*Y) q := by
  unfold uniformFaceBNum uniformHBB uniformGradB uniformCornerPoly
  unfold uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num
  unfold uniformSideFactor faceBThreeCore
  ring

private theorem faceBThreeCore_nonneg_at_grad_zero
    (a T Y q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hgrad : uniformGradB 3 a T Y q = 0) :
    0 ≤ faceBThreeCore T (a*Y) ((1-a)*Y) q := by
  have hcorner : 0 ≤ uniformCornerPoly 3 a T Y q := by
    have hgap := uniformSharpGap_three_nonneg a T Y q ha.le ha1 hT hY hq hq1
    have hid := uniformSharpGap_eq_cornerPoly 3 a T Y q
      (by norm_num) (by norm_num) (by norm_num) hT.ne' hY.ne' hq.ne'
      (by positivity)
    norm_num at hid
    nlinarith
  have hH : 0 ≤ uniformHBB 3 a T Y q := by
    rw [show uniformHBB 3 a T Y q =
        3*T^2*q+100*T*q+75*a*Y+100 by unfold uniformHBB; ring]
    positivity
  have hnum : 0 ≤ uniformFaceBNum 3 a T Y q := by
    unfold uniformFaceBNum
    rw [hgrad]
    simpa using mul_nonneg hH hcorner
  rw [faceBThree_factor] at hnum
  have hside : 0 < uniformSideFactor 3 a T Y q := by
    rw [show uniformSideFactor 3 a T Y q =
        3*T^2*q+4*T*q+3*a*Y+4 by unfold uniformSideFactor; ring]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by positivity :
    0 < 60*uniformSideFactor 3 a T Y q)).mp hnum

private theorem faceBThree_initial_segment
    (a T Y q qstar : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (_hT : 0 < T) (hY : 0 < Y)
    (hq : 0 ≤ q) (hqqstar : q ≤ qstar) (hqstar1 : qstar ≤ 1)
    (hmid : 0 ≤ faceBThreeMid T (a*Y) ((1-a)*Y))
    (hboundary : 0 ≤ faceBThreeCore T (a*Y) ((1-a)*Y) qstar) :
    0 ≤ faceBThreeCore T (a*Y) ((1-a)*Y) q := by
  let X := a*Y
  let Z := (1-a)*Y
  have hX : 0 < X := by dsimp [X]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have h0 := faceBThreeB0_nonneg X Z hX.le hZ
  have hqstar : 0 ≤ qstar := le_trans hq hqqstar
  by_cases hz : qstar = 0
  · have hqz : q = 0 := by linarith
    subst q
    change 0 ≤ faceBThreeCore T X Z 0
    rw [faceBThreeCore_bernstein]
    norm_num
    exact h0
  · have hqstarpos : 0 < qstar := lt_of_le_of_ne hqstar (Ne.symm hz)
    have hid : qstar^2*faceBThreeCore T X Z q =
        faceBThreeB0 X Z*(qstar-q)^2
          +(2*(1-qstar)*faceBThreeB0 X Z
            +qstar*faceBThreeMid T X Z)*q*(qstar-q)
          +faceBThreeCore T X Z qstar*q^2 := by
      rw [faceBThreeCore_bernstein, faceBThreeCore_bernstein]
      ring
    have hscaled : 0 ≤ qstar^2*faceBThreeCore T X Z q := by
      rw [hid]
      dsimp [X, Z] at hmid hboundary ⊢
      positivity
    dsimp [X, Z] at hscaled ⊢
    exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos hqstarpos)).mp hscaled

private theorem faceBThreeCore_nonneg_of_grad_pos
    (a T Y q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hgrad : 0 < uniformGradB 3 a T Y q) :
    0 ≤ faceBThreeCore T (a*Y) ((1-a)*Y) q := by
  let X := a*Y
  let Z := (1-a)*Y
  have hX : 0 < X := by dsimp [X]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hgrad' : 0 < (1-q)*faceBThreeGrad0 T X Z+q*faceBThreeGrad1 T X Z := by
    dsimp [X, Z]
    rw [← faceBThreeGrad_affine]
    exact hgrad
  have h0 := faceBThreeB0_nonneg X Z hX.le hZ
  by_cases hg0 : 0 ≤ faceBThreeGrad0 T X Z
  · have hmid := faceBThreeMid_of_grad0_nonneg T X Z hT.le hX hZ hg0
    by_cases hg1 : 0 < faceBThreeGrad1 T X Z
    · have h2 := faceBThreeB2_of_grad1_pos T X Z hT.le hX.le hZ hg1
      rw [faceBThreeCore_bernstein]
      positivity
    · have hg1' : faceBThreeGrad1 T X Z ≤ 0 := le_of_not_gt hg1
      have hg0' : 0 < faceBThreeGrad0 T X Z := by
        by_contra hn
        have hg0n : faceBThreeGrad0 T X Z ≤ 0 := le_of_not_gt hn
        have hl : (1-q)*faceBThreeGrad0 T X Z ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq1) hg0n
        have hr : q*faceBThreeGrad1 T X Z ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hq.le hg1'
        linarith
      let qstar := faceBThreeGrad0 T X Z /
        (faceBThreeGrad0 T X Z-faceBThreeGrad1 T X Z)
      have hden : 0 < faceBThreeGrad0 T X Z-faceBThreeGrad1 T X Z := by linarith
      have hqstar : 0 < qstar := by dsimp [qstar]; positivity
      have hqstar1 : qstar ≤ 1 := by
        dsimp [qstar]
        rw [div_le_one hden]
        linarith
      have hqqstar : q ≤ qstar := by
        dsimp [qstar]
        rw [le_div_iff₀ hden]
        nlinarith
      have hGstar : uniformGradB 3 a T Y qstar = 0 := by
        rw [faceBThreeGrad_affine]
        change (1-qstar)*faceBThreeGrad0 T X Z
          +qstar*faceBThreeGrad1 T X Z = 0
        dsimp [qstar]
        field_simp [hden.ne']
        ring
      have hboundary := faceBThreeCore_nonneg_at_grad_zero
        a T Y qstar ha ha1 hT hY hqstar hqstar1 hGstar
      exact faceBThree_initial_segment a T Y q qstar ha ha1 hT hY hq.le
        hqqstar hqstar1 (by simpa [X, Z] using hmid) hboundary
  · have hg0' : faceBThreeGrad0 T X Z < 0 := lt_of_not_ge hg0
    have hg1 : 0 < faceBThreeGrad1 T X Z := by
      by_contra hn
      have hg1n : faceBThreeGrad1 T X Z ≤ 0 := le_of_not_gt hn
      have hl : (1-q)*faceBThreeGrad0 T X Z ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq1) hg0'.le
      have hr : q*faceBThreeGrad1 T X Z ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hq.le hg1n
      linarith
    have hmid := faceBThreeMid_of_grad_slope T X Z hT hX hZ (by linarith)
    have h2 := faceBThreeB2_of_grad1_pos T X Z hT.le hX.le hZ hg1
    rw [faceBThreeCore_bernstein]
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem uniformSharpFaceB_three_num_identity
    (a T Y q : ℝ) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hq : q ≠ 0) (hsum : Y+a ≠ 0) :
    T^2*3*q*4*2^4*uniformSharpFaceB 3 a T Y q =
      4*uniformFaceBNum 3 a T Y q := by
  have hgap := uniformSharpGap_eq_cornerPoly 3 a T Y q
    (by norm_num) (by norm_num) (by norm_num) hT hY hq hsum
  unfold uniformSharpFaceB sharpFaceB sharpGradB sharpThird excursionGradB
    excursionHBB excursionReducedGap stageGap hessianCore
  unfold SSP.K3S4Renewal.geomM4 SSP.K3S4Renewal.geomM3
    SSP.K3S4Renewal.geomM2 SSP.K3S4Renewal.geomM1
  unfold SSP.K3S4Renewal.kernelM1 SSP.K3S4Renewal.kernelM2
    SSP.K3S4Renewal.kernelM3 SSP.K3S4Renewal.kernelM4
  unfold uniformFaceBNum uniformHBB uniformGradB
  have hsq : a*Y*2+a^2+Y^2 ≠ 0 := by
    convert pow_ne_zero 2 hsum using 1
    all_goals ring
  field_simp [hT, hY, hq, hsum, hsq]
  rw [← hgap]
  unfold uniformSharpGap
  ring_nf

/-- The normalized terminal-face certificate follows from the active-gradient
condition alone at the exceptional stage `n = 3`. -/
theorem uniformSharpFaceB_three_nonneg_of_grad
    (a T Y q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hgrad : 0 < uniformGradB 3 a T Y q) :
    0 ≤ uniformSharpFaceB 3 a T Y q := by
  have hcore := faceBThreeCore_nonneg_of_grad_pos
    a T Y q ha ha1 hT hY hq hq1 hgrad
  have hside : 0 < uniformSideFactor 3 a T Y q := by
    rw [show uniformSideFactor 3 a T Y q =
        3*T^2*q+4*T*q+3*a*Y+4 by unfold uniformSideFactor; ring]
    positivity
  have hnum : 0 ≤ uniformFaceBNum 3 a T Y q := by
    rw [faceBThree_factor]
    positivity
  have hid := uniformSharpFaceB_three_num_identity a T Y q
    hT.ne' hY.ne' hq.ne' (by positivity)
  have hrhs : 0 ≤ 4*uniformFaceBNum 3 a T Y q := by positivity
  rw [← hid] at hrhs
  exact (mul_nonneg_iff_of_pos_left (by positivity :
    0 < T^2*3*q*4*2^4)).mp hrhs

/-- KKT-facing form of `uniformSharpFaceB_three_nonneg_of_grad`. -/
theorem uniformSharpFaceB_three_nonneg
    (a T Y q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hgrad : 0 < uniformGradB 3 a T Y q)
    (_hterminal : 0 ≤ uniformTerminalSide 3 a T Y q) :
    0 ≤ uniformSharpFaceB 3 a T Y q :=
  uniformSharpFaceB_three_nonneg_of_grad a T Y q ha ha1 hT hY hq hq1 hgrad

end SSP.K3AllStages
