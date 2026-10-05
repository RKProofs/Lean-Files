import SSPLean.K3AllStagesFaceBasic

/-!
# The return face in the exceptional three-stage case

At `n = 3` the return-face numerator has a particularly small cubic core.
The proof below splits at `T = 2` and, on the unbounded chart, at `X = T`.
In each chart the polynomial is a nested Bernstein polynomial.  Only two
coefficients are not coefficientwise positive; both are elementary positive
quadratics after the indicated split.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

noncomputable def uniformFaceAThreeCore (X T q : ℝ) : ℝ :=
  15*T^6*q^2+20*T^5*q^2-240*T^4*X*q^3+171*T^4*X*q^2+15*T^4*X*q
    -550*T^4*q^2+500*T^4*q-320*T^3*X*q^3+984*T^3*X*q^2-984*T^3*X*q
    +240*T^3*q^2-640*T^3*q-186*T^2*X^2*q^2+702*T^2*X^2*q
    -208*T^2*X*q^2+1164*T^2*X*q+160*T^2*q^2+240*T^2*q
    +228*T*X^2*q+464*T*X*q+320*T*q+27*X^3+264*X^2+352*X+160

private theorem n3_return_low_exception_nonneg (X : ℝ) (hX : 0 ≤ X) :
    0 ≤ 81*X^3+4056*X^2-992*X+4960 := by
  rcases le_total X 1 with hX1 | h1X
  · have : 0 ≤ 81*X^3+4056*X^2 := by positivity
    nlinarith
  · have hXX : X ≤ X^2 := by
      nlinarith [mul_nonneg hX (sub_nonneg.mpr h1X)]
    have : 0 ≤ 81*X^3 := by positivity
    nlinarith

private theorem n3_return_low_nonneg (X T q : ℝ)
    (hX : 0 ≤ X) (hT : 0 ≤ T) (hT2 : T ≤ 2)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ uniformFaceAThreeCore X T q := by
  let t := T/2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  let C0 := cornerBern6
    (27*X^3+264*X^2+352*X+160)
    (27*X^3+264*X^2+352*X+160)
    (27*X^3+264*X^2+352*X+160)
    (27*X^3+264*X^2+352*X+160)
    (27*X^3+264*X^2+352*X+160)
    (27*X^3+264*X^2+352*X+160)
    (27*X^3+264*X^2+352*X+160) t
  let C1 := cornerBern6
    (27*X^3+264*X^2+352*X+160)
    ((243*X^3+2604*X^2+3632*X+1760)/9)
    ((1215*X^3+16968*X^2+25136*X+11360)/45)
    ((405*X^3+7908*X^2+10288*X+3680)/15)
    ((1215*X^3+33288*X^2+29680*X+12000)/45)
    ((243*X^3+9132*X^2+3232*X+5280)/9)
    ((81*X^3+4056*X^2-992*X+4960)/3) t
  let C2 := cornerBern6
    (27*X^3+264*X^2+352*X+160)
    ((243*X^3+2832*X^2+4096*X+2080)/9)
    ((1215*X^3+21312*X^2+33600*X+16160)/45)
    ((405*X^3+11112*X^2+16432*X+6080)/15)
    ((1215*X^3+50232*X^2+64880*X+17600)/45)
    ((81*X^3+4800*X^2+5392*X+1600)/3)
    ((81*X^3+6576*X^2+6736*X+4800)/3) t
  let C3 := cornerBern6
    (27*X^3+264*X^2+352*X+160)
    ((81*X^3+1020*X^2+1520*X+800)/3)
    ((405*X^3+8304*X^2+13744*X+7200)/15)
    ((135*X^3+4524*X^2+7264*X+3200)/5)
    ((405*X^3+20904*X^2+28960*X+8000)/15)
    (X*(81*X^2+6060*X+6320)/3)
    (3*X*(9*X^2+928*X+560)) t
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    apply cornerBern6_nonneg <;> first | assumption | positivity
  have hC1 : 0 ≤ C1 := by
    have he := n3_return_low_exception_nonneg X hX
    dsimp [C1]
    apply cornerBern6_nonneg <;> first | assumption | positivity
  have hC2 : 0 ≤ C2 := by
    dsimp [C2]
    apply cornerBern6_nonneg <;> first | assumption | positivity
  have hC3 : 0 ≤ C3 := by
    dsimp [C3]
    apply cornerBern6_nonneg <;> first | assumption | positivity
  have hid : uniformFaceAThreeCore X (2*t) q =
      cornerBern3 C0 C1 C2 C3 q := by
    dsimp [uniformFaceAThreeCore, C0, C1, C2, C3, cornerBern6, cornerBern3]
    ring
  rw [show (2: ℝ)*t = T by dsimp [t]; ring] at hid
  rw [hid]
  exact cornerBern3_nonneg C0 C1 C2 C3 q hC0 hC1 hC2 hC3 hq hq1

private theorem n3_return_high_smallX_nonneg (X T q : ℝ)
    (hX : 0 ≤ X) (hT2 : 2 ≤ T) (hXT : X ≤ T)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ uniformFaceAThreeCore X T q := by
  let W := T-2
  let b := X/T
  have hT : 0 < T := by linarith
  have hW : 0 ≤ W := by dsimp [W]; linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; exact (div_le_one hT).mpr hXT
  have hbad : 0 ≤
      45*W^6+546*W^5+2290*W^4+3436*W^3+200*W^2-880*W+3360 := by
    have hquad : 0 ≤ 200*W^2-880*W+3360 := by
      nlinarith [sq_nonneg (10*W-22)]
    have hid :
        45*W^6+546*W^5+2290*W^4+3436*W^3+200*W^2-880*W+3360 =
          45*W^6+546*W^5+2290*W^4+3436*W^3+
            (200*W^2-880*W+3360) := by ring
    rw [hid]
    positivity
  let Q0 := cornerBern3
    160 (32*(11*W+37)/3) (8*(33*W^2+220*W+368)/3)
    (27*W^3+426*W^2+1732*W+2136) b
  let Q1 := cornerBern3
    (20*(25*W^4+168*W^3+420*W^2+480*W+248)/3)
    ((15*W^5+666*W^4+3972*W^3+10232*W^2+15392*W+12896)/9)
    (2*(15*W^5+267*W^4+1854*W^3+7136*W^2+15176*W+13568)/9)
    ((15*W^5+368*W^4+3177*W^3+12926*W^2+25532*W+19848)/3) b
  let Q2 := cornerBern3
    (5*(3*W^6+40*W^5+310*W^4+1152*W^3+2080*W^2+1920*W+960)/3)
    ((45*W^6+801*W^5+5676*W^4+19568*W^3+37312*W^2+43600*W+27872)/9)
    ((45*W^6+1002*W^5+7920*W^4+32056*W^3+76184*W^2+106016*W+67648)/9)
    ((15*W^6+401*W^5+3794*W^4+18329*W^3+49758*W^2+72988*W+45224)/3) b
  let Q3 := cornerBern3
    (5*W^2*(3*W^4+40*W^3+210*W^2+480*W+400))
    ((45*W^6+546*W^5+2290*W^4+3436*W^3+200*W^2-880*W+3360)/3)
    ((45*W^6+492*W^5+1946*W^4+4028*W^3+8416*W^2+18544*W+17856)/3)
    ((W+3)*(15*W^5+101*W^4+403*W^3+1810*W^2+4948*W+4904)) b
  have hQ0 : 0 ≤ Q0 := by
    dsimp [Q0]; apply cornerBern3_nonneg <;> first | assumption | positivity
  have hQ1 : 0 ≤ Q1 := by
    dsimp [Q1]; apply cornerBern3_nonneg <;> first | assumption | positivity
  have hQ2 : 0 ≤ Q2 := by
    dsimp [Q2]; apply cornerBern3_nonneg <;> first | assumption | positivity
  have hQ3 : 0 ≤ Q3 := by
    dsimp [Q3]
    apply cornerBern3_nonneg <;> first | assumption | positivity
  have hTb : T*b = X := by dsimp [b]; field_simp [hT.ne']
  have hTW : W+2 = T := by dsimp [W]; ring
  have hid : uniformFaceAThreeCore ((W+2)*b) (W+2) q =
      cornerBern3 Q0 Q1 Q2 Q3 q := by
    dsimp [uniformFaceAThreeCore, Q0, Q1, Q2, Q3, cornerBern3]
    ring
  rw [hTW, hTb] at hid
  rw [hid]
  exact cornerBern3_nonneg Q0 Q1 Q2 Q3 q hQ0 hQ1 hQ2 hQ3 hq hq1

private theorem n3_return_high_largeX_nonneg (X T q : ℝ)
    (hT2 : 2 ≤ T) (hTX : T ≤ X) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ uniformFaceAThreeCore X T q := by
  let W := T-2
  let Z := X-T
  have hW : 0 ≤ W := by dsimp [W]; linarith
  have hZ : 0 ≤ Z := by dsimp [Z]; linarith
  let Q0 := 27*W^3+81*W^2*Z+426*W^2+81*W*Z^2+852*W*Z+1732*W
      +27*Z^3+426*Z^2+1732*Z+2136
  let Q1 := (15*W^5+15*W^4*Z+368*W^4+540*W^3*Z+3177*W^3
      +702*W^2*Z^2+4743*W^2*Z+12926*W^2+3279*W*Z^2+15020*W*Z
      +25532*W+81*Z^3+4542*Z^2+16204*Z+19848)/3
  let Q2 := (15*W^6+401*W^5+201*W^4*Z+3794*W^4+3060*W^3*Z+18329*W^3
      +1218*W^2*Z^2+16811*W^2*Z+49758*W^2+5571*W*Z^2+39468*W*Z
      +72988*W+81*Z^3+7062*Z^2+34012*Z+45224)/3
  let Q3 := 15*W^6+146*W^5-54*W^4*Z+706*W^4+280*W^3*Z+3019*W^3
      +516*W^2*Z^2+4469*W^2*Z+10378*W^2+2373*W*Z^2+13780*W*Z
      +19748*W+27*Z^3+2946*Z^2+13140*Z+14712
  have hQ0 : 0 ≤ Q0 := by dsimp [Q0]; positivity
  have hQ1 : 0 ≤ Q1 := by dsimp [Q1]; positivity
  have hQ2 : 0 ≤ Q2 := by dsimp [Q2]; positivity
  have hquad : 0 ≤ 15*W^4-54*W^2*Z+516*Z^2 := by
    nlinarith [sq_nonneg (5*W^2-9*Z)]
  have hQ3 : 0 ≤ Q3 := by
    dsimp [Q3]
    have : 0 ≤ W^2*(15*W^4-54*W^2*Z+516*Z^2) :=
      mul_nonneg (sq_nonneg W) hquad
    nlinarith [this,
      mul_nonneg hW (mul_nonneg (sq_nonneg W) hZ),
      mul_nonneg (sq_nonneg W) hZ,
      mul_nonneg hW (sq_nonneg Z),
      mul_nonneg (sq_nonneg Z) hZ]
  have hTW : W+2 = T := by dsimp [W]; ring
  have hXZ : W+2+Z = X := by dsimp [W, Z]; ring
  have hid : uniformFaceAThreeCore (W+2+Z) (W+2) q =
      cornerBern3 Q0 Q1 Q2 Q3 q := by
    dsimp [uniformFaceAThreeCore, Q0, Q1, Q2, Q3, cornerBern3]
    ring
  rw [hXZ, hTW] at hid
  rw [hid]
  exact cornerBern3_nonneg Q0 Q1 Q2 Q3 q hQ0 hQ1 hQ2 hQ3 hq hq1

theorem uniformFaceAThreeCore_nonneg (X T q : ℝ)
    (hX : 0 ≤ X) (hT : 0 < T) (hq : 0 < q) (hq1 : q ≤ 1) :
    0 ≤ uniformFaceAThreeCore X T q := by
  by_cases hT2 : T ≤ 2
  · exact n3_return_low_nonneg X T q hX hT.le hT2 hq.le hq1
  · by_cases hXT : X ≤ T
    · exact n3_return_high_smallX_nonneg X T q hX (by linarith) hXT hq.le hq1
    · exact n3_return_high_largeX_nonneg X T q (by linarith) (by linarith) hq.le hq1

theorem uniformFaceACore_three_nonneg (X T q : ℝ)
    (hX : 0 ≤ X) (hT : 0 < T) (hq : 0 < q) (hq1 : q ≤ 1) :
    0 ≤ uniformFaceACore 3 X T q := by
  have hcore := uniformFaceAThreeCore_nonneg X T q hX hT hq hq1
  rw [show uniformFaceACore 3 X T q = 12*uniformFaceAThreeCore X T q by
    unfold uniformFaceACore uniformFaceAThreeCore
    norm_num
    ring]
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem sharpGradA_three_normalized
    (a T Y q : ℝ) (hY : Y ≠ 0) (hq : q ≠ 0) (hsum : Y+a ≠ 0) :
    sharpGradA 3 (a/Y) (Y*(1-a)/(Y+a)) Y (3*Y^2/2)
        (q*T) (3*q*T^2/2) = a*uniformGradA 3 a T Y q/(2*Y) := by
  unfold sharpGradA sharpThird excursionGradA excursionHAA
  unfold excursionReducedGap stageGap hessianCore
  unfold SSP.K3S4Renewal.geomM4 SSP.K3S4Renewal.geomM3
    SSP.K3S4Renewal.geomM2 SSP.K3S4Renewal.geomM1
  unfold SSP.K3S4Renewal.kernelM1 SSP.K3S4Renewal.kernelM2
    SSP.K3S4Renewal.kernelM3 SSP.K3S4Renewal.kernelM4 uniformGradA
  have hsq : a*Y*2+a^2+Y^2 ≠ 0 := by
    convert pow_ne_zero 2 hsum using 1
    all_goals ring
  field_simp [hY, hq, hsum, hsq]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem excursionHAA_three_normalized
    (a T Y q : ℝ) (hY : Y ≠ 0) (hsum : Y+a ≠ 0) :
    excursionHAA 3 (a/Y) (Y*(1-a)/(Y+a)) Y (3*Y^2/2)
        (q*T) (3*q*T^2/2) = a*uniformHAA 3 a T Y q/(6*Y^3) := by
  unfold excursionHAA hessianCore uniformHAA
  have hsq : a*Y*2+a^2+Y^2 ≠ 0 := by
    convert pow_ne_zero 2 hsum using 1
    all_goals ring
  field_simp [hY, hsum, hsq]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformSharpFaceA_three_num_identity
    (a T Y q : ℝ) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hq : q ≠ 0) (hsum : Y+a ≠ 0) :
    Y^3*3*4*2^4*uniformSharpFaceA 3 a T Y q =
      4*a*uniformFaceANum 3 a T Y q := by
  have hgap := uniformSharpGap_eq_cornerPoly 3 a T Y q
    (by norm_num) (by norm_num) (by norm_num) hT hY hq hsum
  have hgrad := sharpGradA_three_normalized a T Y q hY hq hsum
  have hhaa := excursionHAA_three_normalized a T Y q hY hsum
  unfold uniformSharpFaceA sharpFaceA
  norm_num at hgap ⊢
  rw [hgrad, hhaa]
  rw [show sharpGap 3 (a/Y) (Y*(1-a)/(Y+a)) Y (3*Y^2/2)
      (q*T) (3*q*T^2/2) = uniformSharpGap 3 a T Y q by
        unfold uniformSharpGap
        congr 2 <;> ring]
  unfold uniformFaceANum
  field_simp [hY]
  rw [← hgap]
  ring

/-- The normalized return-face certificate at the exceptional stage `n = 3`.
It is in fact unconditional: the active-gradient and return-side hypotheses
used by the KKT wrapper are unnecessary here. -/
theorem uniformSharpFaceA_three_nonneg (a T Y q : ℝ)
    (ha : 0 < a) (hT : 0 < T) (hY : 0 < Y)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    0 ≤ uniformSharpFaceA 3 a T Y q := by
  have hcore := uniformFaceACore_three_nonneg (a*Y) T q (by positivity) hT hq hq1
  have hm2 : 0 ≤ uniformCornerM2Num 3 a T Y q := by
    rw [show uniformCornerM2Num 3 a T Y q =
      3*T^2*q+4*T*q+3*Y*a+4 by unfold uniformCornerM2Num; ring]
    positivity
  have hnum : 0 ≤ uniformFaceANum 3 a T Y q := by
    rw [uniformFaceANum_factor]
    positivity
  have hid := uniformSharpFaceA_three_num_identity a T Y q
    hT.ne' hY.ne' hq.ne' (by positivity)
  have hrhs : 0 ≤ 4*a*uniformFaceANum 3 a T Y q := by positivity
  norm_num at hid
  rw [← hid] at hrhs
  exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < Y^3*3*4*16)).mp hrhs

end SSP.K3AllStages
