import SSPLean.K3AllStagesCorner

set_option autoImplicit false

namespace SSP.K3AllStages

open SSP.K3S4Renewal
open SSP.K3S4KKT

/-! ### Polynomial numerators for the two one-face discriminants -/

noncomputable def uniformFaceANum (n a T Y q : ℝ) : ℝ :=
  uniformHAA n a T Y q*uniformCornerPoly n a T Y q
    -a*Y*n*(n+1)*(uniformGradA n a T Y q)^2

noncomputable def uniformFaceBNum (n a T Y q : ℝ) : ℝ :=
  uniformHBB n a T Y q*uniformCornerPoly n a T Y q
    -T^2*n*q*(n+1)*(uniformGradB n a T Y q)^2

set_option maxHeartbeats 3000000 in
/-- After the positive factors `(n+2) * uniformCornerM2Num` are removed,
the return-face numerator depends on `a` and `Y` only through `X = aY`.
It is cubic in the terminal mixture weight `q`. -/
noncomputable def uniformFaceACore (n X T q : ℝ) : ℝ :=
  6*X^3*n^4-6*X^3*n^3
    +8*X^2*n^6-4*X^2*n^5-36*X^2*n^4+52*X^2*n^3-20*X^2*n^2
    +16*X*n^6-24*X*n^5-64*X*n^4+176*X*n^3-144*X*n^2+40*X*n
    +12*n^6-36*n^5+120*n^3-180*n^2+108*n-24
    +q^3*(-4*T^4*X*n^6-4*T^4*X*n^5+12*T^4*X*n^4+4*T^4*X*n^3
      -8*T^4*X*n^2-8*T^3*X*n^6+32*T^3*X*n^4-16*T^3*X*n^3
      -24*T^3*X*n^2+16*T^3*X*n)
    +q^2*(T^6*n^4+3*T^6*n^3+2*T^6*n^2-2*T^5*n^5+4*T^5*n^4
      +18*T^5*n^3-4*T^5*n^2-16*T^5*n+4*T^4*X*n^6+4*T^4*X*n^5
      -22*T^4*X*n^4-10*T^4*X*n^3+24*T^4*X*n^2-T^4*n^6
      -27*T^4*n^5-17*T^4*n^4+79*T^4*n^3+6*T^4*n^2-40*T^4*n
      +14*T^3*X*n^6+26*T^3*X*n^5-54*T^3*X*n^4-26*T^3*X*n^3
      +40*T^3*X*n^2+12*T^3*n^6-24*T^3*n^5-24*T^3*n^4
      +96*T^3*n^3-84*T^3*n^2+24*T^3*n-T^2*X^2*n^6
      -7*T^2*X^2*n^5-9*T^2*X^2*n^4+43*T^2*X^2*n^3-26*T^2*X^2*n^2
      -4*T^2*X*n^6-8*T^2*X*n^4+64*T^2*X*n^3-84*T^2*X*n^2
      +32*T^2*X*n+12*T^2*n^6-36*T^2*n^5+120*T^2*n^3
      -180*T^2*n^2+108*T^2*n-24*T^2)
    +q*(T^4*X*n^4+3*T^4*X*n^3+2*T^4*X*n^2+2*T^4*n^6
      +12*T^4*n^5+22*T^4*n^4+4*T^4*n^3-24*T^4*n^2-16*T^4*n
      -4*T^3*X*n^6-28*T^3*X*n^5-40*T^3*X*n^4+28*T^3*X*n^3
      +44*T^3*X*n^2-4*T^3*n^6-24*T^3*n^5-8*T^3*n^4
      +64*T^3*n^3+12*T^3*n^2-40*T^3*n+6*T^2*X^2*n^6
      +18*T^2*X^2*n^5+6*T^2*X^2*n^4-30*T^2*X^2*n^3
      +20*T^2*X*n^6+20*T^2*X*n^5-72*T^2*X*n^4+4*T^2*X*n^3
      +28*T^2*X*n^2+12*T^2*n^6-24*T^2*n^5-24*T^2*n^4
      +96*T^2*n^3-84*T^2*n^2+24*T^2*n+8*T*X^2*n^6
      -4*T*X^2*n^5-48*T*X^2*n^4+76*T*X^2*n^3-32*T*X^2*n^2
      +20*T*X*n^6-24*T*X*n^5-104*T*X*n^4+256*T*X*n^3
      -204*T*X*n^2+56*T*X*n+24*T*n^6-72*T*n^5+240*T*n^3
      -360*T*n^2+216*T*n-48*T)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- Exact factorization of the return-face numerator into a positive moment
factor and the reduced cubic. -/
theorem uniformFaceANum_factor (n a T Y q : ℝ) :
    uniformFaceANum n a T Y q =
      (n+2)*uniformCornerM2Num n a T Y q*
        uniformFaceACore n (a*Y) T q := by
  unfold uniformFaceANum uniformHAA uniformGradA uniformCornerPoly
  unfold uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num
  unfold uniformFaceACore
  ring

/-- Bernstein core of the return-face numerator on the `q = 0` boundary. -/
noncomputable def uniformFaceAQ0Core (m a Y : ℝ) : ℝ :=
  cornerBern3
    (6*(m+3)^4*(m+6))
    (2*(m+3)^3*(4*Y*m^2+42*Y*m+104*Y
      +9*m^2+81*m+162)/3)
    (2*(m+3)^2*(2*Y^2*m^3+29*Y^2*m^2+136*Y^2*m+208*Y^2
      +8*Y*m^3+108*Y*m^2+460*Y*m+624*Y
      +9*m^3+108*m^2+405*m+486)/3)
    (3*Y^3*m^3+36*Y^3*m^2+144*Y^3*m+192*Y^3
      +4*Y^2*m^5+82*Y^2*m^4+656*Y^2*m^3+2570*Y^2*m^2
      +4944*Y^2*m+3744*Y^2+8*Y*m^5+156*Y*m^4+1180*Y*m^3
      +4356*Y*m^2+7884*Y*m+5616*Y+6*m^5+108*m^4+756*m^3
      +2592*m^2+4374*m+2916) a

theorem uniformFaceAQ0Core_nonneg
    (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hY : 0 ≤ Y) : 0 ≤ uniformFaceAQ0Core m a Y := by
  unfold uniformFaceAQ0Core
  apply cornerBern3_nonneg <;> first | assumption | positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformFaceANum_at_q_zero_identity (m a T Y : ℝ) :
    uniformFaceANum (m+4) a T Y 0 =
      2*(m+3)*(m+6)*uniformCornerM2Num (m+4) a T Y 0
        *uniformFaceAQ0Core m a Y := by
  unfold uniformFaceANum uniformHAA uniformGradA uniformCornerPoly
  unfold uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num
  unfold uniformFaceAQ0Core cornerBern3
  ring

theorem uniformFaceANum_at_q_zero_nonneg
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hY : 0 ≤ Y) : 0 ≤ uniformFaceANum n a T Y 0 := by
  let m := n-4
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hcore := uniformFaceAQ0Core_nonneg m a Y hm ha ha1 hY
  have hm2 : 0 ≤ uniformCornerM2Num (m+4) a T Y 0 := by
    rw [show uniformCornerM2Num (m+4) a T Y 0 =
      Y*a*(m+4)+2*(m+3) by unfold uniformCornerM2Num; ring]
    positivity
  have hm3 : 0 ≤ m+3 := by linarith
  have hm6 : 0 ≤ m+6 := by linarith
  have hid := uniformFaceANum_at_q_zero_identity m a T Y
  have hnid : m+4 = n := by dsimp [m]; ring
  rw [hnid] at hid
  rw [hid]
  have hm2n : 0 ≤ uniformCornerM2Num n a T Y 0 := by
    rw [← hnid]
    exact hm2
  have hcoef : 0 ≤ 2*(m+3)*(m+6) := by positivity
  have hprod := mul_nonneg hcoef (mul_nonneg hm2n hcore)
  simpa only [mul_assoc] using hprod

/-! ### Bernstein reduction of the return-face core in `q` -/

noncomputable def uniformFaceAQB0 (n X T : ℝ) : ℝ :=
  uniformFaceACore n X T 0

noncomputable def uniformFaceAQB1 (n X T : ℝ) : ℝ :=
  -(5/6)*uniformFaceACore n X T 0
    +(1/3)*uniformFaceACore n X T 1
    +3*uniformFaceACore n X T (1/3)
    -(3/2)*uniformFaceACore n X T (2/3)

noncomputable def uniformFaceAQB2 (n X T : ℝ) : ℝ :=
  (1/3)*uniformFaceACore n X T 0
    -(5/6)*uniformFaceACore n X T 1
    -(3/2)*uniformFaceACore n X T (1/3)
    +3*uniformFaceACore n X T (2/3)

noncomputable def uniformFaceAQB3 (n X T : ℝ) : ℝ :=
  uniformFaceACore n X T 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- Exact cubic Bernstein expansion of the reduced return-face numerator. -/
theorem uniformFaceACore_bernstein_q (n X T q : ℝ) :
    uniformFaceACore n X T q =
      cornerBern3 (uniformFaceAQB0 n X T) (uniformFaceAQB1 n X T)
        (uniformFaceAQB2 n X T) (uniformFaceAQB3 n X T) q := by
  unfold uniformFaceAQB0 uniformFaceAQB1 uniformFaceAQB2 uniformFaceAQB3
  unfold uniformFaceACore cornerBern3
  ring

theorem uniformFaceAQB0_shift (m X T : ℝ) :
    uniformFaceAQB0 (m+4) X T =
      2*(m+3)*uniformFaceAQ0Core m 1 X := by
  unfold uniformFaceAQB0 uniformFaceACore uniformFaceAQ0Core cornerBern3
  ring

theorem uniformFaceAQB0_nonneg
    (n X T : ℝ) (hn : 4 ≤ n) (hX : 0 ≤ X) :
    0 ≤ uniformFaceAQB0 n X T := by
  let m := n-4
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hcore := uniformFaceAQ0Core_nonneg m 1 X hm (by norm_num)
    (by norm_num) hX
  have hid := uniformFaceAQB0_shift m X T
  have hnid : m+4 = n := by dsimp [m]; ring
  rw [hnid] at hid
  rw [hid]
  positivity

/-- The return-face problem is reduced to the three nontrivial Bernstein
coefficients of its cubic core. -/
theorem uniformFaceACore_nonneg_of_q_bernstein
    (n X T q : ℝ) (hn : 4 ≤ n) (hX : 0 ≤ X)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (h1 : 0 ≤ uniformFaceAQB1 n X T)
    (h2 : 0 ≤ uniformFaceAQB2 n X T)
    (h3 : 0 ≤ uniformFaceAQB3 n X T) :
    0 ≤ uniformFaceACore n X T q := by
  have h0 := uniformFaceAQB0_nonneg n X T hn hX
  rw [uniformFaceACore_bernstein_q]
  exact cornerBern3_nonneg _ _ _ _ _ h0 h1 h2 h3 hq hq1

/-- Once the three nontrivial cubic coefficients are nonnegative, the full
return-face numerator follows because the discarded moment factor is positive. -/
theorem uniformFaceANum_nonneg_of_q_bernstein
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a)
    (hT : 0 ≤ T) (hY : 0 ≤ Y) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (h1 : 0 ≤ uniformFaceAQB1 n (a*Y) T)
    (h2 : 0 ≤ uniformFaceAQB2 n (a*Y) T)
    (h3 : 0 ≤ uniformFaceAQB3 n (a*Y) T) :
    0 ≤ uniformFaceANum n a T Y q := by
  have hX : 0 ≤ a*Y := by positivity
  have hcore := uniformFaceACore_nonneg_of_q_bernstein n (a*Y) T q
    hn hX hq hq1 h1 h2 h3
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

/-! The middle nontrivial `q`-coefficient is a degree-six polynomial in `T`.
On `0 ≤ T ≤ n-1`, rescale `T = (n-1)t` and use its degree-six Bernstein
coefficients.  Defining the coefficients from seven exact samples keeps the
certificate auditable while avoiding a second copy of the expanded polynomial. -/

noncomputable def uniformFaceAQB2CompactSample (m X t : ℝ) : ℝ :=
  uniformFaceAQB2 (m+4) X ((m+3)*t)

noncomputable def uniformFaceAQB2C0 (m X : ℝ) : ℝ :=
  uniformFaceAQB2CompactSample m X 0

noncomputable def uniformFaceAQB2C1 (m X : ℝ) : ℝ :=
  -(29/20)*uniformFaceAQB2CompactSample m X 0
    +6*uniformFaceAQB2CompactSample m X (1/6)
    -(15/2)*uniformFaceAQB2CompactSample m X (2/6)
    +(20/3)*uniformFaceAQB2CompactSample m X (3/6)
    -(15/4)*uniformFaceAQB2CompactSample m X (4/6)
    +(6/5)*uniformFaceAQB2CompactSample m X (5/6)
    -(1/6)*uniformFaceAQB2CompactSample m X 1

noncomputable def uniformFaceAQB2C2 (m X : ℝ) : ℝ :=
  (227/150)*uniformFaceAQB2CompactSample m X 0
    -(222/25)*uniformFaceAQB2CompactSample m X (1/6)
    +(201/10)*uniformFaceAQB2CompactSample m X (2/6)
    -(308/15)*uniformFaceAQB2CompactSample m X (3/6)
    +(123/10)*uniformFaceAQB2CompactSample m X (4/6)
    -(102/25)*uniformFaceAQB2CompactSample m X (5/6)
    +(29/50)*uniformFaceAQB2CompactSample m X 1

noncomputable def uniformFaceAQB2C3 (m X : ℝ) : ℝ :=
  -(227/200)*uniformFaceAQB2CompactSample m X 0
    +(189/25)*uniformFaceAQB2CompactSample m X (1/6)
    -(837/40)*uniformFaceAQB2CompactSample m X (2/6)
    +30*uniformFaceAQB2CompactSample m X (3/6)
    -(837/40)*uniformFaceAQB2CompactSample m X (4/6)
    +(189/25)*uniformFaceAQB2CompactSample m X (5/6)
    -(227/200)*uniformFaceAQB2CompactSample m X 1

noncomputable def uniformFaceAQB2C4 (m X : ℝ) : ℝ :=
  (29/50)*uniformFaceAQB2CompactSample m X 0
    -(102/25)*uniformFaceAQB2CompactSample m X (1/6)
    +(123/10)*uniformFaceAQB2CompactSample m X (2/6)
    -(308/15)*uniformFaceAQB2CompactSample m X (3/6)
    +(201/10)*uniformFaceAQB2CompactSample m X (4/6)
    -(222/25)*uniformFaceAQB2CompactSample m X (5/6)
    +(227/150)*uniformFaceAQB2CompactSample m X 1

noncomputable def uniformFaceAQB2C5 (m X : ℝ) : ℝ :=
  -(1/6)*uniformFaceAQB2CompactSample m X 0
    +(6/5)*uniformFaceAQB2CompactSample m X (1/6)
    -(15/4)*uniformFaceAQB2CompactSample m X (2/6)
    +(20/3)*uniformFaceAQB2CompactSample m X (3/6)
    -(15/2)*uniformFaceAQB2CompactSample m X (4/6)
    +6*uniformFaceAQB2CompactSample m X (5/6)
    -(29/20)*uniformFaceAQB2CompactSample m X 1

noncomputable def uniformFaceAQB2C6 (m X : ℝ) : ℝ :=
  uniformFaceAQB2CompactSample m X 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformFaceAQB2_compact_bernstein (m X t : ℝ) :
    uniformFaceAQB2 (m+4) X ((m+3)*t) =
      cornerBern6 (uniformFaceAQB2C0 m X) (uniformFaceAQB2C1 m X)
        (uniformFaceAQB2C2 m X) (uniformFaceAQB2C3 m X)
        (uniformFaceAQB2C4 m X) (uniformFaceAQB2C5 m X)
        (uniformFaceAQB2C6 m X) t := by
  unfold uniformFaceAQB2C0 uniformFaceAQB2C1 uniformFaceAQB2C2
  unfold uniformFaceAQB2C3 uniformFaceAQB2C4 uniformFaceAQB2C5
  unfold uniformFaceAQB2C6 uniformFaceAQB2CompactSample
  unfold uniformFaceAQB2 uniformFaceACore cornerBern6
  ring

private theorem uniformFaceAQB2C0_nonneg
    (m X : ℝ) (hm : 0 ≤ m) (hX : 0 ≤ X) :
    0 ≤ uniformFaceAQB2C0 m X := by
  unfold uniformFaceAQB2C0 uniformFaceAQB2CompactSample
  unfold uniformFaceAQB2 uniformFaceACore
  ring_nf
  positivity

private theorem uniformFaceAQB2C1_nonneg
    (m X : ℝ) (hm : 0 ≤ m) (hX : 0 ≤ X) :
    0 ≤ uniformFaceAQB2C1 m X := by
  unfold uniformFaceAQB2C1 uniformFaceAQB2CompactSample
  unfold uniformFaceAQB2 uniformFaceACore
  ring_nf
  positivity

private theorem uniformFaceAQB2C2_nonneg
    (m X : ℝ) (hm : 0 ≤ m) (hX : 0 ≤ X) :
    0 ≤ uniformFaceAQB2C2 m X := by
  unfold uniformFaceAQB2C2 uniformFaceAQB2CompactSample
  unfold uniformFaceAQB2 uniformFaceACore
  ring_nf
  positivity

private theorem uniformFaceAQB2C3_nonneg
    (m X : ℝ) (hm : 0 ≤ m) (hX : 0 ≤ X) :
    0 ≤ uniformFaceAQB2C3 m X := by
  unfold uniformFaceAQB2C3 uniformFaceAQB2CompactSample
  unfold uniformFaceAQB2 uniformFaceACore
  ring_nf
  positivity

private theorem uniformFaceAQB2C4_nonneg
    (m X : ℝ) (hm : 0 ≤ m) (hX : 0 ≤ X) :
    0 ≤ uniformFaceAQB2C4 m X := by
  unfold uniformFaceAQB2C4 uniformFaceAQB2CompactSample
  unfold uniformFaceAQB2 uniformFaceACore
  ring_nf
  positivity

private theorem uniformFaceAQB2C5_nonneg
    (m X : ℝ) (hm : 0 ≤ m) (hX : 0 ≤ X) :
    0 ≤ uniformFaceAQB2C5 m X := by
  unfold uniformFaceAQB2C5 uniformFaceAQB2CompactSample
  unfold uniformFaceAQB2 uniformFaceACore
  ring_nf
  positivity

private theorem uniformFaceAQB2C6_nonneg
    (m X : ℝ) (hm : 0 ≤ m) (hX : 0 ≤ X) :
    0 ≤ uniformFaceAQB2C6 m X := by
  unfold uniformFaceAQB2C6 uniformFaceAQB2CompactSample
  unfold uniformFaceAQB2 uniformFaceACore
  ring_nf
  positivity

/-- The middle nontrivial return-face Bernstein coefficient is nonnegative
on the compact half `0 ≤ T ≤ n-1`. -/
theorem uniformFaceAQB2_nonneg_of_T_le
    (n X T : ℝ) (hn : 4 ≤ n) (hX : 0 ≤ X)
    (hT : 0 ≤ T) (hT1 : T ≤ n-1) :
    0 ≤ uniformFaceAQB2 n X T := by
  let m := n-4
  let t := T/(n-1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hn1 : 0 < n-1 := by linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; exact (div_le_one hn1).2 hT1
  have hid : (m+3)*t = T := by
    dsimp [m, t]
    field_simp [hn1.ne']
    ring
  have hnid : m+4 = n := by dsimp [m]; ring
  rw [← hnid, ← hid]
  rw [uniformFaceAQB2_compact_bernstein]
  apply cornerBern6_nonneg <;> first
    | exact uniformFaceAQB2C0_nonneg m X hm hX
    | exact uniformFaceAQB2C1_nonneg m X hm hX
    | exact uniformFaceAQB2C2_nonneg m X hm hX
    | exact uniformFaceAQB2C3_nonneg m X hm hX
    | exact uniformFaceAQB2C4_nonneg m X hm hX
    | exact uniformFaceAQB2C5_nonneg m X hm hX
    | exact uniformFaceAQB2C6_nonneg m X hm hX
    | exact ht
    | exact ht1

/-- The first nontrivial return-face Bernstein coefficient is nonnegative
for every nonnegative terminal scale.  Its only negative coefficient is the
cubic coefficient in `T`; the adjacent quadratic and quartic coefficients
absorb it by a discriminant estimate. -/
theorem uniformFaceAQB1_nonneg
    (n X T : ℝ) (hn : 4 ≤ n) (hX : 0 ≤ X) (hT : 0 ≤ T) :
    0 ≤ uniformFaceAQB1 n X T := by
  let m := n-4
  let A : ℝ := (m+4)*(m+5)*(m+6)
    *(X*m+4*X+2*m^3+30*m^2+144*m+216)/3
  let B : ℝ := -4*(m+3)*(m+4)*(m+5)
    *(X*m^3+19*X*m^2+115*X*m+220*X+m^3+18*m^2+99*m+162)/3
  let C : ℝ := 2*(m+3)*(m+4)
    *(3*X^2*m^4+60*X^2*m^3+447*X^2*m^2+1464*X^2*m+1776*X^2
      +10*X*m^4+180*X*m^3+1184*X*m^2+3378*X*m+3528*X
      +6*m^4+90*m^3+486*m^2+1134*m+972)/3
  let D : ℝ := 4*(m+3)^2
    *(2*X^2*m^4+35*X^2*m^3+220*X^2*m^2+592*X^2*m+576*X^2
      +5*X*m^4+84*X*m^3+505*X*m^2+1302*X*m+1224*X
      +6*m^4+90*m^3+486*m^2+1134*m+972)/3
  let E : ℝ := 2*(m+3)
    *(3*X^3*m^3+36*X^3*m^2+144*X^3*m+192*X^3
      +4*X^2*m^5+82*X^2*m^4+656*X^2*m^3+2570*X^2*m^2
      +4944*X^2*m+3744*X^2+8*X*m^5+156*X*m^4+1180*X*m^3
      +4356*X*m^2+7884*X*m+5616*X+6*m^5+108*m^4+756*m^3
      +2592*m^2+4374*m+2916)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hdisc : B^2 ≤ 4*A*C := by
    rw [← sub_nonneg]
    dsimp [A, B, C]
    ring_nf
    positivity
  have hquad : 0 ≤ A*T^2+B*T+C := by
    have hid : 4*A*(A*T^2+B*T+C) =
        (2*A*T+B)^2+(4*A*C-B^2) := by ring
    apply (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*A)).mp
    rw [hid]
    nlinarith [sq_nonneg (2*A*T+B)]
  have hdecomp : uniformFaceAQB1 n X T =
      A*T^4+B*T^3+C*T^2+D*T+E := by
    dsimp [m, A, B, C, D, E]
    unfold uniformFaceAQB1 uniformFaceACore
    ring
  rw [hdecomp]
  have hmain : 0 ≤ T^2*(A*T^2+B*T+C) := mul_nonneg (sq_nonneg T) hquad
  nlinarith [mul_nonneg hD hT, hE]

/-- The middle coefficient is also nonnegative on the unbounded half
`n-1 ≤ T`; after translating by `T = (n-1)+z`, every coefficient is
nonnegative. -/
theorem uniformFaceAQB2_nonneg_of_T_ge
    (n X T : ℝ) (hn : 4 ≤ n) (hX : 0 ≤ X) (hT1 : n-1 ≤ T) :
    0 ≤ uniformFaceAQB2 n X T := by
  let m := n-4
  let z := T-(n-1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : m+3+z = T := by dsimp [m, z]; ring
  rw [← hnid, ← hTid]
  unfold uniformFaceAQB2 uniformFaceACore
  ring_nf
  positivity

/-- Global nonnegativity of the middle nontrivial `q`-Bernstein coefficient. -/
theorem uniformFaceAQB2_nonneg
    (n X T : ℝ) (hn : 4 ≤ n) (hX : 0 ≤ X) (hT : 0 ≤ T) :
    0 ≤ uniformFaceAQB2 n X T := by
  by_cases hT1 : T ≤ n-1
  · exact uniformFaceAQB2_nonneg_of_T_le n X T hn hX hT hT1
  · exact uniformFaceAQB2_nonneg_of_T_ge n X T hn hX (by linarith)

/-! The `q = 1` endpoint is likewise positive on the compact half. -/

noncomputable def uniformFaceAQB3CompactSample (m X t : ℝ) : ℝ :=
  uniformFaceAQB3 (m+4) X ((m+3)*t)

noncomputable def uniformFaceAQB3C0 (m X : ℝ) : ℝ :=
  uniformFaceAQB3CompactSample m X 0

noncomputable def uniformFaceAQB3C1 (m X : ℝ) : ℝ :=
  -(29/20)*uniformFaceAQB3CompactSample m X 0
    +6*uniformFaceAQB3CompactSample m X (1/6)
    -(15/2)*uniformFaceAQB3CompactSample m X (2/6)
    +(20/3)*uniformFaceAQB3CompactSample m X (3/6)
    -(15/4)*uniformFaceAQB3CompactSample m X (4/6)
    +(6/5)*uniformFaceAQB3CompactSample m X (5/6)
    -(1/6)*uniformFaceAQB3CompactSample m X 1

noncomputable def uniformFaceAQB3C2 (m X : ℝ) : ℝ :=
  (227/150)*uniformFaceAQB3CompactSample m X 0
    -(222/25)*uniformFaceAQB3CompactSample m X (1/6)
    +(201/10)*uniformFaceAQB3CompactSample m X (2/6)
    -(308/15)*uniformFaceAQB3CompactSample m X (3/6)
    +(123/10)*uniformFaceAQB3CompactSample m X (4/6)
    -(102/25)*uniformFaceAQB3CompactSample m X (5/6)
    +(29/50)*uniformFaceAQB3CompactSample m X 1

noncomputable def uniformFaceAQB3C3 (m X : ℝ) : ℝ :=
  -(227/200)*uniformFaceAQB3CompactSample m X 0
    +(189/25)*uniformFaceAQB3CompactSample m X (1/6)
    -(837/40)*uniformFaceAQB3CompactSample m X (2/6)
    +30*uniformFaceAQB3CompactSample m X (3/6)
    -(837/40)*uniformFaceAQB3CompactSample m X (4/6)
    +(189/25)*uniformFaceAQB3CompactSample m X (5/6)
    -(227/200)*uniformFaceAQB3CompactSample m X 1

noncomputable def uniformFaceAQB3C4 (m X : ℝ) : ℝ :=
  (29/50)*uniformFaceAQB3CompactSample m X 0
    -(102/25)*uniformFaceAQB3CompactSample m X (1/6)
    +(123/10)*uniformFaceAQB3CompactSample m X (2/6)
    -(308/15)*uniformFaceAQB3CompactSample m X (3/6)
    +(201/10)*uniformFaceAQB3CompactSample m X (4/6)
    -(222/25)*uniformFaceAQB3CompactSample m X (5/6)
    +(227/150)*uniformFaceAQB3CompactSample m X 1

noncomputable def uniformFaceAQB3C5 (m X : ℝ) : ℝ :=
  -(1/6)*uniformFaceAQB3CompactSample m X 0
    +(6/5)*uniformFaceAQB3CompactSample m X (1/6)
    -(15/4)*uniformFaceAQB3CompactSample m X (2/6)
    +(20/3)*uniformFaceAQB3CompactSample m X (3/6)
    -(15/2)*uniformFaceAQB3CompactSample m X (4/6)
    +6*uniformFaceAQB3CompactSample m X (5/6)
    -(29/20)*uniformFaceAQB3CompactSample m X 1

noncomputable def uniformFaceAQB3C6 (m X : ℝ) : ℝ :=
  uniformFaceAQB3CompactSample m X 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformFaceAQB3_compact_bernstein (m X t : ℝ) :
    uniformFaceAQB3 (m+4) X ((m+3)*t) =
      cornerBern6 (uniformFaceAQB3C0 m X) (uniformFaceAQB3C1 m X)
        (uniformFaceAQB3C2 m X) (uniformFaceAQB3C3 m X)
        (uniformFaceAQB3C4 m X) (uniformFaceAQB3C5 m X)
        (uniformFaceAQB3C6 m X) t := by
  unfold uniformFaceAQB3C0 uniformFaceAQB3C1 uniformFaceAQB3C2
  unfold uniformFaceAQB3C3 uniformFaceAQB3C4 uniformFaceAQB3C5
  unfold uniformFaceAQB3C6 uniformFaceAQB3CompactSample
  unfold uniformFaceAQB3 uniformFaceACore cornerBern6
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem uniformFaceAQB3_coefficients_nonneg
    (m X : ℝ) (hm : 0 ≤ m) (hX : 0 ≤ X) :
    0 ≤ uniformFaceAQB3C0 m X ∧ 0 ≤ uniformFaceAQB3C1 m X ∧
    0 ≤ uniformFaceAQB3C2 m X ∧ 0 ≤ uniformFaceAQB3C3 m X ∧
    0 ≤ uniformFaceAQB3C4 m X ∧ 0 ≤ uniformFaceAQB3C5 m X ∧
    0 ≤ uniformFaceAQB3C6 m X := by
  unfold uniformFaceAQB3C0 uniformFaceAQB3C1 uniformFaceAQB3C2
  unfold uniformFaceAQB3C3 uniformFaceAQB3C4 uniformFaceAQB3C5
  unfold uniformFaceAQB3C6 uniformFaceAQB3CompactSample
  unfold uniformFaceAQB3 uniformFaceACore
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor <;> ring_nf <;> positivity

/-- The last return-face endpoint is nonnegative on `0 ≤ T ≤ n-1`. -/
theorem uniformFaceAQB3_nonneg_of_T_le
    (n X T : ℝ) (hn : 4 ≤ n) (hX : 0 ≤ X)
    (hT : 0 ≤ T) (hT1 : T ≤ n-1) :
    0 ≤ uniformFaceAQB3 n X T := by
  let m := n-4
  let t := T/(n-1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hn1 : 0 < n-1 := by linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; exact (div_le_one hn1).2 hT1
  have hid : (m+3)*t = T := by
    dsimp [m, t]
    field_simp [hn1.ne']
    ring
  have hnid : m+4 = n := by dsimp [m]; ring
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ :=
    uniformFaceAQB3_coefficients_nonneg m X hm hX
  rw [← hnid, ← hid, uniformFaceAQB3_compact_bernstein]
  exact cornerBern6_nonneg _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 ht ht1

/-! On the unbounded half, the return-side KKT condition supplies the missing
upper bound on `X`.  The following quantities are the positive slope and
intercept of that affine constraint after `n = m+4`, `T = m+3+z`, `q = 1`. -/

noncomputable def uniformFaceALargeM (m z : ℝ) : ℝ :=
  uniformReturnM (m+4) 1 (m+3+z) (m+3+z)

noncomputable def uniformFaceALargeK (m z : ℝ) : ℝ :=
  -uniformReturnK (m+4) (m+3+z) (m+3+z)

/-- The slope and positive intercept of the active return-side constraint at
the current terminal mixture weight. -/
noncomputable def uniformFaceACurrentM (n T q : ℝ) : ℝ :=
  uniformReturnM n 1 T (T*q)

noncomputable def uniformFaceACurrentK (n T q : ℝ) : ℝ :=
  -uniformReturnK n T (T*q)

theorem uniformFaceALargeM_pos
    (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 < uniformFaceALargeM m z := by
  unfold uniformFaceALargeM uniformReturnM
  ring_nf
  positivity

theorem uniformFaceALargeK_pos
    (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 < uniformFaceALargeK m z := by
  unfold uniformFaceALargeK uniformReturnK
  ring_nf
  positivity

theorem uniformFaceACurrentM_affine (n T q : ℝ) :
    uniformFaceACurrentM n T q =
      (1-q)*uniformFaceACurrentM n T 0
        +q*uniformFaceACurrentM n T 1 := by
  unfold uniformFaceACurrentM uniformReturnM
  ring

theorem uniformFaceACurrentM_zero_shift (m z : ℝ) :
    uniformFaceACurrentM (m+4) (m+3+z) 0 =
      2*m^3+35*m^2+191*m+312-(m+6)*z := by
  unfold uniformFaceACurrentM uniformReturnM
  ring

theorem uniformFaceACurrentM_one_sub (m z q : ℝ) :
    uniformFaceACurrentM (m+4) (m+3+z) 1
        -uniformFaceACurrentM (m+4) (m+3+z) q =
      (1-q)*(m+3)*(m+7)*(m+8)*(m+3+z) := by
  unfold uniformFaceACurrentM uniformReturnM
  ring

theorem uniformFaceACurrentK_affine (n T q : ℝ) :
    uniformFaceACurrentK n T q =
      (1-q)*uniformFaceACurrentK n T 0
        +q*uniformFaceACurrentK n T 1 := by
  unfold uniformFaceACurrentK uniformReturnK
  ring

theorem uniformReturnSide_eq_current (n a T Y q : ℝ) :
    uniformReturnSide n a T Y q =
      n*(a*Y)*uniformFaceACurrentM n T q-uniformFaceACurrentK n T q := by
  unfold uniformReturnSide uniformFaceACurrentM uniformFaceACurrentK
  unfold uniformReturnM
  ring

theorem uniformFaceACurrentK_pos
    (n T q : ℝ) (hn : 4 ≤ n) (hT1 : n-1 ≤ T)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 < uniformFaceACurrentK n T q := by
  let m := n-4
  let z := T-(n-1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : m+3+z = T := by dsimp [m, z]; ring
  have hK0 : 0 < uniformFaceACurrentK (m+4) (m+3+z) 0 := by
    unfold uniformFaceACurrentK uniformReturnK
    ring_nf
    positivity
  have hK1 : 0 < uniformFaceACurrentK (m+4) (m+3+z) 1 := by
    unfold uniformFaceACurrentK uniformReturnK
    ring_nf
    positivity
  rw [← hnid, ← hTid, uniformFaceACurrentK_affine]
  have hq0 : 0 ≤ 1-q := sub_nonneg.mpr hq1
  by_cases hqz : q = 0
  · simpa [hqz] using hK0
  · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hqz)
    positivity

theorem uniformFaceACurrentM_at_one_pos
    (n T : ℝ) (hn : 4 ≤ n) (hT1 : n-1 ≤ T) :
    0 < uniformFaceACurrentM n T 1 := by
  let m := n-4
  let z := T-(n-1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : m+3+z = T := by dsimp [m, z]; ring
  rw [← hnid, ← hTid]
  simpa [uniformFaceACurrentM, uniformFaceALargeM] using
    uniformFaceALargeM_pos m z hm hz

theorem uniformFaceACurrentM_nonpos_implies_q_lt_one
    (m z q : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z)
    (hM : uniformFaceACurrentM (m+4) (m+3+z) q ≤ 0) :
    q < 1 := by
  have hM1 : 0 < uniformFaceACurrentM (m+4) (m+3+z) 1 := by
    simpa [uniformFaceACurrentM, uniformFaceALargeM] using
      uniformFaceALargeM_pos m z hm hz
  have hdiff : 0 < uniformFaceACurrentM (m+4) (m+3+z) 1
      -uniformFaceACurrentM (m+4) (m+3+z) q := by linarith
  rw [uniformFaceACurrentM_one_sub] at hdiff
  have hfac : 0 < (m+3)*(m+7)*(m+8)*(m+3+z) := by positivity
  have hprod : 0 < (1-q)*((m+3)*(m+7)*(m+8)*(m+3+z)) := by
    simpa only [mul_assoc] using hdiff
  have hqdiff : 0 < 1-q := (mul_pos_iff_of_pos_right hfac).mp hprod
  linarith

theorem uniformFaceACurrentM_zero_nonpos_of_nonpos
    (m z q : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z)
    (hq : 0 ≤ q)
    (hM : uniformFaceACurrentM (m+4) (m+3+z) q ≤ 0) :
    uniformFaceACurrentM (m+4) (m+3+z) 0 ≤ 0 := by
  have hq1 : q < 1 :=
    uniformFaceACurrentM_nonpos_implies_q_lt_one m z q hm hz hM
  have hM1 : 0 < uniformFaceACurrentM (m+4) (m+3+z) 1 := by
    simpa [uniformFaceACurrentM, uniformFaceALargeM] using
      uniformFaceALargeM_pos m z hm hz
  rw [uniformFaceACurrentM_affine] at hM
  by_contra hnot
  have hM0 : 0 < uniformFaceACurrentM (m+4) (m+3+z) 0 :=
    lt_of_not_ge hnot
  have : 0 < (1-q)*uniformFaceACurrentM (m+4) (m+3+z) 0
      +q*uniformFaceACurrentM (m+4) (m+3+z) 1 := by positivity
  linarith

theorem uniformFaceACurrentM_nonpos_surplus_bound
    (m z q : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) (hq : 0 ≤ q)
    (hM : uniformFaceACurrentM (m+4) (m+3+z) q ≤ 0) :
    2*m^3+35*m^2+191*m+312 ≤ (m+6)*z := by
  have hM0 := uniformFaceACurrentM_zero_nonpos_of_nonpos m z q hm hz hq hM
  rw [uniformFaceACurrentM_zero_shift] at hM0
  linarith

end SSP.K3AllStages
