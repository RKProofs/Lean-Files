import SSPLean.K3AllStagesFaceBasic

set_option autoImplicit false

namespace SSP.K3AllStages

open SSP.K3S4Renewal
open SSP.K3S4KKT

/-! In the nonpositive-current-slope branch, retain the positive common
denominator which appears after the surplus substitution.  This makes the
projective `X`-Bernstein coefficients coefficientwise nonnegative. -/

noncomputable def uniformFaceACoreXC0 (n T q : ℝ) : ℝ :=
  uniformFaceACore n 0 T q

noncomputable def uniformFaceACoreXC1 (n T q : ℝ) : ℝ :=
  (-11*uniformFaceACore n 0 T q+18*uniformFaceACore n 1 T q
    -9*uniformFaceACore n 2 T q+2*uniformFaceACore n 3 T q)/6

noncomputable def uniformFaceACoreXC2 (n T q : ℝ) : ℝ :=
  (2*uniformFaceACore n 0 T q-5*uniformFaceACore n 1 T q
    +4*uniformFaceACore n 2 T q-uniformFaceACore n 3 T q)/2

noncomputable def uniformFaceACoreXC3 (n T q : ℝ) : ℝ :=
  (-uniformFaceACore n 0 T q+3*uniformFaceACore n 1 T q
    -3*uniformFaceACore n 2 T q+uniformFaceACore n 3 T q)/6

noncomputable def uniformFaceACoreHom (n T q x : ℝ) : ℝ :=
  uniformFaceACoreXC0 n T q*(1-x)^3
    +uniformFaceACoreXC1 n T q*x*(1-x)^2
    +uniformFaceACoreXC2 n T q*x^2*(1-x)
    +uniformFaceACoreXC3 n T q*x^3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformFaceACoreHom_projective (n X T q : ℝ)
    (hX1 : 1+X ≠ 0) :
    uniformFaceACore n X T q =
      (1+X)^3*uniformFaceACoreHom n T q (X/(1+X)) := by
  unfold uniformFaceACoreHom uniformFaceACoreXC0 uniformFaceACoreXC1
  unfold uniformFaceACoreXC2 uniformFaceACoreXC3 uniformFaceACore
  field_simp [hX1]
  ring_nf

noncomputable def uniformFaceANonposP (m : ℝ) : ℝ :=
  2*m^3+35*m^2+191*m+312

noncomputable def uniformFaceANonposZ (m s : ℝ) : ℝ :=
  uniformFaceANonposP m/(m+6)+s

noncomputable def uniformFaceANonposT (m s : ℝ) : ℝ :=
  m+3+uniformFaceANonposZ m s

noncomputable def uniformFaceANonposQ (m s v : ℝ) : ℝ :=
  v*(m+6)*s /
    ((m+3)*(m+7)*(m+8)*uniformFaceANonposT m s)

noncomputable def uniformFaceANonposScale (m : ℝ) : ℝ :=
  (m+3)^2*(m+6)*(m+7)^3*(m+8)^3

noncomputable def uniformFaceANonposScaled (m s v X : ℝ) : ℝ :=
  uniformFaceANonposScale m*
    uniformFaceACore (m+4) X (uniformFaceANonposT m s)
      (uniformFaceANonposQ m s v)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
noncomputable def FaceCoreProduct (n X T U : ℝ) : ℝ :=
  -4*U^3*X*n*(n - 1)^2*(n + 1)*(n + 2)*(T*n + 2*n - 2) - U^2*X^2*n^2*(n - 1)^2*(n^2 + 9*n + 26) + 2*U^2*X*n*(n - 1)*(2*T^2*n^4 + 4*T^2*n^3 - 7*T^2*n^2 - 12*T^2*n + 7*T*n^4 + 20*T*n^3 - 7*T*n^2 - 20*T*n - 2*n^4 - 2*n^3 - 6*n^2 + 26*n - 16) - U^2*(n + 2)*(-T^4*n^3 - T^4*n^2 + 2*T^3*n^4 - 8*T^3*n^3 - 2*T^3*n^2 + 8*T^3*n + T^2*n^5 + 25*T^2*n^4 - 33*T^2*n^3 - 13*T^2*n^2 + 20*T^2*n - 12*T*n^5 + 48*T*n^4 - 72*T*n^3 + 48*T*n^2 - 12*T*n - 12*n^5 + 60*n^4 - 120*n^3 + 120*n^2 - 60*n + 12) + 2*U*X^2*n^2*(n - 1)*(3*T*n^3 + 12*T*n^2 + 15*T*n + 4*n^3 + 2*n^2 - 22*n + 16) - U*X*n*(-T^3*n^3 - 3*T^3*n^2 - 2*T^3*n + 4*T^2*n^5 + 28*T^2*n^4 + 40*T^2*n^3 - 28*T^2*n^2 - 44*T^2*n - 20*T*n^5 - 20*T*n^4 + 72*T*n^3 - 4*T*n^2 - 28*T*n - 20*n^5 + 24*n^4 + 104*n^3 - 256*n^2 + 204*n - 56) + 2*U*(n - 1)*(n + 2)*(T^3*n^4 + 5*T^3*n^3 + 8*T^3*n^2 + 4*T^3*n - 2*T^2*n^4 - 10*T^2*n^3 + 2*T^2*n^2 + 10*T^2*n + 6*T*n^4 - 18*T*n^3 + 18*T*n^2 - 6*T*n + 12*n^4 - 48*n^3 + 72*n^2 - 48*n + 12) + 6*X^3*n^3*(n - 1) + 4*X^2*n^2*(n - 1)^3*(2*n + 5) + 8*X*n*(n - 1)^4*(2*n + 5) + 12*(n - 1)^5*(n + 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem FaceCoreProduct_eq (n X T q : ℝ) :
    uniformFaceACore n X T q = FaceCoreProduct n X T (T*q) := by
  unfold uniformFaceACore FaceCoreProduct
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
noncomputable def NonposCompactPolynomial (m s v X : ℝ) : ℝ :=
  6*X^3*(m + 3)^3*(m + 4)^3*(m + 6)*(m + 7)^3*(m + 8)^3 - X^2*s^2*v^2*(m + 3)^2*(m + 4)^2*(m + 6)^3*(m + 7)*(m + 8)*(m^2 + 17*m + 78) + 2*X^2*s*v*(m + 3)^2*(m + 4)^2*(m + 6)*(m + 7)^2*(m + 8)^2*(6*m^6 + 204*m^5 + 3*m^4*s + 2842*m^4 + 66*m^3*s + 20732*m^3 + 543*m^2*s + 83310*m^2 + 1974*m*s + 174282*m + 2664*s + 147816) + 4*X^2*(m + 3)^5*(m + 4)^2*(m + 6)*(m + 7)^3*(m + 8)^3*(2*m + 13) - 4*X*s^3*v^3*(m + 3)*(m + 4)*(m + 5)*(m + 6)^4*(2*m^4 + 44*m^3 + m^2*s + 346*m^2 + 10*m*s + 1148*m + 24*s + 1356) + 2*X*s^2*v^2*(m + 3)*(m + 4)*(m + 6)*(m + 7)*(m + 8)*(8*m^10 + 432*m^9 + 8*m^8*s + 10322*m^8 + 336*m^7*s + 143592*m^7 + 2*m^6*s^2 + 6059*m^6*s + 1286880*m^6 + 60*m^5*s^2 + 61200*m^5*s + 7757084*m^5 + 737*m^4*s^2 + 378165*m^4*s + 31823974*m^4 + 4728*m^3*s^2 + 1461348*m^3*s + 87678468*m^3 + 16628*m^2*s^2 + 3442268*m^2*s + 155159840*m^2 + 30192*m*s^2 + 4509936*m*s + 159190824*m + 21888*s^2 + 2511360*s + 71890272) + X*s*v*(m + 3)*(m + 4)*(m + 7)^2*(m + 8)^2*(-8*m^11 - 504*m^10 - 4*m^9*s - 14184*m^9 - 204*m^8*s - 235440*m^8 + 2*m^7*s^2 - 4532*m^7*s - 2561428*m^7 + 78*m^6*s^2 - 57636*m^6*s - 19177640*m^6 + m^5*s^3 + 1284*m^5*s^2 - 462736*m^5*s - 100823520*m^5 + 27*m^4*s^3 + 11562*m^4*s^2 - 2432844*m^4*s - 372164328*m^4 + 290*m^3*s^3 + 61474*m^3*s^2 - 8375768*m^3*s - 945135124*m^3 + 1548*m^2*s^3 + 192840*m^2*s^2 - 18204684*m^2*s - 1572617736*m^2 + 4104*m*s^3 + 330120*m*s^2 - 22660920*m*s - 1543025160*m + 4320*s^3 + 237600*s^2 - 12305952*s - 676430784) + 8*X*(m + 3)^6*(m + 4)*(m + 6)*(m + 7)^3*(m + 8)^3*(2*m + 13) + s^2*v^2*(m + 7)*(m + 8)*(16*m^15 + 1344*m^14 + 32*m^13*s + 52220*m^13 + 2312*m^12*s + 1244572*m^12 + 24*m^11*s^2 + 76380*m^11*s + 20341996*m^11 + 1452*m^10*s^2 + 1527220*m^10*s + 241451708*m^10 + 8*m^9*s^3 + 39551*m^9*s^2 + 20614080*m^9*s + 2149450724*m^9 + 390*m^8*s^3 + 640071*m^8*s^2 + 198285744*m^8*s + 14609363316*m^8 + m^7*s^4 + 8376*m^7*s^3 + 6835957*m^7*s^2 + 1397909724*m^7*s + 76415877556*m^7 + 37*m^6*s^4 + 103994*m^6*s^3 + 50572737*m^6*s^2 + 7311141860*m^6*s + 307520757940*m^6 + 584*m^5*s^4 + 822352*m^5*s^3 + 264364680*m^5*s^2 + 28358122936*m^5*s + 944157074480*m^5 + 5096*m^4*s^4 + 4293760*m^4*s^3 + 976124712*m^4*s^2 + 80544492784*m^4*s + 2171383315712*m^4 + 26544*m^3*s^4 + 14797344*m^3*s^3 + 2493965376*m^3*s^2 + 162784120560*m^3*s + 3620386832640*m^3 + 82512*m^2*s^4 + 32442336*m^2*s^3 + 4197705552*m^2*s^2 + 221636768832*m^2*s + 4130889456384*m^2 + 141696*m*s^4 + 41040000*m*s^3 + 4187547072*m*s^2 + 182177477568*m*s + 2883985003584*m + 103680*s^4 + 22809600*s^3 + 1875073536*s^2 + 68265047808*s + 928694362176) + 2*s*v*(m + 3)^2*(m + 6)*(m + 7)^2*(m + 8)^2*(8*m^12 + 552*m^11 + 12*m^10*s + 17240*m^10 + 684*m^9*s + 322128*m^9 + 6*m^8*s^2 + 17320*m^8*s + 4008796*m^8 + 270*m^7*s^2 + 256464*m^7*s + 34990212*m^7 + m^6*s^3 + 5254*m^6*s^2 + 2458230*m^6*s + 219554824*m^6 + 33*m^5*s^3 + 57732*m^5*s^2 + 15930054*m^5*s + 997520664*m^5 + 452*m^4*s^3 + 391652*m^4*s^2 + 70648334*m^4*s + 3255813252*m^4 + 3288*m^3*s^3 + 1678854*m^3*s^2 + 211627662*m^3*s + 7442945340*m^3 + 13392*m^2*s^3 + 4437648*m^2*s^2 + 409586256*m^2*s + 11309724360*m^2 + 28944*m*s^3 + 6607224*m*s^2 + 462285576*m*s + 10255034160*m + 25920*s^3 + 4237920*s^2 + 230970528*s + 4196146032) + 12*(m + 3)^7*(m + 6)^2*(m + 7)^3*(m + 8)^3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem NonposCompactPolynomial_eq (m s v X : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceANonposScaled m s v X = NonposCompactPolynomial m s v X := by
  have ha : m+6 ≠ 0 := by linarith
  have hb : m+3 ≠ 0 := by linarith
  have hc : m+7 ≠ 0 := by linarith
  have hd : m+8 ≠ 0 := by linarith
  have hT : uniformFaceANonposT m s ≠ 0 := by
    unfold uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP
    positivity
  have hU : uniformFaceANonposT m s * uniformFaceANonposQ m s v =
      v*(m+6)*s / ((m+3)*(m+7)*(m+8)) := by
    unfold uniformFaceANonposQ
    field_simp [hT]
  unfold uniformFaceANonposScaled
  rw [FaceCoreProduct_eq, hU]
  unfold uniformFaceANonposScale FaceCoreProduct
  unfold uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP
  unfold NonposCompactPolynomial
  field_simp [ha,hb,hc,hd]
  ring

noncomputable def uniformFaceANonposXB0 (m s v : ℝ) : ℝ :=
  uniformFaceANonposScaled m s v 0

noncomputable def uniformFaceANonposXB1 (m s v : ℝ) : ℝ :=
  -(5/6)*uniformFaceANonposScaled m s v 0
    +(1/3)*uniformFaceANonposScaled m s v 1
    +3*uniformFaceANonposScaled m s v (1/3)
    -(3/2)*uniformFaceANonposScaled m s v (2/3)

noncomputable def uniformFaceANonposXB2 (m s v : ℝ) : ℝ :=
  (1/3)*uniformFaceANonposScaled m s v 0
    -(5/6)*uniformFaceANonposScaled m s v 1
    -(3/2)*uniformFaceANonposScaled m s v (1/3)
    +3*uniformFaceANonposScaled m s v (2/3)

noncomputable def uniformFaceANonposXB3 (m s v : ℝ) : ℝ :=
  uniformFaceANonposScaled m s v 1


set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem FaceCore_bernstein_X (n T q X : ℝ) :
    uniformFaceACore n X T q =
      cornerBern3 (uniformFaceACore n 0 T q)
        (-(5/6)*uniformFaceACore n 0 T q+(1/3)*uniformFaceACore n 1 T q
          +3*uniformFaceACore n (1/3) T q-(3/2)*uniformFaceACore n (2/3) T q)
        ((1/3)*uniformFaceACore n 0 T q-(5/6)*uniformFaceACore n 1 T q
          -(3/2)*uniformFaceACore n (1/3) T q+3*uniformFaceACore n (2/3) T q)
        (uniformFaceACore n 1 T q) X := by
  unfold uniformFaceACore cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem uniformFaceANonposScaled_bernstein_X (m s v X : ℝ) :
    uniformFaceANonposScaled m s v X =
      cornerBern3 (uniformFaceANonposXB0 m s v)
        (uniformFaceANonposXB1 m s v) (uniformFaceANonposXB2 m s v)
        (uniformFaceANonposXB3 m s v) X := by
  unfold uniformFaceANonposXB0 uniformFaceANonposXB1
  unfold uniformFaceANonposXB2 uniformFaceANonposXB3 uniformFaceANonposScaled
  conv_lhs => rw [FaceCore_bernstein_X]
  unfold cornerBern3
  ring

noncomputable def uniformCubicSampleB0 (f : ℝ → ℝ) : ℝ := f 0

noncomputable def uniformCubicSampleB1 (f : ℝ → ℝ) : ℝ :=
  -(5/6)*f 0+(1/3)*f 1+3*f (1/3)-(3/2)*f (2/3)

noncomputable def uniformCubicSampleB2 (f : ℝ → ℝ) : ℝ :=
  (1/3)*f 0-(5/6)*f 1-(3/2)*f (1/3)+3*f (2/3)

noncomputable def uniformCubicSampleB3 (f : ℝ → ℝ) : ℝ := f 1


noncomputable def GenericNonposXB0 (n T Q scale v : ℝ) : ℝ :=
  scale*uniformFaceACore n 0 T (Q*v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem GenericNonposXB0_bernstein (n T Q scale v : ℝ) :
    GenericNonposXB0 n T Q scale v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => GenericNonposXB0 n T Q scale u))
        (uniformCubicSampleB1 (fun u => GenericNonposXB0 n T Q scale u))
        (uniformCubicSampleB2 (fun u => GenericNonposXB0 n T Q scale u))
        (uniformCubicSampleB3 (fun u => GenericNonposXB0 n T Q scale u)) v := by
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold GenericNonposXB0 uniformFaceACore cornerBern3
  ring

theorem GenericNonposXB0_eq (m s v : ℝ) :
    uniformFaceANonposXB0 m s v =
      GenericNonposXB0 (m+4) (uniformFaceANonposT m s)
        ((m+6)*s/((m+3)*(m+7)*(m+8)*uniformFaceANonposT m s))
        (uniformFaceANonposScale m) v := by
  unfold uniformFaceANonposXB0 uniformFaceANonposScaled GenericNonposXB0
  have hQ : uniformFaceANonposQ m s v =
      ((m+6)*s/((m+3)*(m+7)*(m+8)*uniformFaceANonposT m s))*v := by
    unfold uniformFaceANonposQ
    ring
  rw [hQ]
  


noncomputable def GenericNonposXB1 (n T Q scale v : ℝ) : ℝ :=
  -(5/6)*scale*uniformFaceACore n 0 T (Q*v)+(1/3)*scale*uniformFaceACore n 1 T (Q*v)+3*scale*uniformFaceACore n (1/3) T (Q*v)-(3/2)*scale*uniformFaceACore n (2/3) T (Q*v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem GenericNonposXB1_bernstein (n T Q scale v : ℝ) :
    GenericNonposXB1 n T Q scale v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => GenericNonposXB1 n T Q scale u))
        (uniformCubicSampleB1 (fun u => GenericNonposXB1 n T Q scale u))
        (uniformCubicSampleB2 (fun u => GenericNonposXB1 n T Q scale u))
        (uniformCubicSampleB3 (fun u => GenericNonposXB1 n T Q scale u)) v := by
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold GenericNonposXB1 uniformFaceACore cornerBern3
  ring

theorem GenericNonposXB1_eq (m s v : ℝ) :
    uniformFaceANonposXB1 m s v =
      GenericNonposXB1 (m+4) (uniformFaceANonposT m s)
        ((m+6)*s/((m+3)*(m+7)*(m+8)*uniformFaceANonposT m s))
        (uniformFaceANonposScale m) v := by
  unfold uniformFaceANonposXB1 uniformFaceANonposScaled GenericNonposXB1
  have hQ : uniformFaceANonposQ m s v =
      ((m+6)*s/((m+3)*(m+7)*(m+8)*uniformFaceANonposT m s))*v := by
    unfold uniformFaceANonposQ
    ring
  rw [hQ]
  ring


noncomputable def GenericNonposXB2 (n T Q scale v : ℝ) : ℝ :=
  (1/3)*scale*uniformFaceACore n 0 T (Q*v)-(5/6)*scale*uniformFaceACore n 1 T (Q*v)-(3/2)*scale*uniformFaceACore n (1/3) T (Q*v)+3*scale*uniformFaceACore n (2/3) T (Q*v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem GenericNonposXB2_bernstein (n T Q scale v : ℝ) :
    GenericNonposXB2 n T Q scale v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => GenericNonposXB2 n T Q scale u))
        (uniformCubicSampleB1 (fun u => GenericNonposXB2 n T Q scale u))
        (uniformCubicSampleB2 (fun u => GenericNonposXB2 n T Q scale u))
        (uniformCubicSampleB3 (fun u => GenericNonposXB2 n T Q scale u)) v := by
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold GenericNonposXB2 uniformFaceACore cornerBern3
  ring

theorem GenericNonposXB2_eq (m s v : ℝ) :
    uniformFaceANonposXB2 m s v =
      GenericNonposXB2 (m+4) (uniformFaceANonposT m s)
        ((m+6)*s/((m+3)*(m+7)*(m+8)*uniformFaceANonposT m s))
        (uniformFaceANonposScale m) v := by
  unfold uniformFaceANonposXB2 uniformFaceANonposScaled GenericNonposXB2
  have hQ : uniformFaceANonposQ m s v =
      ((m+6)*s/((m+3)*(m+7)*(m+8)*uniformFaceANonposT m s))*v := by
    unfold uniformFaceANonposQ
    ring
  rw [hQ]
  ring


noncomputable def GenericNonposXB3 (n T Q scale v : ℝ) : ℝ :=
  scale*uniformFaceACore n 1 T (Q*v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem GenericNonposXB3_bernstein (n T Q scale v : ℝ) :
    GenericNonposXB3 n T Q scale v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => GenericNonposXB3 n T Q scale u))
        (uniformCubicSampleB1 (fun u => GenericNonposXB3 n T Q scale u))
        (uniformCubicSampleB2 (fun u => GenericNonposXB3 n T Q scale u))
        (uniformCubicSampleB3 (fun u => GenericNonposXB3 n T Q scale u)) v := by
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold GenericNonposXB3 uniformFaceACore cornerBern3
  ring

theorem GenericNonposXB3_eq (m s v : ℝ) :
    uniformFaceANonposXB3 m s v =
      GenericNonposXB3 (m+4) (uniformFaceANonposT m s)
        ((m+6)*s/((m+3)*(m+7)*(m+8)*uniformFaceANonposT m s))
        (uniformFaceANonposScale m) v := by
  unfold uniformFaceANonposXB3 uniformFaceANonposScaled GenericNonposXB3
  have hQ : uniformFaceANonposQ m s v =
      ((m+6)*s/((m+3)*(m+7)*(m+8)*uniformFaceANonposT m s))*v := by
    unfold uniformFaceANonposQ
    ring
  rw [hQ]
  

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformFaceANonposXB0_bernstein_v (m s v : ℝ) :
    uniformFaceANonposXB0 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposXB0 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposXB0 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposXB0 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposXB0 m s u)) v := by
  simp only [GenericNonposXB0_eq]
  exact GenericNonposXB0_bernstein _ _ _ _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformFaceANonposXB1_bernstein_v (m s v : ℝ) :
    uniformFaceANonposXB1 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposXB1 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposXB1 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposXB1 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposXB1 m s u)) v := by
  simp only [GenericNonposXB1_eq]
  exact GenericNonposXB1_bernstein _ _ _ _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformFaceANonposXB2_bernstein_v (m s v : ℝ) :
    uniformFaceANonposXB2 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposXB2 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposXB2 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposXB2 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposXB2 m s u)) v := by
  simp only [GenericNonposXB2_eq]
  exact GenericNonposXB2_bernstein _ _ _ _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformFaceANonposXB3_bernstein_v (m s v : ℝ) :
    uniformFaceANonposXB3 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposXB3 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposXB3 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposXB3 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposXB3 m s u)) v := by
  simp only [GenericNonposXB3_eq]
  exact GenericNonposXB3_bernstein _ _ _ _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposXB0_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposXB0 m s v := by
  rw [uniformFaceANonposXB0_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    simp only [uniformCubicSampleB0, uniformCubicSampleB1,
      uniformCubicSampleB2, uniformCubicSampleB3]
    unfold uniformFaceANonposXB0
    simp only [NonposCompactPolynomial_eq m s _ _ hm hs]
    unfold NonposCompactPolynomial
    ring_nf
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposXB1_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposXB1 m s v := by
  rw [uniformFaceANonposXB1_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    simp only [uniformCubicSampleB0, uniformCubicSampleB1,
      uniformCubicSampleB2, uniformCubicSampleB3]
    unfold uniformFaceANonposXB1
    simp only [NonposCompactPolynomial_eq m s _ _ hm hs]
    unfold NonposCompactPolynomial
    ring_nf
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposXB2_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposXB2 m s v := by
  rw [uniformFaceANonposXB2_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    simp only [uniformCubicSampleB0, uniformCubicSampleB1,
      uniformCubicSampleB2, uniformCubicSampleB3]
    unfold uniformFaceANonposXB2
    simp only [NonposCompactPolynomial_eq m s _ _ hm hs]
    unfold NonposCompactPolynomial
    ring_nf
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposXB3_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposXB3 m s v := by
  rw [uniformFaceANonposXB3_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    simp only [uniformCubicSampleB0, uniformCubicSampleB1,
      uniformCubicSampleB2, uniformCubicSampleB3]
    unfold uniformFaceANonposXB3
    simp only [NonposCompactPolynomial_eq m s _ _ hm hs]
    unfold NonposCompactPolynomial
    ring_nf
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem uniformFaceANonposScaled_nonneg_of_X_le_one
    (m s v X : ℝ)
    (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hX : 0 ≤ X) (hX1 : X ≤ 1) :
    0 ≤ uniformFaceANonposScaled m s v X := by
  rw [uniformFaceANonposScaled_bernstein_X]
  exact cornerBern3_nonneg _ _ _ _ _
    (uniformFaceANonposXB0_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposXB1_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposXB2_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposXB3_nonneg m s v hm hs hv hv1)
    hX hX1

/-! On the far unbounded tail, use the ordinary power coefficients.  The
quadratic and cubic coefficients are nonnegative, so positivity of the value
and derivative at one sufficiently large point propagates to the right. -/

noncomputable def uniformFaceANonposXC0 (m s v : ℝ) : ℝ :=
  uniformFaceANonposScale m *
    uniformFaceACoreXC0 (m+4) (uniformFaceANonposT m s)
      (uniformFaceANonposQ m s v)

noncomputable def uniformFaceANonposXC1 (m s v : ℝ) : ℝ :=
  uniformFaceANonposScale m *
    uniformFaceACoreXC1 (m+4) (uniformFaceANonposT m s)
      (uniformFaceANonposQ m s v)

noncomputable def uniformFaceANonposXC2 (m s v : ℝ) : ℝ :=
  uniformFaceANonposScale m *
    uniformFaceACoreXC2 (m+4) (uniformFaceANonposT m s)
      (uniformFaceANonposQ m s v)

noncomputable def uniformFaceANonposXC3 (m s v : ℝ) : ℝ :=
  uniformFaceANonposScale m *
    uniformFaceACoreXC3 (m+4) (uniformFaceANonposT m s)
      (uniformFaceANonposQ m s v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem uniformFaceANonposScaled_power (m s v X : ℝ) :
    uniformFaceANonposScaled m s v X =
      uniformFaceANonposXC0 m s v + uniformFaceANonposXC1 m s v*X
        +uniformFaceANonposXC2 m s v*X^2
        +uniformFaceANonposXC3 m s v*X^3 := by
  unfold uniformFaceANonposXC0 uniformFaceANonposXC1
  unfold uniformFaceANonposXC2 uniformFaceANonposXC3
  unfold uniformFaceACoreXC0 uniformFaceACoreXC1
  unfold uniformFaceACoreXC2 uniformFaceACoreXC3
  unfold uniformFaceANonposScaled uniformFaceACore
  ring


set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem NonposXC2_sample (m s v : ℝ) :
    uniformFaceANonposXC2 m s v =
      (2*uniformFaceANonposScaled m s v 0-5*uniformFaceANonposScaled m s v 1+4*uniformFaceANonposScaled m s v 2-uniformFaceANonposScaled m s v 3)/2 := by
  unfold uniformFaceANonposXC2 uniformFaceACoreXC2 uniformFaceANonposScaled
  ring


set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem NonposXC3_sample (m s v : ℝ) :
    uniformFaceANonposXC3 m s v =
      (-uniformFaceANonposScaled m s v 0+3*uniformFaceANonposScaled m s v 1-3*uniformFaceANonposScaled m s v 2+uniformFaceANonposScaled m s v 3)/6 := by
  unfold uniformFaceANonposXC3 uniformFaceACoreXC3 uniformFaceANonposScaled
  ring


end SSP.K3AllStages
