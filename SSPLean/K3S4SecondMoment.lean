import SSPLean.K3S4ExcursionKKT

/-!
# Compactifying the second-moment layer for `k = 3`, `s = 4`

On the sharp third- and fourth-moment boundary, an excursion with mean `u` and second
moment `A` has the moments of a mixture of an atom at zero and an Erlang-three law.  Its
nonzero mixture weight is

`p = 4*u^2/(3*A)`.

Thus the two unbounded second moments can be replaced by weights `p,q ∈ (0,1]`.  This
file records that change of variables and the exact 15-term polynomial obtained after
clearing `p^4*q^4` from the reduced renewal gap.
-/

set_option autoImplicit false

namespace SSP.K3S4SecondMoment

open SSP.K3S4Renewal
open SSP.K3S4ExcursionKKT

noncomputable def mixtureWeight (u A : ℝ) : ℝ := 4*u^2/(3*A)

theorem mixtureWeight_pos_le_one
    (u A : ℝ) (hu : 0 < u) (hA : 4*u^2 ≤ 3*A) :
    0 < mixtureWeight u A ∧ mixtureWeight u A ≤ 1 := by
  have hApos : 0 < A := by nlinarith [sq_pos_of_pos hu]
  constructor
  · unfold mixtureWeight
    positivity
  · unfold mixtureWeight
    rw [div_le_one (by positivity : 0 < 3*A)]
    exact hA

theorem secondMoment_eq_mixtureWeight
    (u A : ℝ) (hu : 0 < u) (hA : 0 < A) :
    A = 4*u^2/(3*mixtureWeight u A) := by
  unfold mixtureWeight
  field_simp [hu.ne', hA.ne']

theorem sharpThird_eq_mixtureWeight
    (u A : ℝ) (hu : 0 < u) (hA : 0 < A) :
    5*A^2/(4*u) = 20*u^3/(9*(mixtureWeight u A)^2) := by
  unfold mixtureWeight
  field_simp [hu.ne', hA.ne']
  ring

theorem sharpFourth_eq_mixtureWeight
    (u A : ℝ) (hu : 0 < u) (hA : 0 < A) :
    6*(5*A^2/(4*u))^2/(5*A) = 40*u^4/(9*(mixtureWeight u A)^3) := by
  unfold mixtureWeight
  field_simp [hu.ne', hA.ne']
  ring

/-- The excursion-reduced gap on the simultaneous sharp moment boundary, parameterized
by the two nonzero mixture weights. -/
noncomputable def sharpMixtureGap (r x u v p q : ℝ) : ℝ :=
  excursionReducedGap r x u (4*u^2/(3*p)) (20*u^3/(9*p^2))
    v (4*v^2/(3*q)) (20*v^3/(9*q^2))

/-- The only coefficient of `p^2*q^4` which is not manifestly positive before using the
state-return geometry. -/
noncomputable def mixtureHardCoeff (r x u v : ℝ) : ℝ :=
  17*r^3*u^3+39*r^3*u^2*x+27*r^3*u*x^2+5*r^3*x^3
    +13*r^2*u^2*v+39*r^2*u^2*x+38*r^2*u*v*x+54*r^2*u*x^2
    +25*r^2*v*x^2+15*r^2*x^3-r*u*v^2+38*r*u*v*x+27*r*u*x^2
    +20*r*v^2*x+50*r*v*x^2+15*r*x^3+20*v^2*x+25*v*x^2+5*x^3

/-- The exact polynomial `p^4*q^4 * sharpMixtureGap`.  It has only fifteen monomials in
`p,q`; this is the compact target for the remaining sharp second-moment corner. -/
noncomputable def sharpMixturePoly (r x u v p q : ℝ) : ℝ :=
  36*(r*u+r*x+x)^4*(r*u+r*x+v+x)^2*p^4*q^4
    +48*v^2*(r*u+r*x+x)^3*(r*u+r*x+v+x)*p^4*q^3
    -16*v^3*(r*u+r*x+x)^2*(5*r*u+5*r*x+4*v+5*x)*p^4*q^2
    +(160/3)*v^4*(r*u+r*x+x)^2*p^4*q+(80/81)*v^6*p^4
    +48*r*u^2*(r*u+r*x+x)^2*(r*u+r*x+v+x)
      *(2*r*u+2*r*x+v+2*x)*p^3*q^4
    +32*r*u^2*v^2*(r*u+r*x+x)*(6*r*u+6*r*x+5*v+6*x)*p^3*q^3
    -(32/9)*r*u^2*v^3*(50*r*u+50*r*x+11*v+50*x)*p^3*q^2
    +(320/9)*r*u^2*v^4*p^3*q
    +(16/3)*r*u^3*mixtureHardCoeff r x u v*p^2*q^4
    +(32/9)*r*u^3*v^2*(53*r*u+5*r*x+20*v+5*x)*p^2*q^3
    -(5600/81)*r*u^3*v^3*p^2*q^2
    +(32/3)*r*u^4*(3*r^2*u^2+5*r^2*x^2+5*r*v*x+10*r*x^2
      +5*v*x+5*x^2)*p*q^4
    +(320/9)*r*u^4*v^2*p*q^3+(80/81)*r^2*u^6*q^4

set_option maxHeartbeats 2000000 in
/-- Exact denominator-clearing identity for the compactified sharp corner. -/
theorem sharpMixtureGap_clear
    (r x u v p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) :
    p^4*q^4*sharpMixtureGap r x u v p q = sharpMixturePoly r x u v p q := by
  unfold sharpMixtureGap sharpMixturePoly mixtureHardCoeff
  unfold excursionReducedGap
  unfold geomGap geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4
  field_simp [hp, hq]
  ring

set_option linter.flexible false in
theorem sharpMixturePoly_at_p_zero
    (r x u v q : ℝ) (_hr : 0 ≤ r) (_hu : 0 ≤ u) (_hq : 0 ≤ q) :
    0 ≤ sharpMixturePoly r x u v 0 q := by
  simp [sharpMixturePoly]
  positivity

set_option linter.flexible false in
theorem sharpMixturePoly_at_q_zero
    (r x u v p : ℝ) (_hv : 0 ≤ v) (_hp : 0 ≤ p) :
    0 ≤ sharpMixturePoly r x u v p 0 := by
  simp [sharpMixturePoly]
  positivity

theorem sharpMixturePoly_at_one_nonneg
    (r x u v : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v) :
    0 ≤ sharpMixturePoly r x u v 1 1 := by
  have hgap := deepCorner r x u v 0 0 hr hx hu hv (by norm_num) (by norm_num)
  have hclear := sharpMixtureGap_clear r x u v 1 1 (by norm_num) (by norm_num)
  norm_num [sharpMixtureGap] at hclear
  rw [← hclear]
  convert hgap using 1
  all_goals ring_nf

/-- The no-return edge of the compactified second-moment problem follows from the
one-kernel theorem. -/
theorem sharpMixturePoly_noReturn
    (x u v p q : ℝ) (hx : 0 ≤ x) (hv : 0 < v) (hp : 0 < p)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    0 ≤ sharpMixturePoly 0 x u v p q := by
  let B := 4*v^2/(3*q)
  let D := 20*v^3/(9*q^2)
  let F := 40*v^4/(9*q^3)
  have hB : 4*v^2 ≤ 3*B := by
    dsimp [B]
    field_simp [hq.ne']
    nlinarith [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hq1)]
  have hD : 5*B^2 ≤ 4*v*D := by
    dsimp [B, D]
    field_simp [hq.ne']
    norm_num
  have hF : 6*D^2 ≤ 5*B*F := by
    dsimp [B, D, F]
    field_simp [hq.ne']
    norm_num
  have hFexact : 6*D^2/(5*B) = F := by
    dsimp [B, D, F]
    field_simp [hq.ne']
    ring
  have hterminal := noReturn_k3 x v B D F hx hv hB hD hF
  have hterminal' := sub_nonneg.mpr hterminal
  have hgap : 0 ≤ sharpMixtureGap 0 x u v p q := by
    simpa [sharpMixtureGap, excursionReducedGap, geomGap, geomM4, geomM3, geomM2,
      geomM1, kernelM2, kernelM3, B, D, hFexact] using hterminal'
  have hclear := sharpMixtureGap_clear 0 x u v p q hp.ne' hq.ne'
  rw [← hclear]
  positivity

/-! The only non-obvious Bernstein coefficient in the terminal mixture weight. -/

noncomputable def mixtureBernsteinC1 (T Y : ℝ) : ℝ :=
  180*T^3*Y+540*T^3-350*T^2*Y^2-900*T^2*Y-810*T^2
    +180*T*Y^3+90*T*Y^2+972*T*Y+486*T
    +270*Y^3+675*Y^2+729*Y+729

set_option maxHeartbeats 1000000 in
-- The proof expands two degree-six discriminant identities.
/-- The middle Bernstein coefficient in the geometric return coordinate is nonnegative.

The proof groups it as `A₄+B₃+C₂+D₁+729`.  If `T ≤ Y`, every group is
nonnegative.  For `T > Y`, put `d=T-Y`.  If `B₃ < 0`, then `8d<Y` and the
discriminant `4*A₄*C₂-B₃²` is nonnegative.  If `C₂ < 0` instead, the
opposite bound `2Y≤3d` makes `4*B₃*D₁-C₂²` nonnegative. -/
theorem mixtureBernsteinC1_nonneg (T Y : ℝ) (hT : 0 ≤ T) (hY : 0 ≤ Y) :
    0 ≤ mixtureBernsteinC1 T Y := by
  let A := 10*T*Y*(18*Y^2-35*T*Y+18*T^2)
  let B := 90*(Y-T)*(3*Y^2+4*T*Y-6*T^2)
  let C := 675*Y^2+972*T*Y-810*T^2
  let D := 486*T+729*Y
  have hquad : 0 ≤ 18*Y^2-35*T*Y+18*T^2 := by
    nlinarith [sq_nonneg (36*Y-35*T), sq_nonneg T]
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hdecomp : mixtureBernsteinC1 T Y = A+B+C+D+729 := by
    dsimp [mixtureBernsteinC1, A, B, C, D]
    ring
  rw [hdecomp]
  rcases le_total T Y with hTY | hYT
  · have hTYmul : T^2 ≤ T*Y := by
      nlinarith [mul_nonneg hT (sub_nonneg.mpr hTY)]
    have hTYsq : T^2 ≤ Y^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hTY) (by positivity : 0 ≤ Y+T)]
    have hinner : 0 ≤ 3*Y^2+4*T*Y-6*T^2 := by nlinarith
    have hB : 0 ≤ B := by
      dsimp [B]
      positivity
    have hC : 0 ≤ C := by
      dsimp [C]
      nlinarith
    positivity
  · let d := T-Y
    have hd : 0 ≤ d := by dsimp [d]; linarith
    have hTd : T = Y+d := by dsimp [d]; ring
    by_cases hinner : 0 < Y^2-8*Y*d-6*d^2
    · have hC : 0 ≤ C := by
        dsimp [C]
        rw [hTd]
        nlinarith [mul_nonneg hY hd]
      have hyprod : 0 < Y*(Y-8*d) := by
        nlinarith [sq_nonneg d]
      have h8d : 8*d < Y := by
        rcases (mul_pos_iff.mp hyprod) with hpos | hneg
        · linarith [hpos.2]
        · linarith [hneg.1]
      have hd4 := pow_le_pow_left₀ (by positivity : 0 ≤ 8*d) h8d.le 4
      have hd5 := pow_le_pow_left₀ (by positivity : 0 ≤ 8*d) h8d.le 5
      have hd6 := pow_le_pow_left₀ (by positivity : 0 ≤ 8*d) h8d.le 6
      have hd4' : 4096*d^4 ≤ Y^4 := by
        norm_num [mul_pow] at hd4
        exact hd4
      have hd5' : 32768*d^5 ≤ Y^5 := by
        norm_num [mul_pow] at hd5
        exact hd5
      have hd6' : 262144*d^6 ≤ Y^6 := by
        norm_num [mul_pow] at hd6
        exact hd6
      have hd4Y : 4096*Y^2*d^4 ≤ Y^6 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hd4') (sq_nonneg Y)]
      have hd5Y : 32768*Y*d^5 ≤ Y^6 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hd5') hY]
      have hdisc0 :
          0 ≤ 62*Y^6+76*Y^5*d+1007*Y^4*d^2+324*Y^3*d^3
            -2784*Y^2*d^4-2520*Y*d^5-540*d^6 := by
        have hY6 : 0 ≤ Y^6 := by positivity
        have h1 : 0 ≤ Y^5*d := by positivity
        have h2 : 0 ≤ Y^4*d^2 := by positivity
        have h3 : 0 ≤ Y^3*d^3 := by positivity
        nlinarith
      have hdisc : 0 ≤ 4*A*C-B^2 := by
        have hid : 4*A*C-B^2 = 540 *
            (62*Y^6+76*Y^5*d+1007*Y^4*d^2+324*Y^3*d^3
              -2784*Y^2*d^4-2520*Y*d^5-540*d^6) := by
          dsimp [A, B, C]
          rw [hTd]
          ring
        rw [hid]
        positivity
      have hsum : 0 ≤ A+B+C := by
        by_cases hB : 0 ≤ B
        · positivity
        · have hBneg : B < 0 := lt_of_not_ge hB
          have hsquares : (-B)^2 ≤ (A+C)^2 := by
            nlinarith [sq_nonneg (A-C)]
          have hminusB : -B ≤ A+C :=
            (sq_le_sq₀ (by linarith) (by positivity)).mp hsquares
          linarith
      have hD : 0 ≤ D := by dsimp [D]; positivity
      positivity
    · have hinner' : Y^2-8*Y*d-6*d^2 ≤ 0 := le_of_not_gt hinner
      have hB : 0 ≤ B := by
        dsimp [B]
        rw [hTd]
        nlinarith
      by_cases hCsign : 0 ≤ C
      · have hD : 0 ≤ D := by dsimp [D]; positivity
        positivity
      · have hCneg : C < 0 := lt_of_not_ge hCsign
        have hcore : 31*Y^2-24*d*Y-30*d^2 < 0 := by
          dsimp [C] at hCneg
          rw [hTd] at hCneg
          nlinarith
        have h2Y3d : 2*Y ≤ 3*d := by
          by_contra hnot
          have hstrict : 3*d < 2*Y := lt_of_not_ge hnot
          have hsecond : 0 < 15*d+22*Y := by nlinarith
          have hfactor : 0 < (2*Y-3*d)*(15*d+22*Y) :=
            mul_pos (by linarith) hsecond
          nlinarith
        have hsqbound : 4*Y^2 ≤ 9*d^2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr h2Y3d) (by positivity : 0 ≤ 3*d+2*Y)]
        have hfourth : 4*Y^4 ≤ 9*d^2*Y^2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hsqbound) (sq_nonneg Y)]
        have hdisc0 :
            0 ≤ 540*d^4+4080*d^3*Y+5844*d^2*Y^2+888*d*Y^3-961*Y^4 := by
          have h0 : 0 ≤ d^4 := by positivity
          have h1 : 0 ≤ d^3*Y := by positivity
          have h3 : 0 ≤ d*Y^3 := by positivity
          nlinarith
        have hdisc : 0 ≤ 4*B*D-C^2 := by
          have hid : 4*B*D-C^2 = 729 *
              (540*d^4+4080*d^3*Y+5844*d^2*Y^2+888*d*Y^3-961*Y^4) := by
            dsimp [B, C, D]
            rw [hTd]
            ring
          rw [hid]
          positivity
        have hBCD : 0 ≤ B+C+D := by
          have hD : 0 ≤ D := by dsimp [D]; positivity
          have hsquares : (-C)^2 ≤ (B+D)^2 := by
            nlinarith [sq_nonneg (B-D)]
          have hminusC : -C ≤ B+D :=
            (sq_le_sq₀ (by linarith) (by positivity)).mp hsquares
          linarith
        nlinarith

noncomputable def mixtureBernsteinC0 (T : ℝ) : ℝ :=
  27*(20*T^3-30*T^2+18*T+27)

theorem mixtureBernsteinC0_nonneg (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ mixtureBernsteinC0 T := by
  have hquad : 0 ≤ 20*T^2-30*T+18 := by
    nlinarith [sq_nonneg (4*T-3)]
  dsimp [mixtureBernsteinC0]
  nlinarith [mul_nonneg hT hquad]

noncomputable def mixtureBernsteinC2 (T Y : ℝ) : ℝ :=
  360*T^3*Y+540*T^3-700*T^2*Y^2-1800*T^2*Y-810*T^2
    +360*T*Y^3+1908*T*Y^2+1944*T*Y+486*T
    +702*Y^2+1458*Y+729

set_option maxHeartbeats 1000000 in
-- The proof expands the homogeneous degree-four Bernstein certificate.
/-- The final Bernstein coefficient.  Its quartic and cubic homogeneous parts are
positive definite.  If its quadratic part is negative, a degree-four Bernstein
certificate on `2Y ≤ T` proves that the cubic and linear parts dominate it. -/
theorem mixtureBernsteinC2_nonneg (T Y : ℝ) (hT : 0 ≤ T) (hY : 0 ≤ Y) :
    0 ≤ mixtureBernsteinC2 T Y := by
  let A := 20*T*Y*(18*Y^2-35*T*Y+18*T^2)
  let B := 36*T*(15*T^2-50*T*Y+53*Y^2)
  let C := -810*T^2+1944*T*Y+702*Y^2
  let D := 486*T+1458*Y
  have hquadA : 0 ≤ 18*Y^2-35*T*Y+18*T^2 := by
    nlinarith [sq_nonneg (36*Y-35*T), sq_nonneg T]
  have hquadB : 0 ≤ 15*T^2-50*T*Y+53*Y^2 := by
    nlinarith [sq_nonneg (15*T-25*Y), sq_nonneg Y]
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hdecomp : mixtureBernsteinC2 T Y = A+B+C+D+729 := by
    dsimp [mixtureBernsteinC2, A, B, C, D]
    ring
  rw [hdecomp]
  by_cases hCsign : 0 ≤ C
  · positivity
  · have hCneg : C < 0 := lt_of_not_ge hCsign
    have h2YT : 2*Y ≤ T := by
      by_contra hnot
      have hTY : T < 2*Y := lt_of_not_ge hnot
      have hmul : T^2 ≤ 2*T*Y := by
        nlinarith [mul_nonneg hT (sub_nonneg.mpr hTY.le)]
      dsimp [C] at hCneg
      nlinarith [mul_nonneg hT hY, sq_nonneg Y]
    have hbern :
        0 ≤ 135*(T-2*Y)^4
          +4*255*(2*Y)*(T-2*Y)^3
          +6*(961/4)*(2*Y)^2*(T-2*Y)^2
          +4*(723/4)*(2*Y)^3*(T-2*Y)
          +(2495/16)*(2*Y)^4 := by positivity
    have hdisc0 :
        0 ≤ 135*T^4+960*T^3*Y-3234*T^2*Y^2+2880*T*Y^3-169*Y^4 := by
      nlinarith [hbern]
    have hdisc : 0 ≤ 4*B*D-C^2 := by
      have hid : 4*B*D-C^2 = 2916 *
          (135*T^4+960*T^3*Y-3234*T^2*Y^2+2880*T*Y^3-169*Y^4) := by
        dsimp [B, C, D]
        ring
      rw [hid]
      positivity
    have hsquares : (-C)^2 ≤ (B+D)^2 := by
      nlinarith [sq_nonneg (B-D)]
    have hminusC : -C ≤ B+D :=
      (sq_le_sq₀ (by linarith) (by positivity)).mp hsquares
    nlinarith

noncomputable def mixtureQ0 (a Y : ℝ) : ℝ :=
  20*Y^4*a^2+1728*Y^3*a^3-2160*Y^3*a^2+1080*Y^3*a
    +1296*Y^2*a^2+540*Y^2*a+1944*Y*a+729

noncomputable def mixtureQ1Core (a T Y : ℝ) : ℝ :=
  360*T^3*Y*a+540*T^3-700*T^2*Y^2*a-1800*T^2*Y*a-810*T^2
    +360*T*Y^3*a+1728*T*Y^2*a^2+180*T*Y^2*a+1944*T*Y*a+486*T
    -540*Y^3*a^2+540*Y^3*a-648*Y^2*a^2+1350*Y^2*a
    +1458*Y*a+729

noncomputable def mixtureQ2 (a T Y : ℝ) : ℝ :=
  T^2*(20*T^4-792*T^2*Y*a-1296*T^2+1440*T*Y^2*a
    +3240*T*Y*a+972*T-2268*Y^2*a^2+2160*Y^2*a+972*Y*a+729)

/-- The scale-free sharp-corner polynomial; importantly, it is only quadratic in the
terminal mixture weight `q`. -/
noncomputable def mixtureQ (a T Y q : ℝ) : ℝ :=
  mixtureQ0 a Y + 2*T*mixtureQ1Core a T Y*q + mixtureQ2 a T Y*q^2

theorem mixtureQ0_nonneg (a Y : ℝ) (ha : 0 ≤ a) (hY : 0 ≤ Y) :
    0 ≤ mixtureQ0 a Y := by
  have hmid : 0 ≤ 16*a^2-20*a+10 := by
    nlinarith [sq_nonneg (4*a-5/2)]
  have hid : mixtureQ0 a Y =
      20*Y^4*a^2+108*Y^3*a*(16*a^2-20*a+10)
        +1296*Y^2*a^2+540*Y^2*a+1944*Y*a+729 := by
    dsimp [mixtureQ0]
    ring
  rw [hid]
  positivity

/-- Positivity of the coefficient of `q`, obtained from its three degree-two
Bernstein coefficients in `a`. -/
theorem mixtureQ1Core_nonneg (a T Y : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hY : 0 ≤ Y) : 0 ≤ mixtureQ1Core a T Y := by
  have hc0 := mixtureBernsteinC0_nonneg T hT
  have hc1 := mixtureBernsteinC1_nonneg T Y hT hY
  have hc2 := mixtureBernsteinC2_nonneg T Y hT hY
  have hid : mixtureQ1Core a T Y =
      mixtureBernsteinC0 T*(1-a)^2
        +2*mixtureBernsteinC1 T Y*a*(1-a)
        +mixtureBernsteinC2 T Y*a^2 := by
    dsimp [mixtureQ1Core, mixtureBernsteinC0, mixtureBernsteinC1,
      mixtureBernsteinC2]
    ring
  rw [hid]
  positivity

set_option maxHeartbeats 2000000 in
-- Clearing the normalization denominators expands the full 15-term polynomial.
/-- Exact scale normalization of the original 15-term polynomial.  The return mixture
weight `p` disappears from the scale-free factor `mixtureQ`. -/
theorem sharpMixturePoly_normalize (L a T Y p q : ℝ)
    (hp : p ≠ 0) (hY : Y ≠ 0) (hden : p*Y+a ≠ 0) :
    sharpMixturePoly (a/(p*Y)) (L*p*Y*(1-a)/(p*Y+a))
        (L*p*Y) (L*q*T) p q
      = (4/81)*L^6*p^4*q^4*mixtureQ a T Y q := by
  unfold sharpMixturePoly mixtureHardCoeff mixtureQ mixtureQ0 mixtureQ1Core mixtureQ2
  field_simp [hp, hY, hden]
  ring

theorem mixtureQ_at_one_nonneg (a T Y : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) : 0 ≤ mixtureQ a T Y 1 := by
  have hden : Y+a ≠ 0 := by positivity
  have hx : 0 ≤ Y*(1-a)/(Y+a) := by positivity
  have hpoly := sharpMixturePoly_at_one_nonneg (a/Y) (Y*(1-a)/(Y+a)) Y T
    (by positivity) hx hY hT
  have hnorm := sharpMixturePoly_normalize 1 a T Y 1 1 (by norm_num) hY.ne' (by simpa using hden)
  norm_num at hnorm
  rw [hnorm] at hpoly
  nlinarith

/-- Endpoint positivity together with the nonnegative linear coefficient proves the
quadratic `mixtureQ` on the full interval `0 ≤ q ≤ 1`. -/
theorem mixtureQ_nonneg (a T Y q : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ mixtureQ a T Y q := by
  have hQ0 := mixtureQ0_nonneg a Y ha0 hY.le
  have hQ1 := mixtureQ1Core_nonneg a T Y ha0 ha1 hT.le hY.le
  have hQone := mixtureQ_at_one_nonneg a T Y ha0 ha1 hT hY
  by_cases hQ2 : 0 ≤ mixtureQ2 a T Y
  · unfold mixtureQ
    positivity
  · have hQ2neg : mixtureQ2 a T Y < 0 := lt_of_not_ge hQ2
    have hqprod : 0 ≤ q*(1-q) := mul_nonneg hq0 (sub_nonneg.mpr hq1)
    have hconc : 0 ≤ q*(1-q)*(-mixtureQ2 a T Y) :=
      mul_nonneg hqprod (by linarith)
    have hid : mixtureQ a T Y q =
        (1-q)*mixtureQ0 a Y+q*mixtureQ a T Y 1
          +q*(1-q)*(-mixtureQ2 a T Y) := by
      unfold mixtureQ
      ring
    rw [hid]
    positivity

/-- Positivity of the complete sharp-boundary polynomial for both mixture weights. -/
theorem sharpMixturePoly_nonneg
    (r x u v p q : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v)
    (hp : 0 < p) (_hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    0 ≤ sharpMixturePoly r x u v p q := by
  by_cases hr0 : r = 0
  · subst r
    exact sharpMixturePoly_noReturn x u v p q hx hv hp hq hq1
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    let L := r*u+(r+1)*x
    let a := r*u/L
    let Y := u/(p*L)
    let T := v/(q*L)
    have hL : 0 < L := by
      dsimp [L]
      have : 0 < r*u := mul_pos hrp hu
      positivity
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have ha1 : a ≤ 1 := by
      dsimp [a]
      rw [div_le_one hL]
      dsimp [L]
      nlinarith [mul_nonneg (by linarith : 0 ≤ r+1) hx]
    have hY : 0 < Y := by dsimp [Y]; positivity
    have hT : 0 < T := by dsimp [T]; positivity
    have hden : p*Y+a ≠ 0 := by positivity
    have hQ := mixtureQ_nonneg a T Y q ha0 ha1 hT hY hq.le hq1
    have hnorm := sharpMixturePoly_normalize L a T Y p q hp.ne' hY.ne' hden
    have hnormalized : 0 ≤
        sharpMixturePoly (a/(p*Y)) (L*p*Y*(1-a)/(p*Y+a))
          (L*p*Y) (L*q*T) p q := by
      rw [hnorm]
      positivity
    have hrid : a/(p*Y) = r := by
      dsimp [a, Y]
      field_simp [hp.ne', hL.ne', hu.ne']
    have huid : L*p*Y = u := by
      dsimp [Y]
      field_simp [hp.ne', hL.ne']
    have hvid : L*q*T = v := by
      dsimp [T]
      field_simp [hq.ne', hL.ne']
    have hxid : L*p*Y*(1-a)/(p*Y+a) = x := by
      dsimp [a, Y, L]
      field_simp [hp.ne', hL.ne', hu.ne', hden]
      ring
    rwa [hrid, hxid, huid, hvid] at hnormalized

/-! ## The next KKT layer: the return face -/

/-- Numerator of the return-face discriminant after the same scale and mixture
normalization used for `mixtureQ`. -/
noncomputable def returnFacePoly (a T Y q : ℝ) : ℝ :=
  20*T^6*q^2-720*T^4*Y*a*q^3+608*T^4*Y*a*q^2+20*T^4*Y*a*q
    -1296*T^4*q^2+1080*T^4*q-1080*T^3*Y*a*q^3+2880*T^3*Y*a*q^2
    -2200*T^3*Y*a*q+972*T^3*q^2-1620*T^3*q
    -468*T^2*Y^2*a^2*q^2+1776*T^2*Y^2*a^2*q
    -648*T^2*Y*a*q^2+3528*T^2*Y*a*q+729*T^2*q^2+972*T^2*q
    +864*T*Y^2*a^2*q+1836*T*Y*a*q+1458*T*q
    +48*Y^3*a^3+936*Y^2*a^2+1404*Y*a+729

set_option linter.flexible false in
theorem returnFacePoly_at_q_zero_nonneg
    (a T Y : ℝ) (ha : 0 ≤ a) (hY : 0 ≤ Y) :
    0 ≤ returnFacePoly a T Y 0 := by
  simp [returnFacePoly]
  positivity

/-- The no-return edge of the normalized return-face certificate. -/
theorem returnFacePoly_at_a_zero_nonneg
    (T q : ℝ) (hT : 0 ≤ T) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ returnFacePoly 0 T 0 q := by
  let c0 := (729 : ℝ)
  let c1 := 2*T*mixtureBernsteinC0 T
  let c2 := returnFacePoly 0 T 0 1-c0-c1
  have hc0 : 0 ≤ c0 := by norm_num [c0]
  have hc1 : 0 ≤ c1 := by
    dsimp [c1]
    exact mul_nonneg (mul_nonneg (by norm_num) hT) (mixtureBernsteinC0_nonneg T hT)
  have hend : 0 ≤ returnFacePoly 0 T 0 1 := by
    have hid : returnFacePoly 0 T 0 1 =
        (T-3)^2*(20*T^4+120*T^3+324*T^2+216*T+81) := by
      unfold returnFacePoly
      ring
    rw [hid]
    positivity
  have hidq : returnFacePoly 0 T 0 q = c0+c1*q+c2*q^2 := by
    dsimp [c0, c1, c2, returnFacePoly, mixtureBernsteinC0]
    ring
  rw [hidq]
  by_cases hc2 : 0 ≤ c2
  · positivity
  · have hconc : 0 ≤ q*(1-q)*(-c2) := by
      exact mul_nonneg (mul_nonneg hq0 (sub_nonneg.mpr hq1)) (by linarith)
    have hid : c0+c1*q+c2*q^2 =
        (1-q)*c0+q*returnFacePoly 0 T 0 1+q*(1-q)*(-c2) := by
      dsimp [c2, c0, c1, mixtureBernsteinC0]
      unfold returnFacePoly
      ring
    rw [hid]
    positivity

/-- A cubic on the unit interval is nonnegative if its constant and linear coefficients
are nonnegative, its leading coefficient is nonpositive, and its value at one is
nonnegative.  This is the shape occurring in `returnFacePoly`. -/
theorem cubic_unit_nonneg_of_leading_nonpos
    (c0 c1 c2 c3 q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc3 : c3 ≤ 0)
    (hend : 0 ≤ c0+c1+c2+c3) :
    0 ≤ c0+c1*q+c2*q^2+c3*q^3 := by
  by_cases hs : 0 ≤ -c2-(q+1)*c3
  · have hid : c0+c1*q+c2*q^2+c3*q^3 =
        (1-q)*c0+q*(c0+c1+c2+c3)+q*(1-q)*(-c2-(q+1)*c3) := by ring
    rw [hid]
    positivity
  · have hs' : 0 < c2+(q+1)*c3 := by linarith
    have hinner : 0 ≤ c2+q*c3 := by linarith
    have hid : c0+c1*q+c2*q^2+c3*q^3 = c0+q*(c1+q*(c2+q*c3)) := by ring
    rw [hid]
    positivity

noncomputable def returnFaceCoeff1 (a T Y : ℝ) : ℝ :=
  2*T*(10*T^3*Y*a+540*T^3-1100*T^2*Y*a-810*T^2
    +888*T*Y^2*a^2+1764*T*Y*a+486*T
    +432*Y^2*a^2+918*Y*a+729)

noncomputable def returnFaceCoeff3 (a T Y : ℝ) : ℝ :=
  -360*T^3*Y*a*(2*T+3)

set_option maxHeartbeats 1000000 in
-- The degree-six interval certificate has large exact rational coefficients.
/-- The initial slope of the return-face cubic is nonnegative. -/
theorem returnFaceCoeff1_nonneg
    (a T Y : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (hY : 0 ≤ Y) :
    0 ≤ returnFaceCoeff1 a T Y := by
  let W := a*Y
  let A := 888*T+432
  let B := 2*(5*T^3-550*T^2+882*T+459)
  let C := mixtureBernsteinC0 T
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 ≤ C := mixtureBernsteinC0_nonneg T hT
  have hcore : returnFaceCoeff1 a T Y = 2*T*(A*W^2+B*W+C) := by
    dsimp [returnFaceCoeff1, W, A, B, C, mixtureBernsteinC0]
    ring
  rw [hcore]
  apply mul_nonneg (mul_nonneg (by norm_num) hT)
  by_cases hB : 0 ≤ B
  · positivity
  · have hBneg : B < 0 := lt_of_not_ge hB
    have hT2 : 2 < T := by
      by_contra hn
      have hTle : T ≤ 2 := le_of_not_gt hn
      have hbern : 0 ≤
          459*(2-T)^3+3*1047*T*(2-T)^2+2705*T^2*(2-T)+63*T^3 := by
        positivity
      have hid : 8*(5*T^3-550*T^2+882*T+459) =
          459*(2-T)^3+3*1047*T*(2-T)^2+2705*T^2*(2-T)+63*T^3 := by ring
      dsimp [B] at hBneg
      nlinarith
    have hT110 : T < 110 := by
      by_contra hn
      have hd : 0 ≤ T-110 := sub_nonneg.mpr (le_of_not_gt hn)
      have hid : 5*T^3-550*T^2+882*T+459 =
          5*(T-110)^3+1100*(T-110)^2+61382*(T-110)+97479 := by ring
      dsimp [B] at hBneg
      rw [hid] at hBneg
      have hbnon : 0 ≤
          5*(T-110)^3+1100*(T-110)^2+61382*(T-110)+97479 := by positivity
      linarith
    let H := 25*T^6-5500*T^5-168200*T^4-479610*T^3
      +191376*T^2-47628*T-104247
    have hcert : 0 ≤
        6136479*(110-T)^6
          +6*201527271*(T-2)*(110-T)^5
          +15*(29811332907/5)*(T-2)^2*(110-T)^4
          +20*(729275954931/5)*(T-2)^3*(110-T)^3
          +15*(12796249099707/5)*(T-2)^4*(110-T)^2
          +6*24130495021383*(T-2)^5*(110-T)
          +69551237603727*(T-2)^6 := by positivity
    have hcertId : 108^6*(-H) =
        6136479*(110-T)^6
          +6*201527271*(T-2)*(110-T)^5
          +15*(29811332907/5)*(T-2)^2*(110-T)^4
          +20*(729275954931/5)*(T-2)^3*(110-T)^3
          +15*(12796249099707/5)*(T-2)^4*(110-T)^2
          +6*24130495021383*(T-2)^5*(110-T)
          +69551237603727*(T-2)^6 := by
      dsimp [H]
      ring
    have hH : H ≤ 0 := by
      rw [← hcertId] at hcert
      norm_num at hcert ⊢
      linarith
    have hdisc : 0 ≤ 4*A*C-B^2 := by
      have hid : 4*A*C-B^2 = -4*H := by
        dsimp [A, B, C, H, mixtureBernsteinC0]
        ring
      rw [hid]
      linarith
    have hid : 4*A*(A*W^2+B*W+C) = (2*A*W+B)^2+(4*A*C-B^2) := by ring
    have hscaled : 0 ≤ 4*A*(A*W^2+B*W+C) := by
      rw [hid]
      positivity
    exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*A)).mp hscaled

set_option maxHeartbeats 1000000 in
-- The endpoint proof uses an exact degree-eight shifted discriminant.
/-- The pure-terminal-mixture endpoint of the return-face numerator is nonnegative. -/
theorem returnFacePoly_at_one_nonneg
    (a T Y : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (hY : 0 ≤ Y) :
    0 ≤ returnFacePoly a T Y 1 := by
  let W := a*Y
  let A := 1308*T^2+864*T+936
  let B := -92*T^4-400*T^3+2880*T^2+1836*T+1404
  let C := (T-3)^2*(20*T^4+120*T^3+324*T^2+216*T+81)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdecomp : returnFacePoly a T Y 1 = 48*W^3+A*W^2+B*W+C := by
    dsimp [returnFacePoly, W, A, B, C]
    ring
  rw [hdecomp]
  by_cases hB : 0 ≤ B
  · positivity
  · have hBneg : B < 0 := lt_of_not_ge hB
    have hT4 : 4 < T := by
      by_contra hn
      have hTle : T ≤ 4 := le_of_not_gt hn
      have hbern : 0 ≤
          1404*(4-T)^4+4*3240*T*(4-T)^3+6*12756*T^2*(4-T)^2
            +4*23552*T^3*(4-T)+5676*T^4 := by positivity
      have hid : 256*B =
          1404*(4-T)^4+4*3240*T*(4-T)^3+6*12756*T^2*(4-T)^2
            +4*23552*T^3*(4-T)+5676*T^4 := by
        dsimp [B]
        ring
      rw [← hid] at hbern
      nlinarith
    let H := 6011*T^8-280*T^7-42832*T^6-93438*T^5-44739*T^4
      +101790*T^3+235224*T^2+176418*T+47385
    have hH : 0 ≤ H := by
      have hid : H =
          6011*(T-4)^8+192072*(T-4)^7+2642256*(T-4)^6
            +20327938*(T-4)^5+94896741*(T-4)^4+271796910*(T-4)^3
            +456255008*(T-4)^2+392576130*(T-4)+117807009 := by
        dsimp [H]
        ring
      rw [hid]
      positivity
    have hdisc : 0 ≤ 4*A*C-B^2 := by
      have hid : 4*A*C-B^2 = 16*H := by
        dsimp [A, B, C, H]
        ring
      rw [hid]
      positivity
    have hid : 4*A*(A*W^2+B*W+C) = (2*A*W+B)^2+(4*A*C-B^2) := by ring
    have hquad : 0 ≤ A*W^2+B*W+C := by
      have hscaled : 0 ≤ 4*A*(A*W^2+B*W+C) := by
        rw [hid]
        positivity
      exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*A)).mp hscaled
    have hcubic : 0 ≤ 48*W^3 := by positivity
    linarith

/-- The full return-face numerator is reduced to its initial slope and terminal endpoint.
These are the two smaller semialgebraic certificates still required in the interior. -/
theorem returnFacePoly_nonneg_of_coeff1_endpoint
    (a T Y q : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (hY : 0 ≤ Y)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hcoeff1 : 0 ≤ returnFaceCoeff1 a T Y)
    (hend : 0 ≤ returnFacePoly a T Y 1) :
    0 ≤ returnFacePoly a T Y q := by
  let c0 := returnFacePoly a T Y 0
  let c1 := returnFaceCoeff1 a T Y
  let c3 := returnFaceCoeff3 a T Y
  let c2 := returnFacePoly a T Y 1-c0-c1-c3
  have hc0 : 0 ≤ c0 := returnFacePoly_at_q_zero_nonneg a T Y ha hY
  have hc1 : 0 ≤ c1 := hcoeff1
  have hc3 : c3 ≤ 0 := by
    have hprod : 0 ≤ 360*T^3*Y*a*(2*T+3) := by positivity
    dsimp [c3, returnFaceCoeff3]
    linarith
  have hpoly : returnFacePoly a T Y q = c0+c1*q+c2*q^2+c3*q^3 := by
    dsimp [c0, c1, c2, c3, returnFacePoly, returnFaceCoeff1, returnFaceCoeff3]
    ring
  rw [hpoly]
  apply cubic_unit_nonneg_of_leading_nonpos c0 c1 c2 c3 q hq0 hq1 hc0 hc1 hc3
  dsimp [c2]
  linarith

/-- The normalized return-face numerator is nonnegative throughout its parameter box. -/
theorem returnFacePoly_nonneg
    (a T Y q : ℝ) (ha0 : 0 ≤ a) (_ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hY : 0 ≤ Y) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ returnFacePoly a T Y q := by
  apply returnFacePoly_nonneg_of_coeff1_endpoint a T Y q ha0 hT hY hq0 hq1
  · exact returnFaceCoeff1_nonneg a T Y ha0 hT hY
  · exact returnFacePoly_at_one_nonneg a T Y ha0 hT hY

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
-- This is the exact expanded normalization of the return-face KKT discriminant.
/-- The return-face KKT discriminant is a positive factor times `returnFacePoly`. -/
theorem returnFace_normalize (a T Y p q : ℝ)
    (hp : p ≠ 0) (hY : Y ≠ 0) (hden : p*Y+a ≠ 0) :
    2*excursionHAA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
        *excursionReducedGap (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -(excursionGradA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9))^2
      = 32*a*(2*T^2*q+3*T*q+2*Y*a+3)*returnFacePoly a T Y q
          /(45*Y^3*p^2) := by
  unfold excursionHAA excursionGradA excursionReducedGap
  unfold excursionHAA
  unfold geomGap geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4 returnFacePoly
  field_simp [hp, hY, hden]
  ring

/-- Once the normalized numerator is nonnegative, the return-face KKT certificate follows
immediately.  This separates the remaining semialgebraic problem from the renewal algebra. -/
theorem returnFace_nonneg_of_poly
    (a T Y p q : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (hY : 0 < Y)
    (hp : 0 < p) (hq : 0 ≤ q) (hpoly : 0 ≤ returnFacePoly a T Y q) :
    0 ≤
      2*excursionHAA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
        *excursionReducedGap (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -(excursionGradA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9))^2 := by
  have hden : p*Y+a ≠ 0 := by positivity
  rw [returnFace_normalize a T Y p q hp.ne' hY.ne' hden]
  positivity

/-- Unconditional return-face KKT certificate in normalized mixture coordinates. -/
theorem returnFace_nonneg
    (a T Y p q : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hY : 0 < Y) (hp : 0 < p)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤
      2*excursionHAA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
        *excursionReducedGap (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -(excursionGradA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9))^2 := by
  apply returnFace_nonneg_of_poly a T Y p q ha0 hT hY hp hq0
  exact returnFacePoly_nonneg a T Y q ha0 ha1 hT hY.le hq0 hq1

/-- The return-face discriminant at the simultaneous sharp third-moment boundary. -/
noncomputable def sharpExcursionFaceA (r x u A v B : ℝ) : ℝ :=
  2*excursionHAA r x u A v B
      *excursionReducedGap r x u A (5*A^2/(4*u)) v B (5*B^2/(4*v))
    -(excursionGradA r x u A (5*A^2/(4*u)) v B (5*B^2/(4*v)))^2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Expanding the definitions verifies the degree-six homogeneity exactly.
/-- Scaling every time variable by `L` scales the sharp return-face discriminant by
`L^6`. -/
theorem sharpExcursionFaceA_scale
    (L r x u A v B : ℝ) (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A ≠ 0) (_hB : B ≠ 0) :
    sharpExcursionFaceA r (L*x) (L*u) (L^2*A) (L*v) (L^2*B)
      = L^6*sharpExcursionFaceA r x u A v B := by
  unfold sharpExcursionFaceA excursionGradA excursionHAA excursionReducedGap
  unfold geomGap geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4
  field_simp [hL, hu, hv, hA, _hB]
  ring

/-- The return-face KKT discriminant is nonnegative for arbitrary admissible second
moments, in the original renewal coordinates. -/
theorem sharpExcursionFaceA_nonneg
    (r x u A v B : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v)
    (hA : 4*u^2 ≤ 3*A) (hB : 4*v^2 ≤ 3*B) :
    0 ≤ sharpExcursionFaceA r x u A v B := by
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBp : 0 < B := by nlinarith [sq_pos_of_pos hv]
  by_cases hr0 : r = 0
  · subst r
    unfold sharpExcursionFaceA excursionGradA excursionHAA excursionReducedGap
    unfold geomGap geomM4 geomM3 geomM2 geomM1
    unfold kernelM1 kernelM2 kernelM3 kernelM4
    field_simp [hu.ne', hv.ne', hAp.ne', hBp.ne']
    ring_nf
    norm_num
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    let p := mixtureWeight u A
    let q := mixtureWeight v B
    let L := r*u+(r+1)*x
    let a := r*u/L
    let Y := u/(p*L)
    let T := v/(q*L)
    obtain ⟨hp, hp1⟩ := mixtureWeight_pos_le_one u A hu hA
    obtain ⟨hq, hq1⟩ := mixtureWeight_pos_le_one v B hv hB
    have hp' : 0 < p := by simpa [p] using hp
    have hq' : 0 < q := by simpa [q] using hq
    have hL : 0 < L := by
      dsimp [L]
      have : 0 < r*u := mul_pos hrp hu
      positivity
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have ha1 : a ≤ 1 := by
      dsimp [a]
      rw [div_le_one hL]
      dsimp [L]
      nlinarith [mul_nonneg (by linarith : 0 ≤ r+1) hx]
    have hY : 0 < Y := by dsimp [Y]; positivity
    have hT : 0 < T := by dsimp [T]; positivity
    have hnorm := returnFace_nonneg a T Y p q ha0 ha1 hT.le hY hp' hq'.le hq1
    have hCnorm : 5*(4*p*Y^2/3)^2/(4*(p*Y)) = 20*p*Y^3/9 := by
      field_simp [hp'.ne', hY.ne']
      ring
    have hDnorm : 5*(4*q*T^2/3)^2/(4*(q*T)) = 20*q*T^3/9 := by
      field_simp [hq'.ne', hT.ne']
      ring
    have hnorm' : 0 ≤ sharpExcursionFaceA (a/(p*Y))
        (p*Y*(1-a)/(p*Y+a)) (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3) := by
      unfold sharpExcursionFaceA
      rw [hCnorm, hDnorm]
      exact hnorm
    have hscale := sharpExcursionFaceA_scale L (a/(p*Y))
      (p*Y*(1-a)/(p*Y+a)) (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
      hL.ne' (by positivity) (by positivity) (by positivity) (by positivity)
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
    have hAid : L^2*(4*p*Y^2/3) = A := by
      dsimp [Y, p, mixtureWeight]
      field_simp [hu.ne', hAp.ne', hL.ne']
    have hBid : L^2*(4*q*T^2/3) = B := by
      dsimp [T, q, mixtureWeight]
      field_simp [hv.ne', hBp.ne', hL.ne']
    have hscaled : 0 ≤ L^6*sharpExcursionFaceA (a/(p*Y))
        (p*Y*(1-a)/(p*Y+a)) (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3) := by
      exact mul_nonneg (by positivity) hnorm'
    rw [← hscale] at hscaled
    rwa [hrid, hxid, huid, hAid, hvid, hBid] at hscaled

/-! ## Compact terminal-face certificates -/

noncomputable def mixtureTerminalGrad (a T Y q : ℝ) : ℝ :=
  -2*T^3*q-54*T^2*q+126*T*Y*a*q-72*T*Y*a+81*T*q-108*T
    +70*Y^2*a+180*Y*a+81

noncomputable def mixtureTerminalSide (a T Y q : ℝ) : ℝ :=
  2*T^3*q^2+2*T^2*Y*q+108*T^2*q^2-52*T^2*q
    -54*T*Y*a*q+108*T*Y*q+135*T*q
    +2*Y^2*a-108*Y*a+108*Y+27

/-- The polynomial controlling the other KKT side condition after the same
normalization.  The sign is reversed: the return-side expression is a negative
positive factor times this polynomial. -/
noncomputable def mixtureReturnSide (a T Y q : ℝ) : ℝ :=
  -2*T^3*q-54*T^2*q+56*T*Y*a*q-2*T*Y*a+81*T*q-108*T
    +110*Y*a+81

/-- The two strict interior KKT inequalities are incompatible.  In polynomial
coordinates, positivity of the return-side polynomial forces nonnegativity of
the terminal-side polynomial. -/
theorem mixtureTerminalSide_nonneg_of_returnSide_pos
    (a T Y q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 ≤ q)
    (hP : 0 < mixtureReturnSide a T Y q) :
    0 ≤ mixtureTerminalSide a T Y q := by
  let z := T*q
  let M := 28*z-T+55
  let K := -2*T^2*z-54*T*z-108*T+81*z+81
  let Lc := 2*T*z+54*z*(2-a)+108*(1-a)
  let S0 := 2*T*z^2-52*T*z+108*z^2+135*z+27
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have ha0 : 0 ≤ a := ha.le
  have h1a : 0 ≤ 1-a := sub_nonneg.mpr ha1
  have h2a : 0 ≤ 2-a := by linarith
  have hPid : mixtureReturnSide a T Y q = 2*a*Y*M+K := by
    unfold mixtureReturnSide
    dsimp [z, M, K]
    ring
  have hSid : mixtureTerminalSide a T Y q = 2*a*Y^2+Lc*Y+S0 := by
    unfold mixtureTerminalSide
    dsimp [z, Lc, S0]
    ring
  have hLc : 0 ≤ Lc := by
    have hid : Lc = 2*T*z+54*z*(2-a)+108*(1-a) := by rfl
    rw [hid]
    positivity
  by_cases hK : 0 ≤ K
  · have hdrop : 0 ≤ 2*T^2*z+54*T*z := by positivity
    have hTbound : 108*T ≤ 81*(z+1) := by
      dsimp [K] at hK
      nlinarith
    have hTz := mul_le_mul_of_nonneg_right hTbound hz
    have hS0 : 0 ≤ S0 := by
      dsimp [S0]
      nlinarith [sq_nonneg z]
    rw [hSid]
    positivity
  · have hKneg : K < 0 := lt_of_not_ge hK
    have hM : 0 < M := by
      rw [hPid] at hP
      by_contra hn
      have hMnonpos : M ≤ 0 := le_of_not_gt hn
      have hprod : 2*a*Y*M ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hMnonpos
      linarith
    let J0 := T^2*z+28*T*z^2+55*T*z+54*T+1512*z^2+4401*z+2889
    let J1 := -K+z*(T+27)*M
    let J := (1-a)*J0+a*J1
    let N0 := -K
    let N1 := (z+1)*(2*(T-1)^2+56*z+27)
    let N := (1-a)*N0+a*N1
    let H := 8*T*z+432*z+837
    have hJ0 : 0 ≤ J0 := by dsimp [J0]; positivity
    have hJ1 : 0 ≤ J1 := by
      dsimp [J1]
      have hnK : 0 ≤ -K := by linarith
      have hzTM : 0 ≤ z*(T+27)*M := by positivity
      linarith
    have hJ : 0 ≤ J := by dsimp [J]; positivity
    have hN0 : 0 ≤ N0 := by dsimp [N0]; linarith
    have hN1 : 0 ≤ N1 := by dsimp [N1]; positivity
    have hN : 0 ≤ N := by dsimp [N]; positivity
    have hH : 0 ≤ H := by dsimp [H]; positivity
    have hid :
        (2*a*M)^2*mixtureTerminalSide a T Y q =
          2*a*(mixtureReturnSide a T Y q)^2
            +4*a*J*mixtureReturnSide a T Y q
            +14*a*(z+1)*H*N := by
      unfold mixtureTerminalSide mixtureReturnSide
      dsimp [z, M, K, Lc, S0, J0, J1, J, N0, N1, N, H]
      ring
    have hscaled : 0 ≤ (2*a*M)^2*mixtureTerminalSide a T Y q := by
      rw [hid]
      positivity
    exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos (by positivity : 0 < 2*a*M))).mp
      hscaled

noncomputable def mixtureTerminalFace (a T Y q : ℝ) : ℝ :=
  48*T^4*Y*a*q^2-396*T^4*q^2+40*T^3*Y^2*a*q^2
    +720*T^3*Y*a*q^2-108*T^3*q^2+20*T^2*Y^3*a*q
    -2268*T^2*Y^2*a^2*q^2+1776*T^2*Y^2*a^2*q
    +2160*T^2*Y^2*a*q^2-1040*T^2*Y^2*a*q
    +972*T^2*Y*a*q^2+648*T^2*Y*a*q+729*T^2*q^2-108*T^2*q
    -1080*T*Y^3*a^2*q+1080*T*Y^3*a*q
    -1296*T*Y^2*a^2*q+2700*T*Y^2*a*q+2916*T*Y*a*q+1458*T*q
    +20*Y^4*a^2+1728*Y^3*a^3-2160*Y^3*a^2+1080*Y^3*a
    +1296*Y^2*a^2+540*Y^2*a+1944*Y*a+729

/-! The terminal-face polynomial is already nonnegative in the region `T ≤ 1`.
The following small Bernstein forms keep the certificate reasonably compact. -/

noncomputable def bern1 (c0 c1 t : ℝ) : ℝ :=
  c0*(1-t)+c1*t

noncomputable def bern2 (c0 c1 c2 t : ℝ) : ℝ :=
  c0*(1-t)^2+2*c1*t*(1-t)+c2*t^2

noncomputable def bern3 (c0 c1 c2 c3 t : ℝ) : ℝ :=
  c0*(1-t)^3+3*c1*t*(1-t)^2+3*c2*t^2*(1-t)+c3*t^3

noncomputable def bern5 (c0 c1 c2 c3 c4 c5 t : ℝ) : ℝ :=
  c0*(1-t)^5+5*c1*t*(1-t)^4+10*c2*t^2*(1-t)^3
    +10*c3*t^3*(1-t)^2+5*c4*t^4*(1-t)+c5*t^5

theorem bern1_nonneg (c0 c1 t : ℝ)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ bern1 c0 c1 t := by
  unfold bern1
  positivity

theorem bern2_nonneg (c0 c1 c2 t : ℝ)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ bern2 c0 c1 c2 t := by
  unfold bern2
  positivity

/-- Restricting a quadratic Bernstein polynomial to an initial subinterval preserves
nonnegativity when its first two original coefficients and its new endpoint are
nonnegative. -/
theorem bern2_initial_segment_nonneg
    (c0 c1 c2 q r : ℝ) (hq0 : 0 ≤ q) (hqr : q ≤ r) (hr1 : r ≤ 1)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hend : 0 ≤ bern2 c0 c1 c2 r) :
    0 ≤ bern2 c0 c1 c2 q := by
  have hr0 : 0 ≤ r := le_trans hq0 hqr
  by_cases hr : r = 0
  · have hq : q = 0 := by linarith
    subst q
    simp [bern2, hc0]
  · have hrp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hmid : 0 ≤ (1-r)*c0+r*c1 := by positivity
    have hid : r^2*bern2 c0 c1 c2 q =
        c0*(r-q)^2+2*((1-r)*c0+r*c1)*q*(r-q)
          +bern2 c0 c1 c2 r*q^2 := by
      unfold bern2
      ring
    have hscaled : 0 ≤ r^2*bern2 c0 c1 c2 q := by
      rw [hid]
      positivity
    exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos hrp)).mp hscaled

/-- The corresponding restriction certificate for a final subinterval. -/
theorem bern2_final_segment_nonneg
    (c0 c1 c2 q r : ℝ) (hr0 : 0 ≤ r) (hrq : r ≤ q) (hq1 : q ≤ 1)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hstart : 0 ≤ bern2 c0 c1 c2 r) :
    0 ≤ bern2 c0 c1 c2 q := by
  have hr1 : r ≤ 1 := le_trans hrq hq1
  by_cases hr : r = 1
  · have hq : q = 1 := by linarith
    subst q
    simp [bern2, hc2]
  · have hrp : 0 < 1-r := sub_pos.mpr (lt_of_le_of_ne hr1 hr)
    have hmid : 0 ≤ (1-r)*c1+r*c2 := by positivity
    have hid : (1-r)^2*bern2 c0 c1 c2 q =
        bern2 c0 c1 c2 r*(1-q)^2
          +2*((1-r)*c1+r*c2)*(q-r)*(1-q)+c2*(q-r)^2 := by
      unfold bern2
      ring
    have hscaled : 0 ≤ (1-r)^2*bern2 c0 c1 c2 q := by
      rw [hid]
      positivity
    exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos hrp)).mp hscaled

theorem bern3_nonneg (c0 c1 c2 c3 t : ℝ)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ bern3 c0 c1 c2 c3 t := by
  unfold bern3
  positivity

theorem bern5_nonneg (c0 c1 c2 c3 c4 c5 t : ℝ)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hc4 : 0 ≤ c4) (hc5 : 0 ≤ c5) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ bern5 c0 c1 c2 c3 c4 c5 t := by
  unfold bern5
  positivity

theorem bern4_nonneg' (c0 c1 c2 c3 c4 t : ℝ)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hc4 : 0 ≤ c4) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ bern4 c0 c1 c2 c3 c4 t := by
  unfold bern4
  positivity

noncomputable def terminalSmallY0 (T q : ℝ) : ℝ :=
  bern4
    (bern2 729 729 729 q)
    (bern2 729 (3645/4) (2187/2) q)
    (bern2 729 (2169/2) (3123/2) q)
    (bern2 729 (4995/4) 2106 q)
    (bern2 729 1404 2304 q) T

noncomputable def terminalSmallY1 (a T q : ℝ) : ℝ :=
  bern4
    (bern1 (bern2 0 0 0 q) (bern2 1944 1944 1944 q) a)
    (bern1 (bern2 0 0 0 q) (bern2 1944 (4617/2) 2673 q) a)
    (bern1 (bern2 0 0 0 q) (bern2 1944 2727 3672 q) a)
    (bern1 (bern2 0 0 0 q) (bern2 1944 (6399/2) 5121 q) a)
    (bern1 (bern2 0 0 0 q) (bern2 1944 3726 7248 q) a) T

noncomputable def terminalSmallY2 (a T q : ℝ) : ℝ :=
  bern3
    (bern2 (bern2 0 0 0 q) (bern2 270 270 270 q) (bern2 1836 1836 1836 q) a)
    (bern2 (bern2 0 0 0 q) (bern2 270 495 720 q) (bern2 1836 2070 2304 q) a)
    (bern2 (bern2 0 0 0 q) (bern2 270 (1900/3) (4070/3) q)
      (bern2 1836 (7280/3) (8944/3) q) a)
    (bern2 (bern2 0 0 0 q) (bern2 270 685 2200 q) (bern2 1836 2906 3908 q) a) T

noncomputable def terminalSmallY3 (a T q : ℝ) : ℝ :=
  bern2
    (bern3 (bern1 0 0 q) (bern1 360 360 q) (bern1 0 0 q) (bern1 648 648 q) a)
    (bern3 (bern1 0 0 q) (bern1 360 540 q) (bern1 0 180 q) (bern1 648 648 q) a)
    (bern3 (bern1 0 0 q) (bern1 360 (2180/3) q) (bern1 0 (1120/3) q)
      (bern1 648 668 q) a) T

noncomputable def terminalSmallY4 (a : ℝ) : ℝ :=
  bern2 0 0 20 a

/-- The zero terminal-mixture endpoint is positive for every nonnegative `a,Y`. -/
theorem mixtureTerminalFace_at_q_zero_nonneg
    (a T Y : ℝ) (ha : 0 ≤ a) (hY : 0 ≤ Y) :
    0 ≤ mixtureTerminalFace a T Y 0 := by
  have hquad : 0 ≤ 8*a^2-10*a+5 := by
    nlinarith [sq_nonneg (8*a-5)]
  have hid : mixtureTerminalFace a T Y 0 =
      20*Y^4*a^2+216*a*Y^3*(8*a^2-10*a+5)
        +Y^2*(1296*a^2+540*a)+1944*Y*a+729 := by
    unfold mixtureTerminalFace
    ring
  rw [hid]
  positivity

/-! A second Bernstein reduction, now in the terminal mixture weight `q`. -/

noncomputable def mixtureTerminalGrad0 (a T Y : ℝ) : ℝ :=
  mixtureTerminalGrad a T Y 0

/-- The middle Bernstein coefficient of `q ↦ mixtureTerminalFace a T Y q`. -/
noncomputable def mixtureTerminalMid (a T Y : ℝ) : ℝ :=
  20*Y^4*a^2+1728*Y^3*a^3-2160*Y^3*a^2+1080*Y^3*a
    +1296*Y^2*a^2+540*Y^2*a+1944*Y*a+729
    +T*(10*T*Y^3*a+888*T*Y^2*a^2-520*T*Y^2*a+324*T*Y*a-54*T
      -540*Y^3*a^2+540*Y^3*a-648*Y^2*a^2+1350*Y^2*a+1458*Y*a+729)

noncomputable def terminalMidMultiplier (a T Y : ℝ) : ℝ :=
  (982/251)*Y*a^2+(19/9)*Y*(T-1)*a*(1-a)+(65/9)*Y*(T-1)*(1-a)^2
    +(505/72)*Y*(1-a)^2+(215821/8785)*a^2*(T-1)+(8905/251)*a^2
    +(152/7)*(T-1)*a*(1-a)+(2138/35)*a*(1-a)
    +(1/2)*(T-1)*(1-a)^2+(35/4)*(1-a)^2

noncomputable def terminalMidRemainder (a T Y : ℝ) : ℝ :=
  (6561/4)*(1-a)^3+(284553/140)*3*a*(1-a)^2
    +(19968957/8785)*3*a^2*(1-a)+(592839/251)*a^3
    +(1515/8)*Y*(1-a)^3+(7921/8)*Y*3*a*(1-a)^2
    +(2812302/8785)*Y*3*a^2*(1-a)
    +(41005/108)*Y^3*3*a*(1-a)^2+(560/3)*Y^3*3*a^2*(1-a)
    +(96418/251)*Y^3*a^3+(20/3)*Y^4*3*a^2*(1-a)+20*Y^4*a^3
    +(3159/2)*(T-1)*(1-a)^3+(233451/70)*(T-1)*3*a*(1-a)^2
    +(39653982/8785)*(T-1)*3*a^2*(1-a)+(44943552/8785)*(T-1)*a^3
    +(1905/2)*(T-1)*Y*(1-a)^3+(2461/2)*(T-1)*Y*3*a*(1-a)^2
    +(19750327/8785)*(T-1)*Y*3*a^2*(1-a)
    +(21345102/8785)*(T-1)*Y*a^3
    +(490/27)*(T-1)*Y^3*3*a*(1-a)^2
    +(3890/27)*(T-1)*Y^3*3*a^2*(1-a)+20*(T-1)*Y^3*a^3
    +(5220/7)*(T-1)^2*3*a*(1-a)^2
    +(2023218/1255)*(T-1)^2*3*a^2*(1-a)
    +(22834278/8785)*(T-1)^2*a^3+780*(T-1)^2*Y*(1-a)^3
    +456*(T-1)^2*Y*3*a*(1-a)^2
    +(5692/7)*(T-1)^2*Y*3*a^2*(1-a)
    +(18385452/8785)*(T-1)^2*Y*a^3+368*(T-1)^2*Y^2*a^3
    +(10/3)*(T-1)^2*Y^3*3*a*(1-a)^2
    +(20/3)*(T-1)^2*Y^3*3*a^2*(1-a)+10*(T-1)^2*Y^3*a^3

/-- The factor left after removing the positive `T` from the slope of
`q ↦ mixtureTerminalGrad a T Y q`. -/
noncomputable def terminalGradSlopeCore (a T Y : ℝ) : ℝ :=
  -2*T^2-54*T+126*Y*a+81

/-- Half the linear power-basis coefficient of the terminal-face quadratic. -/
noncomputable def terminalFaceLinearCore (a T Y : ℝ) : ℝ :=
  10*T*Y^3*a+888*T*Y^2*a^2-520*T*Y^2*a+324*T*Y*a-54*T
    -540*Y^3*a^2+540*Y^3*a-648*Y^2*a^2+1350*Y^2*a+1458*Y*a+729

noncomputable def terminalSlopeMultiplier (a Y : ℝ) : ℝ :=
  99/7+(65/29)*Y^2*4*a*(1-a)^3+(56/29)*Y^2*6*a^2*(1-a)^2

noncomputable def terminalSlopeRemainder (a T Y : ℝ) : ℝ :=
  bern5 (2250/7) (2250/7) (2250/7) (2250/7) (2250/7) (2250/7) a
    +Y^2*bern5 0 (3514/29) (8834/29) (15690/29) 808 1070 a
    +Y^3*bern5 0 110 (1538/29) (3192/145) 116 10 a
    +(T-1)*bern5 (5364/7) (5364/7) (5364/7) (5364/7) (5364/7) (5364/7) a
    +(T-1)*Y*bern5 0 (324/5) (648/5) (972/5) (1296/5) 324 a
    +(T-1)*Y^2*bern5 0 0 0 (108/5) (584/5) 368 a
    +(T-1)*Y^3*bern5 0 2 4 6 8 10 a
    +(T-1)^2*bern5 (198/7) (198/7) (198/7) (198/7) (198/7) (198/7) a
    +(T-1)^2*Y^2*bern5 0 (104/29) (596/145) (336/145) 0 0 a

set_option maxHeartbeats 1000000 in
/-- A positive slope of the terminal gradient forces the linear coefficient of the
face quadratic to be nonnegative. -/
theorem terminalFaceLinearCore_nonneg_of_gradSlopeCore_nonneg
    (a T Y : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hT1 : 1 ≤ T) (hY : 0 ≤ Y) (hG : 0 ≤ terminalGradSlopeCore a T Y) :
    0 ≤ terminalFaceLinearCore a T Y := by
  have hM : 0 ≤ terminalSlopeMultiplier a Y := by
    unfold terminalSlopeMultiplier
    positivity
  have h0 : 0 ≤ bern5 (2250/7) (2250/7) (2250/7) (2250/7) (2250/7) (2250/7) a := by
    apply bern5_nonneg <;> norm_num <;> assumption
  have h1 : 0 ≤ bern5 0 (3514/29) (8834/29) (15690/29) 808 1070 a := by
    apply bern5_nonneg <;> norm_num <;> assumption
  have h2 : 0 ≤ bern5 0 110 (1538/29) (3192/145) 116 10 a := by
    apply bern5_nonneg <;> norm_num <;> assumption
  have h3 : 0 ≤ bern5 (5364/7) (5364/7) (5364/7) (5364/7) (5364/7) (5364/7) a := by
    apply bern5_nonneg <;> norm_num <;> assumption
  have h4 : 0 ≤ bern5 0 (324/5) (648/5) (972/5) (1296/5) 324 a := by
    apply bern5_nonneg <;> norm_num <;> assumption
  have h5 : 0 ≤ bern5 0 0 0 (108/5) (584/5) 368 a := by
    apply bern5_nonneg <;> norm_num <;> assumption
  have h6 : 0 ≤ bern5 0 2 4 6 8 10 a := by
    apply bern5_nonneg <;> norm_num <;> assumption
  have h7 : 0 ≤ bern5 (198/7) (198/7) (198/7) (198/7) (198/7) (198/7) a := by
    apply bern5_nonneg <;> norm_num <;> assumption
  have h8 : 0 ≤ bern5 0 (104/29) (596/145) (336/145) 0 0 a := by
    apply bern5_nonneg <;> norm_num <;> assumption
  have hQ : 0 ≤ terminalSlopeRemainder a T Y := by
    unfold terminalSlopeRemainder
    positivity
  have hid : terminalFaceLinearCore a T Y =
      terminalSlopeMultiplier a Y*terminalGradSlopeCore a T Y
        +terminalSlopeRemainder a T Y := by
    unfold terminalFaceLinearCore terminalSlopeMultiplier terminalGradSlopeCore
    unfold terminalSlopeRemainder bern5
    ring
  rw [hid]
  positivity

set_option maxHeartbeats 1000000 in
/-- If `T ≥ 1` and the terminal derivative numerator is nonnegative at `q=0`,
then the middle Bernstein coefficient in `q` is nonnegative. -/
theorem mixtureTerminalMid_nonneg_of_grad0_nonneg
    (a T Y : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hT1 : 1 ≤ T) (hY : 0 ≤ Y) (hG0 : 0 ≤ mixtureTerminalGrad0 a T Y) :
    0 ≤ mixtureTerminalMid a T Y := by
  have hM : 0 ≤ terminalMidMultiplier a T Y := by
    unfold terminalMidMultiplier
    positivity
  have hQ : 0 ≤ terminalMidRemainder a T Y := by
    unfold terminalMidRemainder
    positivity
  have hid : mixtureTerminalMid a T Y =
      terminalMidMultiplier a T Y*mixtureTerminalGrad0 a T Y
        +terminalMidRemainder a T Y := by
    unfold mixtureTerminalMid terminalMidMultiplier terminalMidRemainder
    unfold mixtureTerminalGrad0 mixtureTerminalGrad
    ring
  rw [hid]
  positivity

theorem mixtureTerminalFace_bernstein_q (a T Y q : ℝ) :
    mixtureTerminalFace a T Y q =
      mixtureTerminalFace a T Y 0*(1-q)^2
        +2*mixtureTerminalMid a T Y*q*(1-q)
        +mixtureTerminalFace a T Y 1*q^2 := by
  unfold mixtureTerminalFace mixtureTerminalMid
  ring

theorem mixtureTerminalGrad_bernstein_q (a T Y q : ℝ) :
    mixtureTerminalGrad a T Y q =
      (1-q)*mixtureTerminalGrad a T Y 0+q*mixtureTerminalGrad a T Y 1 := by
  unfold mixtureTerminalGrad
  ring

theorem mixtureTerminalGrad_endpoint_difference (a T Y : ℝ) :
    mixtureTerminalGrad a T Y 1-mixtureTerminalGrad a T Y 0 =
      T*terminalGradSlopeCore a T Y := by
  unfold mixtureTerminalGrad terminalGradSlopeCore
  ring

theorem mixtureTerminalMid_eq_linearCore (a T Y : ℝ) :
    mixtureTerminalMid a T Y =
      mixtureTerminalFace a T Y 0+T*terminalFaceLinearCore a T Y := by
  unfold mixtureTerminalMid mixtureTerminalFace terminalFaceLinearCore
  ring

/-- A positive gradient numerator at an interior mixture weight forces positivity at
at least one endpoint, since the numerator is affine in `q`. -/
theorem mixtureTerminalGrad_endpoint_dichotomy
    (a T Y q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hG : 0 < mixtureTerminalGrad a T Y q) :
    0 < mixtureTerminalGrad a T Y 0 ∨ 0 < mixtureTerminalGrad a T Y 1 := by
  rw [mixtureTerminalGrad_bernstein_q] at hG
  by_contra hn
  push Not at hn
  have hleft : (1-q)*mixtureTerminalGrad a T Y 0 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq1) hn.1
  have hright : q*mixtureTerminalGrad a T Y 1 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hq0 hn.2
  linarith

set_option maxHeartbeats 1000000 in
/-- On `0 ≤ T ≤ 1`, every coefficient in powers of `Y` has a nonnegative
multivariate Bernstein expansion in `a`, `T`, and `q`. -/
theorem mixtureTerminalFace_small_nonneg
    (a T Y q : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (hY : 0 ≤ Y)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ mixtureTerminalFace a T Y q := by
  have h0 : 0 ≤ terminalSmallY0 T q := by
    unfold terminalSmallY0 bern4 bern2
    positivity
  have h1 : 0 ≤ terminalSmallY1 a T q := by
    unfold terminalSmallY1 bern4 bern1 bern2
    positivity
  have h2 : 0 ≤ terminalSmallY2 a T q := by
    unfold terminalSmallY2 bern3 bern2
    positivity
  have h3 : 0 ≤ terminalSmallY3 a T q := by
    unfold terminalSmallY3 bern3 bern2 bern1
    positivity
  have h4 : 0 ≤ terminalSmallY4 a := by
    unfold terminalSmallY4
    apply bern2_nonneg <;> norm_num <;> assumption
  have hid : mixtureTerminalFace a T Y q =
      terminalSmallY0 T q+Y*terminalSmallY1 a T q+Y^2*terminalSmallY2 a T q
        +Y^3*terminalSmallY3 a T q+Y^4*terminalSmallY4 a := by
    unfold mixtureTerminalFace terminalSmallY0 terminalSmallY1 terminalSmallY2
    unfold terminalSmallY3 terminalSmallY4 bern1 bern2 bern3 bern4
    ring
  rw [hid]
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- At the pure terminal mixture endpoint `q = 1`, positivity follows from the
already-proved deepest-corner terminal certificate.  The change of coordinates is
`b=1/(Y+1)`, `R=(1-a)/(Y+1)`, and `z=T/(Y+1)`. -/
theorem mixtureTerminalFace_at_one_nonneg
    (a T Y : ℝ) (ha0 : 0 ≤ a) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hG : 0 < mixtureTerminalGrad a T Y 1) :
    0 ≤ mixtureTerminalFace a T Y 1 := by
  by_cases hT1 : T ≤ 1
  · exact mixtureTerminalFace_small_nonneg a T Y 1 ha0 ha1 hT.le hT1 hY.le
      (by norm_num) (by norm_num)
  · have hTone : 1 < T := lt_of_not_ge hT1
    let b := 1/(Y+1)
    let R := (1-a)/(Y+1)
    let z := T/(Y+1)
    have hden : 0 < Y+1 := by positivity
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have hRb : R < b := by
      dsimp [R, b]
      rw [div_lt_div_iff_of_pos_right hden]
      linarith
    have hb1 : b ≤ 1 := by
      dsimp [b]
      rw [div_le_one hden]
      linarith
    have hz : 0 ≤ z := by dsimp [z]; positivity
    have hbz : b ≤ z := by
      dsimp [b, z]
      rw [div_le_div_iff_of_pos_right hden]
      linarith
    have hgradId : terminalGradPoly R b z =
        -mixtureTerminalGrad a T Y 1/(Y+1)^3 := by
      dsimp [R, b, z]
      unfold terminalGradPoly mixtureTerminalGrad
      field_simp [hden.ne']
      ring
    have hgrad : terminalGradPoly R b z < 0 := by
      rw [hgradId]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos hG) (pow_pos hden 3)
    have hface := terminalFacePoly_large_nonneg R b z hR hRb hb1 hz hbz hgrad
    have hfaceId : (Y+1)^9*terminalFacePoly R b z =
        mixtureTerminalFace a T Y 1 := by
      dsimp [R, b, z]
      unfold terminalFacePoly faceCoeff0 faceCoeff1 faceCoeff2 faceCoeff3
      unfold mixtureTerminalFace
      field_simp [hden.ne']
      ring
    rw [← hfaceId]
    positivity

/-- If the terminal gradient increases between `q=0` and `q=1` and is positive at
the latter endpoint, the face quadratic has nonnegative constant, linear, and endpoint
Bernstein data. -/
theorem mixtureTerminalFace_nonneg_of_grad_upcrossing
    (a T Y q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT1 : 1 ≤ T) (hY : 0 < Y) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hslope : mixtureTerminalGrad a T Y 0 < mixtureTerminalGrad a T Y 1)
    (hG1 : 0 < mixtureTerminalGrad a T Y 1) :
    0 ≤ mixtureTerminalFace a T Y q := by
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) hT1
  have hslopeCore : 0 < terminalGradSlopeCore a T Y := by
    have hid := mixtureTerminalGrad_endpoint_difference a T Y
    have hprod : 0 < T*terminalGradSlopeCore a T Y := by linarith
    by_contra hn
    have hnonpos : terminalGradSlopeCore a T Y ≤ 0 := le_of_not_gt hn
    have := mul_nonpos_of_nonneg_of_nonpos hT.le hnonpos
    linarith
  have hlinear := terminalFaceLinearCore_nonneg_of_gradSlopeCore_nonneg
    a T Y ha.le ha1 hT1 hY.le hslopeCore.le
  have h0 := mixtureTerminalFace_at_q_zero_nonneg a T Y ha.le hY.le
  have hm : 0 ≤ mixtureTerminalMid a T Y := by
    rw [mixtureTerminalMid_eq_linearCore]
    positivity
  have h1 := mixtureTerminalFace_at_one_nonneg a T Y ha.le ha ha1 hT hY hG1
  rw [mixtureTerminalFace_bernstein_q]
  positivity

/-- If the terminal gradient is positive at both mixture endpoints, the entire
quadratic terminal-face numerator is nonnegative. -/
theorem mixtureTerminalFace_nonneg_of_endpoint_grads
    (a T Y q : ℝ) (ha0 : 0 ≤ a) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT1 : 1 ≤ T) (hY : 0 < Y) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hG0 : 0 ≤ mixtureTerminalGrad a T Y 0)
    (hG1 : 0 < mixtureTerminalGrad a T Y 1) :
    0 ≤ mixtureTerminalFace a T Y q := by
  have h0 := mixtureTerminalFace_at_q_zero_nonneg a T Y ha0 hY.le
  have hm := mixtureTerminalMid_nonneg_of_grad0_nonneg a T Y ha0 ha1 hT1 hY.le hG0
  have h1 := mixtureTerminalFace_at_one_nonneg a T Y ha0 ha ha1
    (lt_of_lt_of_le (by norm_num) hT1) hY hG1
  rw [mixtureTerminalFace_bernstein_q]
  positivity

/-- Once a nonnegative point on the gradient-zero boundary is supplied, the whole
initial `q`-segment is controlled by the positive middle Bernstein coefficient. -/
theorem mixtureTerminalFace_initial_segment_nonneg
    (a T Y q qstar : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hT1 : 1 ≤ T) (hY : 0 ≤ Y)
    (hq0 : 0 ≤ q) (hqqstar : q ≤ qstar) (hqstar1 : qstar ≤ 1)
    (hG0 : 0 ≤ mixtureTerminalGrad a T Y 0)
    (hboundary : 0 ≤ mixtureTerminalFace a T Y qstar) :
    0 ≤ mixtureTerminalFace a T Y q := by
  have h0 := mixtureTerminalFace_at_q_zero_nonneg a T Y ha0 hY
  have hm := mixtureTerminalMid_nonneg_of_grad0_nonneg a T Y ha0 ha1 hT1 hY hG0
  rw [mixtureTerminalFace_bernstein_q]
  apply bern2_initial_segment_nonneg _ _ _ q qstar hq0 hqqstar hqstar1 h0 hm
  rw [mixtureTerminalFace_bernstein_q] at hboundary
  exact hboundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- These three identities expand the sharp excursion moments in normalized coordinates.
theorem terminalGrad_normalize (a T Y p q : ℝ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hden : p*Y+a ≠ 0) :
    excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
        (q*T) (4*q*T^2/3) (20*q*T^3/9)
      = -(4/9)*mixtureTerminalGrad a T Y q := by
  unfold excursionGradB excursionHBB excursionReducedGap
  unfold geomGap geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4 mixtureTerminalGrad
  field_simp [hp, hq, hT, hY, hden]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Exact normalization of the terminal KKT side condition.
theorem terminalSide_normalize (a T Y p q : ℝ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hden : p*Y+a ≠ 0) :
    excursionHBB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
      *excursionGradA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
        (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -excursionHAB (a/(p*Y))
        *excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      = 16*a*(2*T^2*q+3*T*q+2*Y*a+3)*mixtureTerminalSide a T Y q
          /(5*T^2*Y*p*q) := by
  unfold excursionHBB excursionHAB excursionGradA excursionGradB excursionReducedGap
  unfold excursionHAA excursionHBB
  unfold geomGap geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4 mixtureTerminalSide
  field_simp [hp, hq, hT, hY, hden]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Exact normalization of the return KKT side condition. -/
theorem returnSide_normalize (a T Y p q : ℝ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hden : p*Y+a ≠ 0) :
    excursionHAA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
      *excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
        (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -excursionHAB (a/(p*Y))
        *excursionGradA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      = -16*a*(2*T^2*q+3*T*q+2*Y*a+3)*mixtureReturnSide a T Y q
          /(5*Y^3*p^2) := by
  unfold excursionHAA excursionHAB excursionGradA excursionGradB excursionReducedGap
  unfold excursionHAA excursionHBB
  unfold geomGap geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4 mixtureReturnSide
  field_simp [hp, hq, hT, hY, hden]
  ring

/-- In normalized coordinates the two strict KKT side inequalities cannot hold
simultaneously, so there is no interior stationary candidate. -/
theorem terminalInterior_impossible
    (a T Y p q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hp : 0 < p) (hq : 0 < q) :
    excursionHAA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
        *excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -excursionHAB (a/(p*Y))
        *excursionGradA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9) < 0 →
    excursionHBB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
        *excursionGradA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -excursionHAB (a/(p*Y))
        *excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9) < 0 → False := by
  intro hsideA hsideB
  have hden : p*Y+a ≠ 0 := by positivity
  have hAid := returnSide_normalize a T Y p q hp.ne' hq.ne' hT.ne' hY.ne' hden
  have hBid := terminalSide_normalize a T Y p q hp.ne' hq.ne' hT.ne' hY.ne' hden
  let fA := 16*a*(2*T^2*q+3*T*q+2*Y*a+3)/(5*Y^3*p^2)
  let fB := 16*a*(2*T^2*q+3*T*q+2*Y*a+3)/(5*T^2*Y*p*q)
  have hfA : 0 < fA := by dsimp [fA]; positivity
  have hfB : 0 < fB := by dsimp [fB]; positivity
  have hAeq :
      -16*a*(2*T^2*q+3*T*q+2*Y*a+3)*mixtureReturnSide a T Y q
          /(5*Y^3*p^2) = -fA*mixtureReturnSide a T Y q := by
    dsimp [fA]
    ring
  have hBeq :
      16*a*(2*T^2*q+3*T*q+2*Y*a+3)*mixtureTerminalSide a T Y q
          /(5*T^2*Y*p*q) = fB*mixtureTerminalSide a T Y q := by
    dsimp [fB]
    ring
  rw [hAid, hAeq] at hsideA
  rw [hBid, hBeq] at hsideB
  have hPmul : 0 < fA*mixtureReturnSide a T Y q := by linarith
  have hP : 0 < mixtureReturnSide a T Y q :=
    (mul_pos_iff_of_pos_left hfA).mp hPmul
  have hS : 0 ≤ mixtureTerminalSide a T Y q :=
    mixtureTerminalSide_nonneg_of_returnSide_pos a T Y q ha ha1 hT hY hq.le hP
  have hSneg : mixtureTerminalSide a T Y q < 0 :=
    neg_of_mul_neg_right hsideB hfB.le
  exact (not_lt_of_ge hS) hSneg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
-- Exact normalization of the terminal-face discriminant.
theorem terminalFace_normalize (a T Y p q : ℝ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hden : p*Y+a ≠ 0) :
    2*excursionHBB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
        *excursionReducedGap (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -(excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9))^2
      = 32*(2*T^2*q+3*T*q+2*Y*a+3)*mixtureTerminalFace a T Y q
          /(45*T^2*q) := by
  unfold excursionHBB excursionGradB excursionReducedGap
  unfold excursionHBB
  unfold geomGap geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4 mixtureTerminalFace
  field_simp [hp, hq, hT, hY, hden]
  ring

/-- The terminal-face KKT problem in normalized coordinates is exactly the polynomial
implication `Grad > 0 → Side ≥ 0 → Face ≥ 0`. -/
theorem terminalFace_nonneg_of_polynomial_implication
    (a T Y p q : ℝ) (ha : 0 < a) (hT : 0 < T) (hY : 0 < Y)
    (hp : 0 < p) (hq : 0 < q)
    (hpoly : 0 < mixtureTerminalGrad a T Y q →
      0 ≤ mixtureTerminalSide a T Y q →
      0 ≤ mixtureTerminalFace a T Y q) :
    excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
        (q*T) (4*q*T^2/3) (20*q*T^3/9) < 0 →
    0 ≤ excursionHBB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
        *excursionGradA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -excursionHAB (a/(p*Y))
        *excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9) →
    0 ≤ 2*excursionHBB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
        *excursionReducedGap (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -(excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9))^2 := by
  intro hgrad hside
  have hden : p*Y+a ≠ 0 := by positivity
  have hgradId := terminalGrad_normalize a T Y p q hp.ne' hq.ne' hT.ne' hY.ne' hden
  have hG : 0 < mixtureTerminalGrad a T Y q := by linarith
  have hsideId := terminalSide_normalize a T Y p q hp.ne' hq.ne' hT.ne' hY.ne' hden
  let sideFactor := 16*a*(2*T^2*q+3*T*q+2*Y*a+3)/(5*T^2*Y*p*q)
  have hsideFactor : 0 < sideFactor := by dsimp [sideFactor]; positivity
  have hsideEq :
      16*a*(2*T^2*q+3*T*q+2*Y*a+3)*mixtureTerminalSide a T Y q
          /(5*T^2*Y*p*q) = sideFactor*mixtureTerminalSide a T Y q := by
    dsimp [sideFactor]
    ring
  rw [hsideEq] at hsideId
  have hS : 0 ≤ mixtureTerminalSide a T Y q := by
    apply (mul_nonneg_iff_of_pos_left hsideFactor).mp
    rw [← hsideId]
    exact hside
  have hF := hpoly hG hS
  have hfaceId := terminalFace_normalize a T Y p q hp.ne' hq.ne' hT.ne' hY.ne' hden
  rw [hfaceId]
  positivity

/-- The normalized terminal-face KKT certificate in the region `T ≤ 1`.  In this
region the discriminant polynomial is nonnegative independently of the two KKT
hypotheses. -/
theorem terminalFace_small_nonneg
    (a T Y p q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (hY : 0 < Y)
    (hp : 0 < p) (hq : 0 < q) (hq1 : q ≤ 1) :
    excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
        (q*T) (4*q*T^2/3) (20*q*T^3/9) < 0 →
    0 ≤ excursionHBB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
        *excursionGradA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -excursionHAB (a/(p*Y))
        *excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9) →
    0 ≤ 2*excursionHBB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
        *excursionReducedGap (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -(excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9))^2 := by
  apply terminalFace_nonneg_of_polynomial_implication a T Y p q ha hT hY hp hq
  intro _ _
  exact mixtureTerminalFace_small_nonneg a T Y q ha.le ha1 hT.le hT1 hY.le hq.le hq1

/-- The normalized terminal-face KKT certificate at the endpoint `q = 1`. -/
theorem terminalFace_at_one_nonneg
    (a T Y p : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hp : 0 < p) :
    excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
        T (4*T^2/3) (20*T^3/9) < 0 →
    0 ≤ excursionHBB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) T (4*T^2/3)
        *excursionGradA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          T (4*T^2/3) (20*T^3/9)
      -excursionHAB (a/(p*Y))
        *excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          T (4*T^2/3) (20*T^3/9) →
    0 ≤ 2*excursionHBB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) T (4*T^2/3)
        *excursionReducedGap (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          T (4*T^2/3) (20*T^3/9)
      -(excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          T (4*T^2/3) (20*T^3/9))^2 := by
  have hbase := terminalFace_nonneg_of_polynomial_implication
    a T Y p 1 ha hT hY hp (by norm_num : (0 : ℝ) < 1) (by
      intro hG _
      exact mixtureTerminalFace_at_one_nonneg a T Y ha.le ha ha1 hT hY hG)
  simpa only [one_mul, mul_one] using hbase

/-- Reduction of the sharp `A,B` corner to positivity of the compact 15-term polynomial. -/
theorem sharpCorner_nonneg_of_mixturePoly
    (r x u A v B : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hA : 4*u^2 ≤ 3*A) (hB : 4*v^2 ≤ 3*B)
    (hpoly : 0 ≤ sharpMixturePoly r x u v (mixtureWeight u A) (mixtureWeight v B)) :
    0 ≤ excursionReducedGap r x u A (5*A^2/(4*u))
      v B (5*B^2/(4*v)) := by
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBp : 0 < B := by nlinarith [sq_pos_of_pos hv]
  obtain ⟨hp, _⟩ := mixtureWeight_pos_le_one u A hu hA
  obtain ⟨hq, _⟩ := mixtureWeight_pos_le_one v B hv hB
  have hclear := sharpMixtureGap_clear r x u v (mixtureWeight u A)
    (mixtureWeight v B) hp.ne' hq.ne'
  have hscaled : 0 ≤
      (mixtureWeight u A)^4*(mixtureWeight v B)^4
        *sharpMixtureGap r x u v (mixtureWeight u A) (mixtureWeight v B) := by
    rw [hclear]
    exact hpoly
  have hmix : 0 ≤ sharpMixtureGap r x u v (mixtureWeight u A) (mixtureWeight v B) :=
    (mul_nonneg_iff_of_pos_left (by positivity)).mp hscaled
  rw [sharpMixtureGap, ← secondMoment_eq_mixtureWeight u A hu hAp,
    ← sharpThird_eq_mixtureWeight u A hu hAp,
    ← secondMoment_eq_mixtureWeight v B hv hBp,
    ← sharpThird_eq_mixtureWeight v B hv hBp] at hmix
  exact hmix

/-- The excursion-reduced inequality on the simultaneous sharp third-moment boundary,
for arbitrary admissible second moments. -/
theorem sharpCorner_nonneg
    (r x u A v B : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v)
    (hA : 4*u^2 ≤ 3*A) (hB : 4*v^2 ≤ 3*B) :
    0 ≤ excursionReducedGap r x u A (5*A^2/(4*u))
      v B (5*B^2/(4*v)) := by
  apply sharpCorner_nonneg_of_mixturePoly r x u A v B hu hv hA hB
  obtain ⟨hp, hp1⟩ := mixtureWeight_pos_le_one u A hu hA
  obtain ⟨hq, hq1⟩ := mixtureWeight_pos_le_one v B hv hB
  exact sharpMixturePoly_nonneg r x u v (mixtureWeight u A) (mixtureWeight v B)
    hr hx hu hv hp hp1 hq hq1

/-- On the zero set of the terminal gradient, the terminal discriminant is
`2 * HBB * gap`; sharp-corner nonnegativity and positivity of `HBB` therefore settle
the moving endpoint needed for the remaining `q`-interval argument. -/
theorem mixtureTerminalFace_at_grad_zero_nonneg
    (a T Y q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hG : mixtureTerminalGrad a T Y q = 0) :
    0 ≤ mixtureTerminalFace a T Y q := by
  let r := a/Y
  let x := Y*(1-a)/(Y+a)
  let A := 4*Y^2/3
  let v := q*T
  let B := 4*q*T^2/3
  have hr : 0 < r := by dsimp [r]; positivity
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hA : 4*Y^2 ≤ 3*A := by
    dsimp [A]
    ring_nf
    exact le_rfl
  have hqprod : 0 ≤ q*(1-q) := mul_nonneg hq.le (sub_nonneg.mpr hq1)
  have hB : 4*v^2 ≤ 3*B := by
    dsimp [v, B]
    nlinarith [mul_nonneg (sq_nonneg T) hqprod]
  have hgap0 := sharpCorner_nonneg r x Y A v B hr.le hx hY hv hA hB
  have hgap : 0 ≤ excursionReducedGap r x Y A (20*Y^3/9)
      v B (20*q*T^3/9) := by
    convert hgap0 using 1
    all_goals
      dsimp [A, B, v]
      field_simp [hY.ne', hq.ne', hT.ne']
      ring_nf
  obtain ⟨_, hHBB, _⟩ := excursion_hessian_pos r x Y A v B hr hx hY
    (by dsimp [A]; positivity) hv (by dsimp [B]; positivity)
  have hden : Y+a ≠ 0 := by positivity
  have hgradId := terminalGrad_normalize a T Y 1 q (by norm_num) hq.ne'
    hT.ne' hY.ne' (by simpa using hden)
  norm_num at hgradId
  rw [hG] at hgradId
  norm_num at hgradId
  have hgradzero : excursionGradB r x Y A (20*Y^3/9) v B (20*q*T^3/9) = 0 := by
    dsimp [r, x, A, v, B]
    exact hgradId
  have hlhs : 0 ≤
      2*excursionHBB r x Y A v B
          *excursionReducedGap r x Y A (20*Y^3/9) v B (20*q*T^3/9)
        -(excursionGradB r x Y A (20*Y^3/9) v B (20*q*T^3/9))^2 := by
    rw [hgradzero]
    have hprod : 0 ≤ excursionHBB r x Y A v B
        *excursionReducedGap r x Y A (20*Y^3/9) v B (20*q*T^3/9) :=
      mul_nonneg hHBB.le hgap
    nlinarith
  have hfaceId := terminalFace_normalize a T Y 1 q (by norm_num) hq.ne'
    hT.ne' hY.ne' (by simpa using hden)
  norm_num at hfaceId
  change 0 ≤ 2*excursionHBB (a/Y) (Y*(1-a)/(Y+a)) Y (4*Y^2/3)
      (q*T) (4*q*T^2/3)
        *excursionReducedGap (a/Y) (Y*(1-a)/(Y+a)) Y (4*Y^2/3)
          (20*Y^3/9) (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -(excursionGradB (a/Y) (Y*(1-a)/(Y+a)) Y (4*Y^2/3)
          (20*Y^3/9) (q*T) (4*q*T^2/3) (20*q*T^3/9))^2 at hlhs
  rw [hfaceId] at hlhs
  have hfactor : 0 < 32*(2*T^2*q+3*T*q+2*Y*a+3)/(45*T^2*q) := by positivity
  have heq : 32*(2*T^2*q+3*T*q+2*Y*a+3)*mixtureTerminalFace a T Y q
        /(45*T^2*q) =
      (32*(2*T^2*q+3*T*q+2*Y*a+3)/(45*T^2*q))
        *mixtureTerminalFace a T Y q := by ring
  rw [heq] at hlhs
  exact (mul_nonneg_iff_of_pos_left hfactor).mp hlhs

/-- If the affine terminal gradient crosses from positive at `q=0` to nonpositive at
`q=1`, its zero is a moving right endpoint.  The sharp-corner boundary lemma and the
initial-segment Bernstein certificate prove the face inequality up to that endpoint. -/
theorem mixtureTerminalFace_nonneg_of_grad_downcrossing
    (a T Y q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT1 : 1 ≤ T) (hY : 0 < Y) (hq : 0 < q) (_hq1 : q ≤ 1)
    (hG : 0 < mixtureTerminalGrad a T Y q)
    (hG0 : 0 < mixtureTerminalGrad a T Y 0)
    (hG1 : mixtureTerminalGrad a T Y 1 ≤ 0) :
    0 ≤ mixtureTerminalFace a T Y q := by
  let qstar := mixtureTerminalGrad a T Y 0 /
    (mixtureTerminalGrad a T Y 0-mixtureTerminalGrad a T Y 1)
  have hden : 0 < mixtureTerminalGrad a T Y 0-mixtureTerminalGrad a T Y 1 := by
    linarith
  have hqstar : 0 < qstar := by dsimp [qstar]; positivity
  have hqstar1 : qstar ≤ 1 := by
    dsimp [qstar]
    rw [div_le_one hden]
    linarith
  have hqqstar : q ≤ qstar := by
    rw [mixtureTerminalGrad_bernstein_q] at hG
    dsimp [qstar]
    rw [le_div_iff₀ hden]
    nlinarith
  have hGstar : mixtureTerminalGrad a T Y qstar = 0 := by
    rw [mixtureTerminalGrad_bernstein_q]
    dsimp [qstar]
    field_simp [hden.ne']
    ring
  have hboundary := mixtureTerminalFace_at_grad_zero_nonneg a T Y qstar ha ha1
    (lt_of_lt_of_le (by norm_num) hT1) hY hqstar hqstar1 hGstar
  exact mixtureTerminalFace_initial_segment_nonneg a T Y q qstar ha.le ha1 hT1 hY.le
    hq.le hqqstar hqstar1 hG0.le hboundary

/-- The entire `T ≥ 1` part for which the gradient is already nonnegative at
`q=0`.  According to the sign at `q=1`, either the global Bernstein certificate or
the moving gradient-zero endpoint applies. -/
theorem mixtureTerminalFace_nonneg_of_grad0_nonneg
    (a T Y q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT1 : 1 ≤ T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hG : 0 < mixtureTerminalGrad a T Y q)
    (hG0 : 0 ≤ mixtureTerminalGrad a T Y 0) :
    0 ≤ mixtureTerminalFace a T Y q := by
  by_cases hG1 : 0 < mixtureTerminalGrad a T Y 1
  · exact mixtureTerminalFace_nonneg_of_endpoint_grads a T Y q ha.le ha ha1 hT1 hY
      hq.le hq1 hG0 hG1
  · have hG1' : mixtureTerminalGrad a T Y 1 ≤ 0 := le_of_not_gt hG1
    have hG0' : 0 < mixtureTerminalGrad a T Y 0 := by
      rw [mixtureTerminalGrad_bernstein_q] at hG
      by_contra hn
      have hG0nonpos : mixtureTerminalGrad a T Y 0 ≤ 0 := le_of_not_gt hn
      have hleft : (1-q)*mixtureTerminalGrad a T Y 0 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq1) hG0nonpos
      have hright : q*mixtureTerminalGrad a T Y 1 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hq.le hG1'
      linarith
    exact mixtureTerminalFace_nonneg_of_grad_downcrossing a T Y q ha ha1 hT1 hY
      hq hq1 hG hG0' hG1'

/-- Complete polynomial terminal-face certificate.  In fact the KKT side condition is
not needed: positivity of the terminal gradient numerator alone forces face
nonnegativity. -/
theorem mixtureTerminalFace_nonneg_of_grad_pos
    (a T Y q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hG : 0 < mixtureTerminalGrad a T Y q) :
    0 ≤ mixtureTerminalFace a T Y q := by
  by_cases hT1 : T ≤ 1
  · exact mixtureTerminalFace_small_nonneg a T Y q ha.le ha1 hT.le hT1 hY.le hq.le hq1
  · have hT1' : 1 ≤ T := le_of_not_ge hT1
    by_cases hG0 : 0 ≤ mixtureTerminalGrad a T Y 0
    · exact mixtureTerminalFace_nonneg_of_grad0_nonneg a T Y q ha ha1 hT1' hY
        hq hq1 hG hG0
    · have hG0' : mixtureTerminalGrad a T Y 0 < 0 := lt_of_not_ge hG0
      have hend := mixtureTerminalGrad_endpoint_dichotomy a T Y q hq.le hq1 hG
      have hG1 : 0 < mixtureTerminalGrad a T Y 1 := hend.resolve_left (not_lt_of_ge hG0'.le)
      exact mixtureTerminalFace_nonneg_of_grad_upcrossing a T Y q ha ha1 hT1' hY
        hq.le hq1 (by linarith) hG1

/-- The complete normalized terminal-face KKT certificate. -/
theorem terminalFace_nonneg
    (a T Y p q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hp : 0 < p) (hq : 0 < q) (hq1 : q ≤ 1) :
    excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
        (q*T) (4*q*T^2/3) (20*q*T^3/9) < 0 →
    0 ≤ excursionHBB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
        *excursionGradA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -excursionHAB (a/(p*Y))
        *excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9) →
    0 ≤ 2*excursionHBB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
        *excursionReducedGap (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -(excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9))^2 := by
  apply terminalFace_nonneg_of_polynomial_implication a T Y p q ha hT hY hp hq
  intro hG _
  exact mixtureTerminalFace_nonneg_of_grad_pos a T Y q ha ha1 hT hY hq hq1 hG

/-! ## Returning the terminal face to the original coordinates -/

noncomputable def sharpExcursionGradA (r x u A v B : ℝ) : ℝ :=
  excursionGradA r x u A (5*A^2/(4*u)) v B (5*B^2/(4*v))

noncomputable def sharpExcursionGradB (r x u A v B : ℝ) : ℝ :=
  excursionGradB r x u A (5*A^2/(4*u)) v B (5*B^2/(4*v))

noncomputable def sharpExcursionSideA (r x u A v B : ℝ) : ℝ :=
  excursionHAA r x u A v B*sharpExcursionGradB r x u A v B
    -excursionHAB r*sharpExcursionGradA r x u A v B

noncomputable def sharpExcursionSideB (r x u A v B : ℝ) : ℝ :=
  excursionHBB r x u A v B*sharpExcursionGradA r x u A v B
    -excursionHAB r*sharpExcursionGradB r x u A v B

noncomputable def sharpExcursionFaceB (r x u A v B : ℝ) : ℝ :=
  2*excursionHBB r x u A v B
      *excursionReducedGap r x u A (5*A^2/(4*u)) v B (5*B^2/(4*v))
    -(sharpExcursionGradB r x u A v B)^2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The sharp gradients have homogeneous degree three under time rescaling.
theorem sharpExcursionGradA_scale
    (L r x u A v B : ℝ) (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A ≠ 0) (_hB : B ≠ 0) :
    sharpExcursionGradA r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^3*sharpExcursionGradA r x u A v B := by
  unfold sharpExcursionGradA excursionGradA excursionHAA excursionReducedGap
  unfold geomGap geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4
  field_simp [hL, hu, hv, hA, _hB]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The terminal sharp gradient has the same homogeneity.
theorem sharpExcursionGradB_scale
    (L r x u A v B : ℝ) (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (_hA : A ≠ 0) (hB : B ≠ 0) :
    sharpExcursionGradB r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^3*sharpExcursionGradB r x u A v B := by
  unfold sharpExcursionGradB excursionGradB excursionHBB excursionReducedGap
  unfold geomGap geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4
  field_simp [hL, hu, hv, _hA, hB]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The return KKT side expression has homogeneous degree three.
theorem sharpExcursionSideA_scale
    (L r x u A v B : ℝ) (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    sharpExcursionSideA r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^3*sharpExcursionSideA r x u A v B := by
  unfold sharpExcursionSideA
  rw [sharpExcursionGradA_scale L r x u A v B hL hu hv hA hB,
    sharpExcursionGradB_scale L r x u A v B hL hu hv hA hB]
  unfold excursionHAA excursionHAB
  field_simp [hL, hu, hv, hA, hB]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The terminal KKT side expression has homogeneous degree three.
theorem sharpExcursionSideB_scale
    (L r x u A v B : ℝ) (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    sharpExcursionSideB r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^3*sharpExcursionSideB r x u A v B := by
  unfold sharpExcursionSideB
  rw [sharpExcursionGradA_scale L r x u A v B hL hu hv hA hB,
    sharpExcursionGradB_scale L r x u A v B hL hu hv hA hB]
  unfold excursionHBB excursionHAB
  field_simp [hL, hu, hv, hA, hB]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The terminal sharp-face discriminant has homogeneous degree six.
theorem sharpExcursionFaceB_scale
    (L r x u A v B : ℝ) (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (_hA : A ≠ 0) (hB : B ≠ 0) :
    sharpExcursionFaceB r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^6*sharpExcursionFaceB r x u A v B := by
  unfold sharpExcursionFaceB sharpExcursionGradB excursionGradB excursionHBB
  unfold excursionReducedGap geomGap geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4
  field_simp [hL, hu, hv, _hA, hB]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The terminal-face KKT discriminant is nonnegative for arbitrary admissible
second moments, in the original renewal coordinates. -/
theorem sharpExcursionFaceB_nonneg
    (r x u A v B : ℝ) (hr : 0 < r) (hx : 0 ≤ x)
    (hu : 0 < u) (hv : 0 < v)
    (hA : 4*u^2 ≤ 3*A) (hB : 4*v^2 ≤ 3*B)
    (hgrad : sharpExcursionGradB r x u A v B < 0)
    (hside : 0 ≤ sharpExcursionSideB r x u A v B) :
    0 ≤ sharpExcursionFaceB r x u A v B := by
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBp : 0 < B := by nlinarith [sq_pos_of_pos hv]
  let p := mixtureWeight u A
  let q := mixtureWeight v B
  let L := r*u+(r+1)*x
  let a := r*u/L
  let Y := u/(p*L)
  let T := v/(q*L)
  obtain ⟨hp, hp1⟩ := mixtureWeight_pos_le_one u A hu hA
  obtain ⟨hq, hq1⟩ := mixtureWeight_pos_le_one v B hv hB
  have hp' : 0 < p := by simpa [p] using hp
  have hp1' : p ≤ 1 := by simpa [p] using hp1
  have hq' : 0 < q := by simpa [q] using hq
  have hq1' : q ≤ 1 := by simpa [q] using hq1
  have hL : 0 < L := by
    dsimp [L]
    have : 0 < r*u := mul_pos hr hu
    positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one hL]
    dsimp [L]
    nlinarith [mul_nonneg (by linarith : 0 ≤ r+1) hx]
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hCnorm : 5*(4*p*Y^2/3)^2/(4*(p*Y)) = 20*p*Y^3/9 := by
    field_simp [hp'.ne', hY.ne']
    ring
  have hDnorm : 5*(4*q*T^2/3)^2/(4*(q*T)) = 20*q*T^3/9 := by
    field_simp [hq'.ne', hT.ne']
    ring
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
  have hAid : L^2*(4*p*Y^2/3) = A := by
    dsimp [Y, p, mixtureWeight]
    field_simp [hu.ne', hAp.ne', hL.ne']
  have hBid : L^2*(4*q*T^2/3) = B := by
    dsimp [T, q, mixtureWeight]
    field_simp [hv.ne', hBp.ne', hL.ne']
  have hgradScale := sharpExcursionGradB_scale L (a/(p*Y))
    (p*Y*(1-a)/(p*Y+a)) (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
    hL.ne' (by positivity) (by positivity) (by positivity) (by positivity)
  rw [hrid, hxid, huid, hAid, hvid, hBid] at hgradScale
  have hgradNormSharp : sharpExcursionGradB r
      (p*Y*(1-a)/(p*Y+a)) (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3) < 0 := by
    rw [hgradScale] at hgrad
    exact neg_of_mul_neg_right hgrad (by positivity)
  have hsideScale := sharpExcursionSideB_scale L (a/(p*Y))
    (p*Y*(1-a)/(p*Y+a)) (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
    hL.ne' (by positivity) (by positivity) (by positivity) (by positivity)
  rw [hrid, hxid, huid, hAid, hvid, hBid] at hsideScale
  have hsideNormSharp : 0 ≤ sharpExcursionSideB r
      (p*Y*(1-a)/(p*Y+a)) (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3) := by
    rw [hsideScale] at hside
    exact nonneg_of_mul_nonneg_right hside (by positivity)
  have hgradNorm : excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
      (q*T) (4*q*T^2/3) (20*q*T^3/9) < 0 := by
    rw [hrid]
    unfold sharpExcursionGradB at hgradNormSharp
    rw [hCnorm, hDnorm] at hgradNormSharp
    exact hgradNormSharp
  have hsideNorm : 0 ≤ excursionHBB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
      *excursionGradA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
        (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -excursionHAB (a/(p*Y))
        *excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9) := by
    rw [hrid]
    unfold sharpExcursionSideB sharpExcursionGradA sharpExcursionGradB at hsideNormSharp
    rw [hCnorm, hDnorm] at hsideNormSharp
    exact hsideNormSharp
  have hnorm := terminalFace_nonneg a T Y p q ha ha1 hT hY hp' hq' hq1'
    hgradNorm hsideNorm
  have hnormSharp : 0 ≤ sharpExcursionFaceB (a/(p*Y))
      (p*Y*(1-a)/(p*Y+a)) (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3) := by
    unfold sharpExcursionFaceB sharpExcursionGradB
    rw [hCnorm, hDnorm]
    exact hnorm
  have hscale := sharpExcursionFaceB_scale L (a/(p*Y))
    (p*Y*(1-a)/(p*Y+a)) (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
    hL.ne' (by positivity) (by positivity) (by positivity) (by positivity)
  have hscaled : 0 ≤ L^6*sharpExcursionFaceB (a/(p*Y))
      (p*Y*(1-a)/(p*Y+a)) (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3) := by
    exact mul_nonneg (by positivity) hnormSharp
  rw [← hscale] at hscaled
  rwa [hrid, hxid, huid, hAid, hvid, hBid] at hscaled

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- At the simultaneous sharp third-moment boundary the two strict side
conditions for an interior KKT point are contradictory. -/
theorem sharpExcursionInterior_impossible
    (r x u A v B : ℝ) (hr : 0 < r) (hx : 0 ≤ x)
    (hu : 0 < u) (hv : 0 < v)
    (hA : 4*u^2 ≤ 3*A) (hB : 4*v^2 ≤ 3*B)
    (hsideA : sharpExcursionSideA r x u A v B < 0)
    (hsideB : sharpExcursionSideB r x u A v B < 0) : False := by
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBp : 0 < B := by nlinarith [sq_pos_of_pos hv]
  let p := mixtureWeight u A
  let q := mixtureWeight v B
  let L := r*u+(r+1)*x
  let a := r*u/L
  let Y := u/(p*L)
  let T := v/(q*L)
  obtain ⟨hp, hp1⟩ := mixtureWeight_pos_le_one u A hu hA
  obtain ⟨hq, _⟩ := mixtureWeight_pos_le_one v B hv hB
  have hp' : 0 < p := by simpa [p] using hp
  have hq' : 0 < q := by simpa [q] using hq
  have hL : 0 < L := by
    dsimp [L]
    have : 0 < r*u := mul_pos hr hu
    positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one hL]
    dsimp [L]
    nlinarith [mul_nonneg (by linarith : 0 ≤ r+1) hx]
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hCnorm : 5*(4*p*Y^2/3)^2/(4*(p*Y)) = 20*p*Y^3/9 := by
    field_simp [hp'.ne', hY.ne']
    ring
  have hDnorm : 5*(4*q*T^2/3)^2/(4*(q*T)) = 20*q*T^3/9 := by
    field_simp [hq'.ne', hT.ne']
    ring
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
  have hAid : L^2*(4*p*Y^2/3) = A := by
    dsimp [Y, p, mixtureWeight]
    field_simp [hu.ne', hAp.ne', hL.ne']
  have hBid : L^2*(4*q*T^2/3) = B := by
    dsimp [T, q, mixtureWeight]
    field_simp [hv.ne', hBp.ne', hL.ne']
  have hscaleA := sharpExcursionSideA_scale L (a/(p*Y))
    (p*Y*(1-a)/(p*Y+a)) (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
    hL.ne' (by positivity) (by positivity) (by positivity) (by positivity)
  rw [hrid, hxid, huid, hAid, hvid, hBid] at hscaleA
  rw [hscaleA] at hsideA
  have hsideANormSharp : sharpExcursionSideA r
      (p*Y*(1-a)/(p*Y+a)) (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3) < 0 :=
    neg_of_mul_neg_right hsideA (by positivity)
  have hscaleB := sharpExcursionSideB_scale L (a/(p*Y))
    (p*Y*(1-a)/(p*Y+a)) (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
    hL.ne' (by positivity) (by positivity) (by positivity) (by positivity)
  rw [hrid, hxid, huid, hAid, hvid, hBid] at hscaleB
  rw [hscaleB] at hsideB
  have hsideBNormSharp : sharpExcursionSideB r
      (p*Y*(1-a)/(p*Y+a)) (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3) < 0 :=
    neg_of_mul_neg_right hsideB (by positivity)
  have hsideANorm :
      excursionHAA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
        *excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -excursionHAB (a/(p*Y))
        *excursionGradA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9) < 0 := by
    rw [hrid]
    unfold sharpExcursionSideA sharpExcursionGradA sharpExcursionGradB at hsideANormSharp
    rw [hCnorm, hDnorm] at hsideANormSharp
    exact hsideANormSharp
  have hsideBNorm :
      excursionHBB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (q*T) (4*q*T^2/3)
        *excursionGradA (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9)
      -excursionHAB (a/(p*Y))
        *excursionGradB (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (4*p*Y^2/3) (20*p*Y^3/9)
          (q*T) (4*q*T^2/3) (20*q*T^3/9) < 0 := by
    rw [hrid]
    unfold sharpExcursionSideB sharpExcursionGradA sharpExcursionGradB at hsideBNormSharp
    rw [hCnorm, hDnorm] at hsideBNormSharp
    exact hsideBNormSharp
  exact terminalInterior_impossible a T Y p q ha ha1 hT hY hp' hq'
    hsideANorm hsideBNorm

/-- The excursion-reduced `k = 3`, `s = 4` inequality for arbitrary admissible
third moments.  The sharp corner and two faces are certified above, while the
interior KKT alternative is impossible. -/
theorem excursionReducedGap_nonneg
    (r x u A C v B D : ℝ)
    (hr : 0 < r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v)
    (hA : 4*u^2 ≤ 3*A) (hC : 5*A^2 ≤ 4*u*C)
    (hB : 4*v^2 ≤ 3*B) (hD : 5*B^2 ≤ 4*v*D) :
    0 ≤ excursionReducedGap r x u A C v B D := by
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBp : 0 < B := by nlinarith [sq_pos_of_pos hv]
  let C0 := 5*A^2/(4*u)
  let D0 := 5*B^2/(4*v)
  let s := C-C0
  let t := D-D0
  have hs : 0 ≤ s := by
    dsimp [s, C0]
    apply sub_nonneg.mpr
    rw [div_le_iff₀ (by positivity : 0 < 4*u)]
    nlinarith [hC]
  have ht : 0 ≤ t := by
    dsimp [t, D0]
    apply sub_nonneg.mpr
    rw [div_le_iff₀ (by positivity : 0 < 4*v)]
    nlinarith [hD]
  have hcorner : 0 ≤ excursionReducedGap r x u A C0 v B D0 := by
    simpa [C0, D0] using sharpCorner_nonneg r x u A v B hr.le hx hu hv hA hB
  have hkkt := excursionReducedGap_quadrant_nonneg r x u A C0 v B D0 s t
    hr hx hu hAp hv hBp hs ht hcorner
    (by
      intro _ _
      simpa [C0, D0, sharpExcursionFaceA] using
        sharpExcursionFaceA_nonneg r x u A v B hr.le hx hu hv hA hB)
    (by
      intro hgrad hside
      apply sharpExcursionFaceB_nonneg r x u A v B hr hx hu hv hA hB
      · simpa [C0, D0, sharpExcursionGradB] using hgrad
      · simpa [C0, D0, sharpExcursionSideB, sharpExcursionGradA,
          sharpExcursionGradB] using hside)
    (by
      intro hsideA hsideB
      exfalso
      apply sharpExcursionInterior_impossible r x u A v B hr hx hu hv hA hB
      · simpa [C0, D0, sharpExcursionSideA, sharpExcursionGradA,
          sharpExcursionGradB] using hsideA
      · simpa [C0, D0, sharpExcursionSideB, sharpExcursionGradA,
          sharpExcursionGradB] using hsideB)
  have hCeq : C0+s = C := by dsimp [s]; ring
  have hDeq : D0+t = D := by dsimp [t]; ring
  rwa [hCeq, hDeq] at hkkt

/-- Full moment-form `k = 3`, `s = 4` renewal inequality. -/
theorem geomGap_k3_s4_nonneg
    (r x u A C E v B D F : ℝ)
    (hr : 0 < r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v)
    (hA : 4*u^2 ≤ 3*A) (hC : 5*A^2 ≤ 4*u*C) (hE : 6*C^2 ≤ 5*A*E)
    (hB : 4*v^2 ≤ 3*B) (hD : 5*B^2 ≤ 4*v*D) (hF : 6*D^2 ≤ 5*B*F) :
    0 ≤ geomGap r
      (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C) (kernelM4 x u A C E)
      (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D)
        (kernelM4 x v B D F) := by
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBp : 0 < B := by nlinarith [sq_pos_of_pos hv]
  apply geomGap_nonneg_of_excursionReducedGap r x u A C E v B D F
    hr.le hx hu.le hAp hv.le hBp hE hF
  exact excursionReducedGap_nonneg r x u A C v B D hr hx hu hv hA hC hB hD

end SSP.K3S4SecondMoment
