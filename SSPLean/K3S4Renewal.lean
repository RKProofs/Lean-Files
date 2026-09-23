import SSPLean.K3S3Canonical

/-!
# The `k = 3`, four-stage renewal calculation

This file begins the state-return proof at stage order four.  Its main result is the sharp
no-return lemma: adjoining an independent exponential holding time to a random variable
whose first four normalized moments satisfy the order-three hierarchy preserves the
order-four `k = 3` inequality.

After scaling the mean of the order-three variable to one, write its moments as
`1, A, C, E` and write `y` for the exponential mean.  The hypotheses become

* `4 ≤ 3 A`,
* `5 A² ≤ 4 C`, and
* `6 C² ≤ 5 A E`.

The conclusion is `7 m₃² ≤ 6 m₂ m₄` for the convolution.
-/

set_option autoImplicit false

namespace SSP.K3S4Renewal

noncomputable def kernelM1 (x a : ℝ) : ℝ := x+a

noncomputable def kernelM2 (x a A : ℝ) : ℝ := 2*x^2+2*x*a+A

noncomputable def kernelM3 (x a A C : ℝ) : ℝ := 6*x^3+6*x^2*a+3*x*A+C

noncomputable def kernelM4 (x a A C E : ℝ) : ℝ :=
  24*x^4 + 24*x^3*a + 12*x^2*A + 4*x*C + E

/-- The numerator obtained after replacing `E` by its sharp lower bound
`6 C²/(5 A)`.  It is `5 A` times the resulting `k = 3` gap. -/
noncomputable def reducedNumerator (A C y : ℝ) : ℝ :=
  45*A^3*y^2 + 180*A^2*y^4 + 180*A^2*y^3
    + 180*A*y^6 + 360*A*y^5 + 180*A*y^4
    + C^2*(A+72*y^2+72*y)
    + C*(-90*A^2*y-180*A*y^3-180*A*y^2)

/-- Value of the reduced gap at the lower third-moment endpoint `C = 5 A²/4`. -/
noncomputable def endpointGap (A y : ℝ) : ℝ :=
  (5*A^4 + 360*A^3*y^2 - 720*A^2*y^3 - 576*A^2*y^2
    + 576*A*y^4 + 576*A*y^3 + 576*y^6 + 1152*y^5 + 576*y^4) / 16

private theorem boundaryGap_nonneg (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ endpointGap (4/3 : ℝ) y := by
  have hpoly : 0 ≤ 81*y^4+216*y^3+324*y^2+120*y+20 := by positivity
  have hid : endpointGap (4/3 : ℝ) y =
      4/81*(3*y-1)^2*(81*y^4+216*y^3+324*y^2+120*y+20) := by
    unfold endpointGap
    ring
  rw [hid]
  positivity

private theorem low_q1_nonneg (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    0 ≤ 36*y^4-84*y^3+24*y^2+80/27 := by
  have hr : 0 ≤ 2*y := by positivity
  have hs : 0 ≤ 1-2*y := by linarith
  have hid : 16*(243*y^4-567*y^3+162*y^2+20) =
      320*(1-2*y)^4
        + 1280*(2*y)*(1-2*y)^3
        + 2568*(2*y)^2*(1-2*y)^2
        + 1442*(2*y)^3*(1-2*y)
        + 77*(2*y)^4 := by ring
  have h : 0 ≤ 243*y^4-567*y^3+162*y^2+20 := by
    have : 0 ≤ 16*(243*y^4-567*y^3+162*y^2+20) := by
      rw [hid]
      positivity
    nlinarith
  nlinarith

private theorem low_q2_nonneg (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    0 ≤ -45*y^3+54*y^2+10/3 := by
  have hr : 0 ≤ 2*y := by positivity
  have hs : 0 ≤ 1-2*y := by linarith
  have hid : 8*(10+162*y^2-135*y^3) =
      80*(1-2*y)^3
        + 240*(2*y)*(1-2*y)^2
        + 564*(2*y)^2*(1-2*y)
        + 269*(2*y)^3 := by ring
  have h : 0 ≤ 10+162*y^2-135*y^3 := by
    have : 0 ≤ 8*(10+162*y^2-135*y^3) := by
      rw [hid]
      positivity
    nlinarith
  nlinarith

private theorem middle_q2_pos (y : ℝ) (_hy0 : 1/2 ≤ y) (hy1 : y ≤ 3/5) :
    0 < -45*y^3+54*y^2+10/3 := by
  have hcoef : 0 ≤ 54-45*y := by linarith
  have hterm : 0 ≤ y^2*(54-45*y) := mul_nonneg (sq_nonneg y) hcoef
  nlinarith

/-- Bernstein certificate needed only on the narrow interval `[1/2, 3/5]`. -/
private theorem middle_discriminant_nonneg (y : ℝ) (hy0 : 1/2 ≤ y) (hy1 : y ≤ 3/5) :
    0 ≤
      4*(-45*y^3+54*y^2+10/3)*endpointGap (4/3 : ℝ) y
        -(36*y^4-84*y^3+24*y^2+80/27)^2 := by
  have hr : 0 ≤ 10*y-5 := by linarith
  have hs : 0 ≤ 6-10*y := by linarith
  have hid :
      9112500000 *
        (4*(-45*y^3+54*y^2+10/3)*endpointGap (4/3 : ℝ) y
          -(36*y^4-84*y^3+24*y^2+80/27)^2) =
      969126953125*(6-10*y)^9
        + 10419946875000*(10*y-5)*(6-10*y)^8
        + 49476012187500*(10*y-5)^2*(6-10*y)^7
        + 136247020500000*(10*y-5)^3*(6-10*y)^6
        + 239921155350000*(10*y-5)^4*(6-10*y)^5
        + 280273191840000*(10*y-5)^5*(6-10*y)^4
        + 217270873704000*(10*y-5)^6*(6-10*y)^3
        + 107805958963200*(10*y-5)^7*(6-10*y)^2
        + 31073754286080*(10*y-5)^8*(6-10*y)
        + 3964804243456*(10*y-5)^9 := by
    unfold endpointGap
    ring
  have hscaled : 0 ≤
      9112500000 *
        (4*(-45*y^3+54*y^2+10/3)*endpointGap (4/3 : ℝ) y
          -(36*y^4-84*y^3+24*y^2+80/27)^2) := by
    rw [hid]
    positivity
  nlinarith

/-- Positivity of the lower-third-moment endpoint in the half-plane in which it is used. -/
theorem endpointGap_nonneg (A y : ℝ) (hA : 4/3 ≤ A) (hy : 0 ≤ y)
    (hrel : 18*y^2+18*y ≤ 11*A) :
    0 ≤ endpointGap A y := by
  by_cases hlow : y ≤ 1/2
  · let a := A-4/3
    have ha : 0 ≤ a := by dsimp [a]; linarith
    have hb := boundaryGap_nonneg y hy
    have hq1 := low_q1_nonneg y hy hlow
    have hq2 := low_q2_nonneg y hy hlow
    have hq3 : 0 ≤ 5/3+45/2*y^2 := by positivity
    have hid : endpointGap A y =
        endpointGap (4/3 : ℝ) y
          + a*(36*y^4-84*y^3+24*y^2+80/27)
          + a^2*(-45*y^3+54*y^2+10/3)
          + a^3*(5/3+45/2*y^2) + 5/16*a^4 := by
      dsimp [a]
      unfold endpointGap
      ring
    rw [hid]
    positivity
  · have hyhalf : 1/2 ≤ y := by linarith
    by_cases hmiddle : y ≤ 3/5
    · let a := A-4/3
      have ha : 0 ≤ a := by dsimp [a]; linarith
      have hb := boundaryGap_nonneg y hy
      have hq2 := middle_q2_pos y hyhalf hmiddle
      have hdisc := middle_discriminant_nonneg y hyhalf hmiddle
      have hquad : 0 ≤ endpointGap (4/3 : ℝ) y
          + a*(36*y^4-84*y^3+24*y^2+80/27)
          + a^2*(-45*y^3+54*y^2+10/3) := by
        have hsquare : 0 ≤
            (2*(-45*y^3+54*y^2+10/3)*a
              +(36*y^4-84*y^3+24*y^2+80/27))^2 := sq_nonneg _
        have hidquad :
            4*(-45*y^3+54*y^2+10/3) *
              (endpointGap (4/3 : ℝ) y
                + a*(36*y^4-84*y^3+24*y^2+80/27)
                + a^2*(-45*y^3+54*y^2+10/3)) =
              (2*(-45*y^3+54*y^2+10/3)*a
                +(36*y^4-84*y^3+24*y^2+80/27))^2
              + (4*(-45*y^3+54*y^2+10/3)*endpointGap (4/3 : ℝ) y
                -(36*y^4-84*y^3+24*y^2+80/27)^2) := by ring
        have hscaled : 0 ≤
            4*(-45*y^3+54*y^2+10/3) *
              (endpointGap (4/3 : ℝ) y
                + a*(36*y^4-84*y^3+24*y^2+80/27)
                + a^2*(-45*y^3+54*y^2+10/3)) := by
          rw [hidquad]
          positivity
        nlinarith
      have hq3 : 0 ≤ 5/3+45/2*y^2 := by positivity
      have hid : endpointGap A y =
          endpointGap (4/3 : ℝ) y
            + a*(36*y^4-84*y^3+24*y^2+80/27)
            + a^2*(-45*y^3+54*y^2+10/3)
            + a^3*(5/3+45/2*y^2) + 5/16*a^4 := by
        dsimp [a]
        unfold endpointGap
        ring
      rw [hid]
      positivity
    · have hyhigh : 3/5 ≤ y := by linarith
      let t := 11*A-18*y*(y+1)
      have ht : 0 ≤ t := by dsimp [t]; nlinarith [hrel]
      have hw : 0 ≤ y-3/5 := by linarith
      have hq1 : 0 ≤ 2754*y^2+657*y-1129 := by
        have hid : 25*(2754*y^2+657*y-1129) =
            68850*(y-3/5)^2+99045*(y-3/5)+6416 := by ring
        nlinarith [sq_nonneg (y-3/5)]
      have hq2 : 0 ≤ 3105*y^2+2030*y-833 := by
        have hid : 5*(3105*y^2+2030*y-833) =
            15525*(y-3/5)^2+28780*(y-3/5)+7514 := by ring
        nlinarith [sq_nonneg (y-3/5)]
      have hid : 234256*endpointGap A y =
          3600*y^4*(y+1)^2*(81*y-7)^2
            + 1440*t*y^3*(y+1)*(2754*y^2+657*y-1129)
            + 72*t^2*y^2*(3105*y^2+2030*y-833)
            + 360*t^3*y*(12*y+1) + 5*t^4 := by
        dsimp [t]
        unfold endpointGap
        ring
      have hscaled : 0 ≤ 234256*endpointGap A y := by
        rw [hid]
        positivity
      nlinarith

private theorem derivativeAtEndpoint_nonneg (A y : ℝ) (hA : 4/3 ≤ A)
    (hy : 0 ≤ y) (hrel : 18*y^2+18*y ≤ 11*A) :
    0 ≤ A^2+72*A*y^2+36*A*y-72*y^3-72*y^2 := by
  by_cases hsmall : y ≤ 7/81
  · let a := A-4/3
    have ha : 0 ≤ a := by dsimp [a]; linarith
    have hythird : 3*y ≤ 1 := by nlinarith
    have hcubic : 0 ≤ y^2-3*y^3 := by
      have := mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hythird)
      nlinarith
    have hid : A^2+72*A*y^2+36*A*y-72*y^3-72*y^2 =
        a^2+a*(8/3+72*y^2+36*y)+16/9+48*y+24*(y^2-3*y^3) := by
      dsimp [a]
      ring
    rw [hid]
    positivity
  · have hylarge : 7/81 ≤ y := by linarith
    let t := 11*A-18*y*(y+1)
    have ht : 0 ≤ t := by dsimp [t]; nlinarith [hrel]
    have h81 : 0 ≤ 81*y-7 := by linarith
    have hid : 121*(A^2+72*A*y^2+36*A*y-72*y^3-72*y^2) =
        t^2+828*t*y^2+432*t*y+180*y^2*(y+1)*(81*y-7) := by
      dsimp [t]
      ring
    have hscaled : 0 ≤ 121*(A^2+72*A*y^2+36*A*y-72*y^3-72*y^2) := by
      rw [hid]
      positivity
    nlinarith

/-- The reduced fourth-moment numerator is nonnegative under the sharp order-three
second- and third-moment constraints. -/
theorem reducedNumerator_nonneg (A C y : ℝ) (hA : 4/3 ≤ A) (hy : 0 ≤ y)
    (hC : 5*A^2 ≤ 4*C) :
    0 ≤ reducedNumerator A C y := by
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hlead : 0 < A+72*y^2+72*y := by positivity
  by_cases hdisc : 11*A ≤ 18*y^2+18*y
  · have hfactor : 0 ≤ -11*A+18*y^2+18*y := by linarith
    have hid :
        4*(A+72*y^2+72*y)*reducedNumerator A C y =
          (2*(A+72*y^2+72*y)*C
            +(-90*A^2*y-180*A*y^3-180*A*y^2))^2
          +720*A*y^2*(-11*A+18*y^2+18*y)*(A+2*y^2+2*y)^2 := by
      unfold reducedNumerator
      ring
    have hscaled : 0 ≤ 4*(A+72*y^2+72*y)*reducedNumerator A C y := by
      rw [hid]
      positivity
    nlinarith
  · have hrel : 18*y^2+18*y ≤ 11*A := by linarith
    have hend := endpointGap_nonneg A y hA hy hrel
    have hder := derivativeAtEndpoint_nonneg A y hA hy hrel
    have hC0 : 0 ≤ C-5/4*A^2 := by nlinarith [hC]
    have hlin : 0 ≤
        2*(A+72*y^2+72*y)*(5/4*A^2)
          +(-90*A^2*y-180*A*y^3-180*A*y^2) := by
      have hid :
          2*(A+72*y^2+72*y)*(5/4*A^2)
            +(-90*A^2*y-180*A*y^3-180*A*y^2) =
          5/2*A*(A^2+72*A*y^2+36*A*y-72*y^3-72*y^2) := by ring
      rw [hid]
      positivity
    have hid : reducedNumerator A C y =
        5*A*endpointGap A y
          +(C-5/4*A^2) *
            (2*(A+72*y^2+72*y)*(5/4*A^2)
              +(-90*A^2*y-180*A*y^3-180*A*y^2))
          +(A+72*y^2+72*y)*(C-5/4*A^2)^2 := by
      unfold reducedNumerator endpointGap
      ring
    rw [hid]
    positivity

/-- **Sharp no-return convolution lemma.**  If `(1,A,C,E)` obeys the three sharp
order-three moment inequalities, then adding an exponential random variable of mean `y`
gives moments satisfying the order-four `k = 3` inequality. -/
theorem normalized_noReturn_k3 (A C E y : ℝ) (hy : 0 ≤ y)
    (hA : 4 ≤ 3*A) (hC : 5*A^2 ≤ 4*C) (hE : 6*C^2 ≤ 5*A*E) :
    7*(6*y^3+6*y^2+3*y*A+C)^2 ≤
      6*(2*y^2+2*y+A)*(24*y^4+24*y^3+12*y^2*A+4*y*C+E) := by
  have hA' : 4/3 ≤ A := by nlinarith
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA'
  have hred := reducedNumerator_nonneg A C y hA' hy hC
  have hb2 : 0 ≤ A+2*y^2+2*y := by positivity
  have hslack : 0 ≤ 5*A*E-6*C^2 := by linarith
  have hid :
      5*A *
        (6*(2*y^2+2*y+A)*(24*y^4+24*y^3+12*y^2*A+4*y*C+E)
          -7*(6*y^3+6*y^2+3*y*A+C)^2) =
        reducedNumerator A C y + 6*(A+2*y^2+2*y)*(5*A*E-6*C^2) := by
    unfold reducedNumerator
    ring
  have hscaled : 0 ≤
      5*A *
        (6*(2*y^2+2*y+A)*(24*y^4+24*y^3+12*y^2*A+4*y*C+E)
          -7*(6*y^3+6*y^2+3*y*A+C)^2) := by
    rw [hid]
    positivity
  nlinarith

/-- Scale-free version of `normalized_noReturn_k3`.  Here `(v,B,D,F)` are the first
four raw moments of the terminal excursion and `x` is the mean of the independent
exponential holding time. -/
theorem noReturn_k3 (x v B D F : ℝ) (hx : 0 ≤ x) (hv : 0 < v)
    (hB : 4*v^2 ≤ 3*B) (hD : 5*B^2 ≤ 4*v*D) (hF : 6*D^2 ≤ 5*B*F) :
    7*(6*x^3+6*x^2*v+3*x*B+D)^2 ≤
      6*(2*x^2+2*x*v+B)*(kernelM4 x v B D F) := by
  let A := B/v^2
  let C := D/v^3
  let E := F/v^4
  let y := x/v
  have hv2 : 0 < v^2 := pow_pos hv 2
  have hv4 : 0 < v^4 := pow_pos hv 4
  have hv6 : 0 < v^6 := pow_pos hv 6
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hA : 4 ≤ 3*A := by
    have hid : v^2*(3*A-4) = 3*B-4*v^2 := by
      dsimp [A]
      field_simp [hv.ne']
    have hscaled : 0 ≤ v^2*(3*A-4) := by rw [hid]; linarith
    nlinarith
  have hC : 5*A^2 ≤ 4*C := by
    have hid : v^4*(4*C-5*A^2) = 4*v*D-5*B^2 := by
      dsimp [A, C]
      field_simp [hv.ne']
    have hscaled : 0 ≤ v^4*(4*C-5*A^2) := by rw [hid]; linarith
    nlinarith
  have hE : 6*C^2 ≤ 5*A*E := by
    have hid : v^6*(5*A*E-6*C^2) = 5*B*F-6*D^2 := by
      dsimp [A, C, E]
      field_simp [hv.ne']
    have hscaled : 0 ≤ v^6*(5*A*E-6*C^2) := by rw [hid]; linarith
    nlinarith
  have hnorm := normalized_noReturn_k3 A C E y hy hA hC hE
  have hnormGap : 0 ≤
      6*(2*y^2+2*y+A)*(24*y^4+24*y^3+12*y^2*A+4*y*C+E)
        -7*(6*y^3+6*y^2+3*y*A+C)^2 := by linarith
  have hid : v^6 *
      (6*(2*y^2+2*y+A)*(24*y^4+24*y^3+12*y^2*A+4*y*C+E)
        -7*(6*y^3+6*y^2+3*y*A+C)^2) =
      6*(2*x^2+2*x*v+B)*(kernelM4 x v B D F)
        -7*(6*x^3+6*x^2*v+3*x*B+D)^2 := by
    dsimp [A, C, E, y]
    unfold kernelM4
    field_simp [hv.ne']
  have hgap : 0 ≤
      6*(2*x^2+2*x*v+B)*(kernelM4 x v B D F)
        -7*(6*x^3+6*x^2*v+3*x*B+D)^2 := by
    rw [← hid]
    positivity
  linarith

/-! ## The remaining geometric-return calculation -/

/-- First raw moment of a terminal kernel preceded by a geometric number (mean `r`) of
return kernels. -/
noncomputable def geomM1 (r a1 b1 : ℝ) : ℝ := b1 + r*a1

noncomputable def geomM2 (r a1 a2 b1 b2 : ℝ) : ℝ :=
  b2 + r*a2 + 2*r*a1*geomM1 r a1 b1

noncomputable def geomM3 (r a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  b3 + r*a3 + 3*r*a2*geomM1 r a1 b1 + 3*r*a1*geomM2 r a1 a2 b1 b2

noncomputable def geomM4 (r a1 a2 a3 a4 b1 b2 b3 b4 : ℝ) : ℝ :=
  b4 + r*a4 + 4*r*a3*geomM1 r a1 b1
    + 6*r*a2*geomM2 r a1 a2 b1 b2
    + 4*r*a1*geomM3 r a1 a2 a3 b1 b2 b3

noncomputable def geomGap (r a1 a2 a3 a4 b1 b2 b3 b4 : ℝ) : ℝ :=
  6*geomM2 r a1 a2 b1 b2*geomM4 r a1 a2 a3 a4 b1 b2 b3 b4
    -7*(geomM3 r a1 a2 a3 b1 b2 b3)^2

theorem geomM2_nonneg (r a1 a2 b1 b2 : ℝ) (hr : 0 ≤ r) (ha1 : 0 ≤ a1)
    (ha2 : 0 ≤ a2) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) :
    0 ≤ geomM2 r a1 a2 b1 b2 := by
  unfold geomM2 geomM1
  positivity

/-- The full renewal gap is increasing separately in both kernel fourth moments.  Thus the
cyclic problem may legitimately replace them by their sharp lower bounds before studying the
remaining positive-definite quadratic in `a3,b3`. -/
theorem geomGap_fourth_mono (r a1 a2 a3 a4 a4' b1 b2 b3 b4 b4' : ℝ)
    (hr : 0 ≤ r) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (ha4 : a4' ≤ a4) (hb4 : b4' ≤ b4) :
    geomGap r a1 a2 a3 a4' b1 b2 b3 b4' ≤
      geomGap r a1 a2 a3 a4 b1 b2 b3 b4 := by
  have hm2 := geomM2_nonneg r a1 a2 b1 b2 hr ha1 ha2 hb1 hb2
  have hdelta : 0 ≤ r*(a4-a4')+(b4-b4') := by positivity
  have hid :
      geomGap r a1 a2 a3 a4 b1 b2 b3 b4
        -geomGap r a1 a2 a3 a4' b1 b2 b3 b4' =
      6*geomM2 r a1 a2 b1 b2*(r*(a4-a4')+(b4-b4')) := by
    unfold geomGap geomM4
    ring
  nlinarith [mul_nonneg hm2 hdelta]

/-- If the return excursion has zero duration, the geometrically repeated holding times
collapse to a single exponential of mean `x(1+r)`.  Hence this genuinely cyclic-looking
boundary is already covered by `noReturn_k3`. -/
theorem pureHoldingReturn_k3 (r x v B D F : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x) (hv : 0 < v)
    (hB : 4*v^2 ≤ 3*B) (hD : 5*B^2 ≤ 4*v*D) (hF : 6*D^2 ≤ 5*B*F) :
    7*(geomM3 r (kernelM1 x 0) (kernelM2 x 0 0) (kernelM3 x 0 0 0)
          (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D))^2 ≤
      6*(geomM2 r (kernelM1 x 0) (kernelM2 x 0 0)
          (kernelM1 x v) (kernelM2 x v B)) *
        geomM4 r (kernelM1 x 0) (kernelM2 x 0 0) (kernelM3 x 0 0 0)
          (kernelM4 x 0 0 0 0) (kernelM1 x v) (kernelM2 x v B)
          (kernelM3 x v B D) (kernelM4 x v B D F) := by
  let x' := x*(1+r)
  have hx' : 0 ≤ x' := by dsimp [x']; positivity
  have hmain := noReturn_k3 x' v B D F hx' hv hB hD hF
  have hm2 :
      geomM2 r (kernelM1 x 0) (kernelM2 x 0 0)
          (kernelM1 x v) (kernelM2 x v B) = kernelM2 x' v B := by
    dsimp [x']
    unfold geomM2 geomM1 kernelM1 kernelM2
    ring
  have hm3 :
      geomM3 r (kernelM1 x 0) (kernelM2 x 0 0) (kernelM3 x 0 0 0)
          (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D) =
        kernelM3 x' v B D := by
    dsimp [x']
    unfold geomM3 geomM2 geomM1 kernelM1 kernelM2 kernelM3
    ring
  have hm4 :
      geomM4 r (kernelM1 x 0) (kernelM2 x 0 0) (kernelM3 x 0 0 0)
          (kernelM4 x 0 0 0 0) (kernelM1 x v) (kernelM2 x v B)
          (kernelM3 x v B D) (kernelM4 x v B D F) =
        kernelM4 x' v B D F := by
    dsimp [x']
    unfold geomM4 geomM3 geomM2 geomM1 kernelM1 kernelM2 kernelM3 kernelM4
    ring
  rw [hm2, hm3, hm4]
  simpa only [kernelM2, kernelM3] using hmain

/-- The other elementary boundary: the terminal excursion is zero, so absorption occurs directly
after the last holding time.  The holding mean has been scaled to one.  After the sharp
fourth-moment substitution the gap is a quadratic in `C`; its discriminant is the negative of
a manifestly nonnegative product. -/
theorem normalized_directTerminal_k3 (r u A C E : ℝ) (hr : 0 ≤ r) (hu : 0 ≤ u)
    (hA : 0 < A) (hE : 6*C^2 ≤ 5*A*E) :
    0 ≤ geomGap r
      (kernelM1 1 u) (kernelM2 1 u A) (kernelM3 1 u A C) (kernelM4 1 u A C E)
      (kernelM1 1 0) (kernelM2 1 0 0) (kernelM3 1 0 0 0) (kernelM4 1 0 0 0 0) := by
  by_cases hr0 : r = 0
  · subst r
    norm_num [geomGap, geomM4, geomM3, geomM2, geomM1,
      kernelM1, kernelM2, kernelM3, kernelM4]
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    let E0 := 6*C^2/(5*A)
    let w := 1+r*(u+1)
    let L := r*(A*r+72*w^2)
    let Q := A^3*r^3+26*A^2*r^2*w^2+52*A*r*w^4+36*w^6
    have hw : 0 < w := by dsimp [w]; positivity
    have hL : 0 < L := by dsimp [L]; positivity
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    have hid :
        4*L * (5*A * geomGap r
          (kernelM1 1 u) (kernelM2 1 u A) (kernelM3 1 u A C)
            (kernelM4 1 u A C E0)
          (kernelM1 1 0) (kernelM2 1 0 0) (kernelM3 1 0 0 0)
            (kernelM4 1 0 0 0 0)) =
        (2*L*C+60*A*r*w*(w^2-3*A*r))^2
          +720*A*r*(A*r+2*w^2)*Q := by
      dsimp [E0, w, L, Q]
      unfold geomGap geomM4 geomM3 geomM2 geomM1
      unfold kernelM1 kernelM2 kernelM3 kernelM4
      field_simp [hA.ne']
      ring
    have hscaled : 0 ≤
        4*L * (5*A * geomGap r
          (kernelM1 1 u) (kernelM2 1 u A) (kernelM3 1 u A C)
            (kernelM4 1 u A C E0)
          (kernelM1 1 0) (kernelM2 1 0 0) (kernelM3 1 0 0 0)
            (kernelM4 1 0 0 0 0)) := by
      rw [hid]
      positivity
    have hmin : 0 ≤ geomGap r
        (kernelM1 1 u) (kernelM2 1 u A) (kernelM3 1 u A C)
          (kernelM4 1 u A C E0)
        (kernelM1 1 0) (kernelM2 1 0 0) (kernelM3 1 0 0 0)
          (kernelM4 1 0 0 0 0) := by
      have hfiveA : 0 < 5*A := by positivity
      have hinner : 0 ≤ 5*A * geomGap r
          (kernelM1 1 u) (kernelM2 1 u A) (kernelM3 1 u A C)
            (kernelM4 1 u A C E0)
          (kernelM1 1 0) (kernelM2 1 0 0) (kernelM3 1 0 0 0)
            (kernelM4 1 0 0 0 0) :=
        (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*L)).mp hscaled
      exact (mul_nonneg_iff_of_pos_left hfiveA).mp hinner
    have hE0 : E0 ≤ E := by
      dsimp [E0]
      rw [div_le_iff₀ (by positivity : 0 < 5*A)]
      linarith
    have ha4 : kernelM4 1 u A C E0 ≤ kernelM4 1 u A C E := by
      unfold kernelM4
      linarith
    have hmono := geomGap_fourth_mono r
      (kernelM1 1 u) (kernelM2 1 u A) (kernelM3 1 u A C)
      (kernelM4 1 u A C E) (kernelM4 1 u A C E0)
      (kernelM1 1 0) (kernelM2 1 0 0) (kernelM3 1 0 0 0)
      (kernelM4 1 0 0 0 0) (kernelM4 1 0 0 0 0)
      hr (by unfold kernelM1; positivity) (by unfold kernelM2; positivity)
      (by unfold kernelM1; positivity) (by unfold kernelM2; positivity)
      ha4 (le_refl _)
    exact le_trans hmin hmono

/-- Scale-free form of `normalized_directTerminal_k3`, for an arbitrary positive holding mean. -/
theorem directTerminal_k3 (r x u A C E : ℝ) (hr : 0 ≤ r) (hx : 0 < x) (hu : 0 ≤ u)
    (hA : 0 < A) (hE : 6*C^2 ≤ 5*A*E) :
    0 ≤ geomGap r
      (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C) (kernelM4 x u A C E)
      (kernelM1 x 0) (kernelM2 x 0 0) (kernelM3 x 0 0 0) (kernelM4 x 0 0 0 0) := by
  let u' := u/x
  let A' := A/x^2
  let C' := C/x^3
  let E' := E/x^4
  have hu' : 0 ≤ u' := by dsimp [u']; positivity
  have hA' : 0 < A' := by dsimp [A']; positivity
  have hE' : 6*(C')^2 ≤ 5*A'*E' := by
    have hx6 : 0 < x^6 := pow_pos hx 6
    have hid : x^6*(5*A'*E'-6*(C')^2) = 5*A*E-6*C^2 := by
      dsimp [A', C', E']
      field_simp [hx.ne']
    have hscaled : 0 ≤ x^6*(5*A'*E'-6*(C')^2) := by rw [hid]; linarith
    nlinarith
  have hnorm := normalized_directTerminal_k3 r u' A' C' E' hr hu' hA' hE'
  have hid : x^6 * geomGap r
      (kernelM1 1 u') (kernelM2 1 u' A') (kernelM3 1 u' A' C')
        (kernelM4 1 u' A' C' E')
      (kernelM1 1 0) (kernelM2 1 0 0) (kernelM3 1 0 0 0)
        (kernelM4 1 0 0 0 0) =
    geomGap r
      (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C) (kernelM4 x u A C E)
      (kernelM1 x 0) (kernelM2 x 0 0) (kernelM3 x 0 0 0)
        (kernelM4 x 0 0 0 0) := by
    dsimp [u', A', C', E']
    unfold geomGap geomM4 geomM3 geomM2 geomM1
    unfold kernelM1 kernelM2 kernelM3 kernelM4
    field_simp [hx.ne']
    ring
  rw [← hid]
  positivity

end SSP.K3S4Renewal
