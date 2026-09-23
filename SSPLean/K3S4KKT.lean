import SSPLean.K3S4Corner

/-!
# A quadrant KKT lemma for the `k = 3`, four-stage calculation

The reduced renewal gap is a strictly convex quadratic in the two third moments.  Its
mixed Hessian entry is nonpositive.  This file records the elementary algebraic KKT
reduction appropriate to exactly that situation.  No existence theorem for minimizers is
needed: in each of the four possible regions, completing squares gives the desired lower
bound directly.
-/

set_option autoImplicit false

namespace SSP.K3S4KKT

open SSP.K3S4Corner
open SSP.K3S4Renewal

/-- A positive-definite quadratic with nonpositive mixed coefficient is nonnegative on the
positive quadrant provided its value at each KKT candidate which can be active is
nonnegative.  The four hypotheses after `hdet` are, respectively, the certificates at the
corner, the `y = 0` face, the `x = 0` face, and the interior stationary point.

The quadratic is written with its Hessian coefficients:

`F + g*x + h*y + (A*x^2 + 2*B*x*y + C*y^2)/2`.
-/
theorem quadratic_quadrant_nonneg
    (F g h A B C x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hA : 0 < A) (hC : 0 < C) (hB : B ≤ 0)
    (hdet : 0 < A*C-B^2)
    (hcorner : 0 ≤ F)
    (hfaceX : g < 0 → 0 ≤ A*h-B*g → 0 ≤ 2*A*F-g^2)
    (hfaceY : h < 0 → 0 ≤ C*g-B*h → 0 ≤ 2*C*F-h^2)
    (hinterior : A*h-B*g < 0 → C*g-B*h < 0 →
      0 ≤ 2*(A*C-B^2)*F-(C*g^2-2*B*g*h+A*h^2)) :
    0 ≤ F+g*x+h*y+(A*x^2+2*B*x*y+C*y^2)/2 := by
  let det := A*C-B^2
  have hdet' : 0 < det := by simpa [det] using hdet
  have hquad (s t : ℝ) : 0 ≤ A*s^2+2*B*s*t+C*t^2 := by
    have hid : A*(A*s^2+2*B*s*t+C*t^2) =
        (A*s+B*t)^2+det*t^2 := by
      dsimp [det]
      ring
    have hscaled : 0 ≤ A*(A*s^2+2*B*s*t+C*t^2) := by
      rw [hid]
      positivity
    exact (mul_nonneg_iff_of_pos_left hA).mp hscaled
  have hinterior_case
      (hfirst : A*h-B*g < 0) (hsecond : C*g-B*h < 0) :
      0 ≤ F+g*x+h*y+(A*x^2+2*B*x*y+C*y^2)/2 := by
    have hcert := hinterior hfirst hsecond
    let X := det*x+C*g-B*h
    let Y := det*y+A*h-B*g
    have hq := hquad X Y
    have hid :
        2*det^2*(F+g*x+h*y+(A*x^2+2*B*x*y+C*y^2)/2) =
          det*(2*det*F-(C*g^2-2*B*g*h+A*h^2))
            +(A*X^2+2*B*X*Y+C*Y^2) := by
      dsimp [X, Y, det]
      ring
    have hscaled : 0 ≤
        2*det^2*(F+g*x+h*y+(A*x^2+2*B*x*y+C*y^2)/2) := by
      rw [hid]
      positivity
    have hfactor : 0 < 2*det^2 := by positivity
    exact (mul_nonneg_iff_of_pos_left hfactor).mp hscaled
  by_cases hg : 0 ≤ g
  · by_cases hh : 0 ≤ h
    · have hq := hquad x y
      have hgx : 0 ≤ g*x := mul_nonneg hg hx
      have hhy : 0 ≤ h*y := mul_nonneg hh hy
      nlinarith
    · have hh' : h < 0 := lt_of_not_ge hh
      by_cases hface : 0 ≤ C*g-B*h
      · have hcert := hfaceY hh' hface
        have hid :
            2*C*(F+g*x+h*y+(A*x^2+2*B*x*y+C*y^2)/2) =
              (2*C*F-h^2)+(C*y+h+B*x)^2
                +2*(C*g-B*h)*x+det*x^2 := by
          dsimp [det]
          ring
        have hscaled : 0 ≤
            2*C*(F+g*x+h*y+(A*x^2+2*B*x*y+C*y^2)/2) := by
          rw [hid]
          positivity
        exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 2*C)).mp hscaled
      · have hsecond : C*g-B*h < 0 := lt_of_not_ge hface
        have hdet_h : det*h < 0 := mul_neg_of_pos_of_neg hdet' hh'
        have hmix : 0 ≤ B*(C*g-B*h) :=
          mul_nonneg_of_nonpos_of_nonpos hB hsecond.le
        have hfirst : A*h-B*g < 0 := by
          have hid : C*(A*h-B*g) = det*h-B*(C*g-B*h) := by
            dsimp [det]
            ring
          have : C*(A*h-B*g) < 0 := by nlinarith
          by_contra hn
          exact (not_lt_of_ge (mul_nonneg hC.le (le_of_not_gt hn))) this
        exact hinterior_case hfirst hsecond
  · have hg' : g < 0 := lt_of_not_ge hg
    by_cases hface : 0 ≤ A*h-B*g
    · have hcert := hfaceX hg' hface
      have hid :
          2*A*(F+g*x+h*y+(A*x^2+2*B*x*y+C*y^2)/2) =
            (2*A*F-g^2)+(A*x+g+B*y)^2
              +2*(A*h-B*g)*y+det*y^2 := by
        dsimp [det]
        ring
      have hscaled : 0 ≤
          2*A*(F+g*x+h*y+(A*x^2+2*B*x*y+C*y^2)/2) := by
        rw [hid]
        positivity
      exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 2*A)).mp hscaled
    · have hfirst : A*h-B*g < 0 := lt_of_not_ge hface
      have hdet_g : det*g < 0 := mul_neg_of_pos_of_neg hdet' hg'
      have hmix : 0 ≤ B*(A*h-B*g) :=
        mul_nonneg_of_nonpos_of_nonpos hB hfirst.le
      have hsecond : C*g-B*h < 0 := by
        have hid : A*(C*g-B*h) = det*g-B*(A*h-B*g) := by
          dsimp [det]
          ring
        have : A*(C*g-B*h) < 0 := by nlinarith
        by_contra hn
        exact (not_lt_of_ge (mul_nonneg hA.le (le_of_not_gt hn))) this
      exact hinterior_case hfirst hsecond

/-! ## Instantiation for the renewal gap -/

/-- First partial derivative of `reducedGeomGap` with respect to the return-kernel third
moment. -/
noncomputable def gradA
    (r a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  2*r*(6*a1^3*a2*r^3 + 30*a1^2*a2*b1*r^2 + 14*a1^2*a3*r^2
    -18*a1*a2^2*r^2 + 24*a1*a2*b1^2*r + 3*a1*a2*b2*r
    +14*a1*a3*b1*r - 9*a2^2*b1*r + 12*a2*b1*b2 - 7*a2*b3
    +7*a3*b2)/a2

/-- First partial derivative of `reducedGeomGap` with respect to the terminal-kernel third
moment. -/
noncomputable def gradB
    (r a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  -2*r*(18*a1^3*b2*r^2 + 18*a1^2*b1*b2*r - 14*a1^2*b3*r
    +30*a1*a2*b2*r - 14*a1*b1*b3 + 9*a1*b2^2 + 21*a2*b1*b2
    -7*a2*b3 + 7*a3*b2)/b2

/-- Exact Taylor formula for the reduced renewal gap.  Consequently there are no
higher-order remainders in the `C,D` KKT layer. -/
theorem reducedGeomGap_taylor
    (r a1 a2 a3 b1 b2 b3 s t : ℝ) (ha2 : a2 ≠ 0) (hb2 : b2 ≠ 0) :
    reducedGeomGap r a1 a2 (a3+s) b1 b2 (b3+t) =
      reducedGeomGap r a1 a2 a3 b1 b2 b3
        +gradA r a1 a2 a3 b1 b2 b3*s
        +gradB r a1 a2 a3 b1 b2 b3*t
        +(hAA r a1 a2 b1 b2*s^2 + 2*hAB r*s*t
          +hBB r a1 a2 b1 b2*t^2)/2 := by
  unfold reducedGeomGap gradA gradB hAA hAB hBB
  unfold geomGap geomM4 geomM3 geomM2 geomM1
  field_simp [ha2, hb2]
  ring

/-- The complete KKT reduction for the third-moment layer of the four-state renewal
problem.  Once the four displayed scalar certificates are established at the sharp lower
third moments, the reduced gap is nonnegative for every larger pair of third moments.

This theorem is deliberately stated at arbitrary base values `a3,b3`; in the application
they are `5*A^2/(4*u)` and `5*B^2/(4*v)`.
-/
theorem reducedGeomGap_quadrant_nonneg
    (r a1 a2 a3 b1 b2 b3 s t : ℝ)
    (hr : 0 < r) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hb1 : 0 ≤ b1) (hb2 : 0 < b2) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hcorner : 0 ≤ reducedGeomGap r a1 a2 a3 b1 b2 b3)
    (hfaceA : gradA r a1 a2 a3 b1 b2 b3 < 0 →
      0 ≤ hAA r a1 a2 b1 b2*gradB r a1 a2 a3 b1 b2 b3
        -hAB r*gradA r a1 a2 a3 b1 b2 b3 →
      0 ≤ 2*hAA r a1 a2 b1 b2*reducedGeomGap r a1 a2 a3 b1 b2 b3
        -(gradA r a1 a2 a3 b1 b2 b3)^2)
    (hfaceB : gradB r a1 a2 a3 b1 b2 b3 < 0 →
      0 ≤ hBB r a1 a2 b1 b2*gradA r a1 a2 a3 b1 b2 b3
        -hAB r*gradB r a1 a2 a3 b1 b2 b3 →
      0 ≤ 2*hBB r a1 a2 b1 b2*reducedGeomGap r a1 a2 a3 b1 b2 b3
        -(gradB r a1 a2 a3 b1 b2 b3)^2)
    (hinterior :
      hAA r a1 a2 b1 b2*gradB r a1 a2 a3 b1 b2 b3
          -hAB r*gradA r a1 a2 a3 b1 b2 b3 < 0 →
      hBB r a1 a2 b1 b2*gradA r a1 a2 a3 b1 b2 b3
          -hAB r*gradB r a1 a2 a3 b1 b2 b3 < 0 →
      0 ≤ 2*(hAA r a1 a2 b1 b2*hBB r a1 a2 b1 b2-(hAB r)^2)
            *reducedGeomGap r a1 a2 a3 b1 b2 b3
        -(hBB r a1 a2 b1 b2*(gradA r a1 a2 a3 b1 b2 b3)^2
          -2*hAB r*gradA r a1 a2 a3 b1 b2 b3
            *gradB r a1 a2 a3 b1 b2 b3
          +hAA r a1 a2 b1 b2*(gradB r a1 a2 a3 b1 b2 b3)^2)) :
    0 ≤ reducedGeomGap r a1 a2 (a3+s) b1 b2 (b3+t) := by
  have hU : 0 < 2*a1^2*r^2+2*a1*b1*r+b2 := by positivity
  have hV : 0 < 2*a1^2*r+2*a1*b1+a2 := by positivity
  have hhaa : 0 < hAA r a1 a2 b1 b2 := by
    unfold hAA
    positivity
  have hhbb : 0 < hBB r a1 a2 b1 b2 := by
    unfold hBB
    positivity
  have hhab : hAB r ≤ 0 := by
    unfold hAB
    linarith
  have hdetid := hessian_det r a1 a2 b1 b2 ha2.ne' hb2.ne'
  have hdet : 0 <
      hAA r a1 a2 b1 b2*hBB r a1 a2 b1 b2-(hAB r)^2 := by
    rw [hdetid]
    positivity
  have hq := quadratic_quadrant_nonneg
    (reducedGeomGap r a1 a2 a3 b1 b2 b3)
    (gradA r a1 a2 a3 b1 b2 b3) (gradB r a1 a2 a3 b1 b2 b3)
    (hAA r a1 a2 b1 b2) (hAB r) (hBB r a1 a2 b1 b2) s t
    hs ht hhaa hhbb hhab hdet hcorner hfaceA hfaceB hinterior
  rw [reducedGeomGap_taylor r a1 a2 a3 b1 b2 b3 s t ha2.ne' hb2.ne']
  exact hq

/-! ## Named certificates at the sharp third-moment boundary -/

/-- The full third moment of an exponential holding time followed by an excursion whose
third moment is at the order-three lower endpoint. -/
noncomputable def sharpKernelM3 (x u A : ℝ) : ℝ :=
  kernelM3 x u A (5*A^2/(4*u))

/-- The reduced renewal gap at the simultaneous sharp third-moment boundary. -/
noncomputable def sharpGap (r x u A v B : ℝ) : ℝ :=
  reducedGeomGap r
    (kernelM1 x u) (kernelM2 x u A) (sharpKernelM3 x u A)
    (kernelM1 x v) (kernelM2 x v B) (sharpKernelM3 x v B)

noncomputable def sharpGradA (r x u A v B : ℝ) : ℝ :=
  gradA r
    (kernelM1 x u) (kernelM2 x u A) (sharpKernelM3 x u A)
    (kernelM1 x v) (kernelM2 x v B) (sharpKernelM3 x v B)

noncomputable def sharpGradB (r x u A v B : ℝ) : ℝ :=
  gradB r
    (kernelM1 x u) (kernelM2 x u A) (sharpKernelM3 x u A)
    (kernelM1 x v) (kernelM2 x v B) (sharpKernelM3 x v B)

noncomputable def sharpHAA (r x u A v B : ℝ) : ℝ :=
  hAA r (kernelM1 x u) (kernelM2 x u A) (kernelM1 x v) (kernelM2 x v B)

noncomputable def sharpHAB (r : ℝ) : ℝ := hAB r

noncomputable def sharpHBB (r x u A v B : ℝ) : ℝ :=
  hBB r (kernelM1 x u) (kernelM2 x u A) (kernelM1 x v) (kernelM2 x v B)

/-- KKT side condition for a stationary point on the return-third-moment face. -/
noncomputable def sharpSideA (r x u A v B : ℝ) : ℝ :=
  sharpHAA r x u A v B*sharpGradB r x u A v B
    -sharpHAB r*sharpGradA r x u A v B

/-- KKT side condition for a stationary point on the terminal-third-moment face. -/
noncomputable def sharpSideB (r x u A v B : ℝ) : ℝ :=
  sharpHBB r x u A v B*sharpGradA r x u A v B
    -sharpHAB r*sharpGradB r x u A v B

noncomputable def sharpFaceA (r x u A v B : ℝ) : ℝ :=
  2*sharpHAA r x u A v B*sharpGap r x u A v B
    -(sharpGradA r x u A v B)^2

noncomputable def sharpFaceB (r x u A v B : ℝ) : ℝ :=
  2*sharpHBB r x u A v B*sharpGap r x u A v B
    -(sharpGradB r x u A v B)^2

noncomputable def sharpInterior (r x u A v B : ℝ) : ℝ :=
  2*(sharpHAA r x u A v B*sharpHBB r x u A v B-(sharpHAB r)^2)
      *sharpGap r x u A v B
    -(sharpHBB r x u A v B*(sharpGradA r x u A v B)^2
      -2*sharpHAB r*sharpGradA r x u A v B*sharpGradB r x u A v B
      +sharpHAA r x u A v B*(sharpGradB r x u A v B)^2)

/-- Reduction of the complete positive-parameter renewal problem to four explicitly named
semialgebraic certificates.  The excursion assumptions are exactly the adjacent order-three
moment inequalities.  Fourth moments are first lowered using `noReturn_k3`; the remaining
third-moment quadrant is then handled by `reducedGeomGap_quadrant_nonneg`.

Thus no probabilistic or optimization argument remains after the hypotheses `hcorner`,
`hfaceA`, `hfaceB`, and `hinterior` have been proved.
-/
theorem geomGap_nonneg_of_sharp_certificates
    (r x u A C E v B D F : ℝ)
    (hr : 0 < r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v)
    (hA : 4*u^2 ≤ 3*A) (hC : 5*A^2 ≤ 4*u*C) (hE : 6*C^2 ≤ 5*A*E)
    (hB : 4*v^2 ≤ 3*B) (hD : 5*B^2 ≤ 4*v*D) (hF : 6*D^2 ≤ 5*B*F)
    (hcorner : 0 ≤ sharpGap r x u A v B)
    (hfaceA : sharpGradA r x u A v B < 0 →
      0 ≤ sharpSideA r x u A v B → 0 ≤ sharpFaceA r x u A v B)
    (hfaceB : sharpGradB r x u A v B < 0 →
      0 ≤ sharpSideB r x u A v B → 0 ≤ sharpFaceB r x u A v B)
    (hinterior : sharpSideA r x u A v B < 0 →
      sharpSideB r x u A v B < 0 → 0 ≤ sharpInterior r x u A v B) :
    0 ≤ geomGap r
      (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C) (kernelM4 x u A C E)
      (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D)
        (kernelM4 x v B D F) := by
  have hApos : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBpos : 0 < B := by nlinarith [sq_pos_of_pos hv]
  let C0 := 5*A^2/(4*u)
  let D0 := 5*B^2/(4*v)
  let s := C-C0
  let t := D-D0
  have hC0 : C0 ≤ C := by
    dsimp [C0]
    rw [div_le_iff₀ (by positivity : 0 < 4*u)]
    linarith
  have hD0 : D0 ≤ D := by
    dsimp [D0]
    rw [div_le_iff₀ (by positivity : 0 < 4*v)]
    linarith
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ha1 : 0 < kernelM1 x u := by unfold kernelM1; linarith
  have hb1 : 0 < kernelM1 x v := by unfold kernelM1; linarith
  have ha2 : 0 < kernelM2 x u A := by unfold kernelM2; positivity
  have hb2 : 0 < kernelM2 x v B := by unfold kernelM2; positivity
  have hred : 0 ≤ reducedGeomGap r
      (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C)
      (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D) := by
    have hkkt := reducedGeomGap_quadrant_nonneg r
      (kernelM1 x u) (kernelM2 x u A) (sharpKernelM3 x u A)
      (kernelM1 x v) (kernelM2 x v B) (sharpKernelM3 x v B) s t
      hr ha1 ha2 hb1.le hb2 hs ht hcorner
      (by simpa [sharpGradA, sharpGradB, sharpHAA, sharpHAB, sharpSideA,
          sharpFaceA, sharpGap] using hfaceA)
      (by simpa [sharpGradA, sharpGradB, sharpHAB, sharpHBB, sharpSideB,
          sharpFaceB, sharpGap] using hfaceB)
      (by simpa [sharpGradA, sharpGradB, sharpHAA, sharpHAB, sharpHBB,
          sharpSideA, sharpSideB, sharpInterior, sharpGap] using hinterior)
    have ha3 : sharpKernelM3 x u A+s = kernelM3 x u A C := by
      dsimp [sharpKernelM3, s, C0]
      unfold kernelM3
      field_simp [hu.ne']
      ring
    have hb3 : sharpKernelM3 x v B+t = kernelM3 x v B D := by
      dsimp [sharpKernelM3, t, D0]
      unfold kernelM3
      field_simp [hv.ne']
      ring
    rwa [ha3, hb3] at hkkt
  have hreturn := noReturn_k3 x u A C E hx hu hA hC hE
  have hterminal := noReturn_k3 x v B D F hx hv hB hD hF
  have ha4 : 7*(kernelM3 x u A C)^2/(6*kernelM2 x u A) ≤ kernelM4 x u A C E := by
    rw [div_le_iff₀ (by positivity : 0 < 6*kernelM2 x u A)]
    simpa only [kernelM2, kernelM3, mul_comm] using hreturn
  have hb4 : 7*(kernelM3 x v B D)^2/(6*kernelM2 x v B) ≤ kernelM4 x v B D F := by
    rw [div_le_iff₀ (by positivity : 0 < 6*kernelM2 x v B)]
    simpa only [kernelM2, kernelM3, mul_comm] using hterminal
  have hmono := geomGap_fourth_mono r
    (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C) (kernelM4 x u A C E)
      (7*(kernelM3 x u A C)^2/(6*kernelM2 x u A))
    (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D) (kernelM4 x v B D F)
      (7*(kernelM3 x v B D)^2/(6*kernelM2 x v B))
    hr.le ha1.le ha2.le hb1.le hb2.le ha4 hb4
  exact le_trans hred hmono

end SSP.K3S4KKT
