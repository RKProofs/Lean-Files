import SSPLean.K3S4KKT

/-!
# The natural excursion-moment KKT layer for `k = 3`, `s = 4`

There are two possible fourth-moment reductions.  The useful one keeps the common
exponential holding time explicit and replaces only the two excursion fourth moments by
their sharp lower bounds.  Unlike lowering the fourth moments of the full kernels, this
reduction agrees at its deepest corner with `lowerCorner_k3`.
-/

set_option autoImplicit false

namespace SSP.K3S4ExcursionKKT

open SSP.K3S4Renewal
open SSP.K3S4Corner
open SSP.K3S4KKT

/-- Renewal gap after replacing the fourth moments of the two excursions by
`6*C^2/(5*A)` and `6*D^2/(5*B)`. -/
noncomputable def excursionReducedGap
    (r x u A C v B D : ℝ) : ℝ :=
  geomGap r
    (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C)
      (kernelM4 x u A C (6*C^2/(5*A)))
    (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D)
      (kernelM4 x v B D (6*D^2/(5*B)))

noncomputable def excursionHAA (r x u A v B : ℝ) : ℝ :=
  2*r*(A*r + 36*B + 72*r^2*u^2 + 144*r^2*u*x + 72*r^2*x^2
    +72*r*u*v + 144*r*u*x + 72*r*v*x + 144*r*x^2 + 72*v*x + 72*x^2)/(5*A)

noncomputable def excursionHAB (r : ℝ) : ℝ := -14*r

noncomputable def excursionHBB (r x u A v B : ℝ) : ℝ :=
  2*(36*A*r + B + 72*r^2*u^2 + 144*r^2*u*x + 72*r^2*x^2
    +72*r*u*v + 144*r*u*x + 72*r*v*x + 144*r*x^2 + 72*v*x + 72*x^2)/(5*B)

/-- The factored determinant of the excursion-level Hessian. -/
theorem excursion_hessian_det (r x u A v B : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    excursionHAA r x u A v B*excursionHBB r x u A v B-(excursionHAB r)^2 =
      144*r*(A*r+B+2*r^2*u^2+4*r^2*u*x+2*r^2*x^2+2*r*u*v+4*r*u*x
          +2*r*v*x+4*r*x^2+2*v*x+2*x^2)
        *(A*r+B+72*r^2*u^2+144*r^2*u*x+72*r^2*x^2+72*r*u*v+144*r*u*x
          +72*r*v*x+144*r*x^2+72*v*x+72*x^2)/(25*A*B) := by
  unfold excursionHAA excursionHAB excursionHBB
  field_simp [hA, hB]
  ring

/-- First derivative in the return-excursion third moment, encoded by an exact finite
difference.  Since the gap is quadratic, this is independent of the chosen unit step. -/
noncomputable def excursionGradA (r x u A C v B D : ℝ) : ℝ :=
  excursionReducedGap r x u A (C+1) v B D
    -excursionReducedGap r x u A C v B D-excursionHAA r x u A v B/2

/-- First derivative in the terminal-excursion third moment. -/
noncomputable def excursionGradB (r x u A C v B D : ℝ) : ℝ :=
  excursionReducedGap r x u A C v B (D+1)
    -excursionReducedGap r x u A C v B D-excursionHBB r x u A v B/2

noncomputable def GradACompact (r x u A C v B D : ℝ) : ℝ :=
  2*r*(-90*A^2*r^2*u - 90*A^2*r^2*x - 45*A^2*r*v - 90*A^2*r*x + 15*A*B*r*u + 15*A*B*r*x + 60*A*B*v + 15*A*B*x + A*C*r - 35*A*D + 30*A*r^3*u^3 + 90*A*r^3*u^2*x + 90*A*r^3*u*x^2 + 30*A*r^3*x^3 + 150*A*r^2*u^2*v + 90*A*r^2*u^2*x + 300*A*r^2*u*v*x + 180*A*r^2*u*x^2 + 150*A*r^2*v*x^2 + 90*A*r^2*x^3 + 120*A*r*u*v^2 + 300*A*r*u*v*x + 90*A*r*u*x^2 + 120*A*r*v^2*x + 300*A*r*v*x^2 + 90*A*r*x^3 + 120*A*v^2*x + 150*A*v*x^2 + 30*A*x^3 + 36*B*C + 72*C*r^2*u^2 + 144*C*r^2*u*x + 72*C*r^2*x^2 + 72*C*r*u*v + 144*C*r*u*x + 72*C*r*v*x + 144*C*r*x^2 + 72*C*v*x + 72*C*x^2)/(5*A)

set_option maxHeartbeats 2000000 in
theorem GradACompact_eq (r x u A C v B D : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    excursionGradA r x u A C v B D = GradACompact r x u A C v B D := by
  unfold excursionGradA excursionHAA excursionReducedGap geomGap geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4 GradACompact
  field_simp [hA,hB]
  ring

noncomputable def GradBCompact (r x u A C v B D : ℝ) : ℝ :=
  -2*(150*A*B*r^2*u + 150*A*B*r^2*x + 105*A*B*r*v + 150*A*B*r*x - 36*A*D*r + 45*B^2*r*u + 45*B^2*r*x + 45*B^2*x + 35*B*C*r - B*D + 90*B*r^3*u^3 + 270*B*r^3*u^2*x + 270*B*r^3*u*x^2 + 90*B*r^3*x^3 + 90*B*r^2*u^2*v + 270*B*r^2*u^2*x + 180*B*r^2*u*v*x + 540*B*r^2*u*x^2 + 90*B*r^2*v*x^2 + 270*B*r^2*x^3 + 180*B*r*u*v*x + 270*B*r*u*x^2 + 180*B*r*v*x^2 + 270*B*r*x^3 + 90*B*v*x^2 + 90*B*x^3 - 72*D*r^2*u^2 - 144*D*r^2*u*x - 72*D*r^2*x^2 - 72*D*r*u*v - 144*D*r*u*x - 72*D*r*v*x - 144*D*r*x^2 - 72*D*v*x - 72*D*x^2)/(5*B)

set_option maxHeartbeats 2000000 in
theorem GradBCompact_eq (r x u A C v B D : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    excursionGradB r x u A C v B D = GradBCompact r x u A C v B D := by
  unfold excursionGradB excursionHBB excursionReducedGap geomGap geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4 GradBCompact
  field_simp [hA,hB]
  ring


set_option maxHeartbeats 1000000 in
/-- Exact Taylor formula in the two excursion third moments. -/
theorem excursionReducedGap_taylor
    (r x u A C v B D s t : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    excursionReducedGap r x u A (C+s) v B (D+t) =
      excursionReducedGap r x u A C v B D
        +excursionGradA r x u A C v B D*s
        +excursionGradB r x u A C v B D*t
        +(excursionHAA r x u A v B*s^2 + 2*excursionHAB r*s*t
          +excursionHBB r x u A v B*t^2)/2 := by
  unfold excursionGradA excursionGradB excursionHAA excursionHAB excursionHBB
  unfold excursionReducedGap
  unfold geomGap geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4
  field_simp [hA, hB]
  ring

/-- Once the excursion-reduced gap is nonnegative, the original gap follows by monotonicity
in the two fourth moments. -/
theorem geomGap_nonneg_of_excursionReducedGap
    (r x u A C E v B D F : ℝ)
    (hr : 0 ≤ r) (hx : 0 ≤ x) (hu : 0 ≤ u) (hA : 0 < A)
    (hv : 0 ≤ v) (hB : 0 < B)
    (hE : 6*C^2 ≤ 5*A*E) (hF : 6*D^2 ≤ 5*B*F)
    (hred : 0 ≤ excursionReducedGap r x u A C v B D) :
    0 ≤ geomGap r
      (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C) (kernelM4 x u A C E)
      (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D)
        (kernelM4 x v B D F) := by
  let E0 := 6*C^2/(5*A)
  let F0 := 6*D^2/(5*B)
  have hE0 : E0 ≤ E := by
    dsimp [E0]
    rw [div_le_iff₀ (by positivity : 0 < 5*A)]
    linarith
  have hF0 : F0 ≤ F := by
    dsimp [F0]
    rw [div_le_iff₀ (by positivity : 0 < 5*B)]
    linarith
  have ha4 : kernelM4 x u A C E0 ≤ kernelM4 x u A C E := by
    unfold kernelM4
    linarith
  have hb4 : kernelM4 x v B D F0 ≤ kernelM4 x v B D F := by
    unfold kernelM4
    linarith
  have hmono := geomGap_fourth_mono r
    (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C) (kernelM4 x u A C E)
      (kernelM4 x u A C E0)
    (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D) (kernelM4 x v B D F)
      (kernelM4 x v B D F0)
    hr (by unfold kernelM1; positivity) (by unfold kernelM2; positivity)
    (by unfold kernelM1; positivity) (by unfold kernelM2; positivity) ha4 hb4
  have hred' : 0 ≤ geomGap r
      (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C) (kernelM4 x u A C E0)
      (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D)
        (kernelM4 x v B D F0) := by
    simpa only [excursionReducedGap, E0, F0] using hred
  exact le_trans hred' hmono

/-- The excursion-level Hessian is positive definite throughout the genuine cyclic region. -/
theorem excursion_hessian_pos
    (r x u A v B : ℝ) (hr : 0 < r) (hx : 0 ≤ x) (hu : 0 < u) (hA : 0 < A)
    (hv : 0 < v) (hB : 0 < B) :
    0 < excursionHAA r x u A v B ∧
    0 < excursionHBB r x u A v B ∧
    0 < excursionHAA r x u A v B*excursionHBB r x u A v B
      -(excursionHAB r)^2 := by
  have hhaa : 0 < excursionHAA r x u A v B := by
    unfold excursionHAA
    positivity
  have hhbb : 0 < excursionHBB r x u A v B := by
    unfold excursionHBB
    positivity
  have hid := excursion_hessian_det r x u A v B hA.ne' hB.ne'
  have hdet : 0 < excursionHAA r x u A v B*excursionHBB r x u A v B
      -(excursionHAB r)^2 := by
    rw [hid]
    positivity
  exact ⟨hhaa, hhbb, hdet⟩

/-- At the simultaneous lower second- and third-moment corner, the excursion reduction is
exactly the Erlang-three corner already certified in `lowerCorner_k3`. -/
theorem excursionReducedGap_lowerCorner
    (r x u v : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v) :
    0 ≤ excursionReducedGap r x u (4/3*u^2) (20/9*u^3)
      v (4/3*v^2) (20/9*v^3) := by
  have hmain := lowerCorner_k3 r x u v hr hx hu hv.le
  have hu4 : 6*(20/9*u^3)^2/(5*(4/3*u^2)) = 40/9*u^4 := by
    field_simp [hu.ne']
    ring
  have hv4 : 6*(20/9*v^3)^2/(5*(4/3*v^2)) = 40/9*v^4 := by
    field_simp [hv.ne']
    ring
  simpa only [excursionReducedGap, hu4, hv4] using hmain

/-! ## The return-side derivative at the deepest corner -/

noncomputable def cornerGradAPoly (R b z : ℝ) : ℝ :=
  -110*R*b^2-54*R*b*z+112*R*b+54*R*z-2*R
    +29*b^3+81*b^2*z-4*b^2+54*b*z^2+54*b*z+2*b+2*z^3+72*z^2

private theorem cornerGradAPoly_at_zero_nonneg
    (b z : ℝ) (hb : 0 ≤ b) (hz : 0 ≤ z) :
    0 ≤ cornerGradAPoly 0 b z := by
  have hquad : 0 ≤ 29*b^2-4*b+2 := by
    have hid : 29*(29*b^2-4*b+2) = (29*b-2)^2+54 := by ring
    nlinarith [sq_nonneg (29*b-2)]
  have hid : cornerGradAPoly 0 b z =
      b*(29*b^2-4*b+2)+81*b^2*z+54*b*z^2+54*b*z+2*z^3+72*z^2 := by
    unfold cornerGradAPoly
    ring
  rw [hid]
  positivity

private theorem cornerGradAPoly_at_b_nonneg
    (b z : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z) :
    0 ≤ cornerGradAPoly b b z := by
  have hfour : 0 ≤ 4-3*b := by linarith
  have hid : cornerGradAPoly b b z =
      27*b^2*(4-3*b)+27*b^2*z+54*b*z^2+108*b*z+2*z^3+72*z^2 := by
    unfold cornerGradAPoly
    ring
  rw [hid]
  positivity

/-- The compactified return derivative polynomial is nonnegative because it is affine in
`R` and nonnegative at both endpoints of `0 ≤ R ≤ b`. -/
theorem cornerGradAPoly_nonneg
    (R b z : ℝ) (hR : 0 ≤ R) (hRb : R ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z) :
    0 ≤ cornerGradAPoly R b z := by
  have hb0 : 0 ≤ b := le_trans hR hRb
  by_cases hb : b = 0
  · have hR0 : R = 0 := by linarith
    subst R
    exact cornerGradAPoly_at_zero_nonneg b z hb0 hz
  · have hbp : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    have h0 := cornerGradAPoly_at_zero_nonneg b z hb0 hz
    have h1 := cornerGradAPoly_at_b_nonneg b z hb0 hb1 hz
    have hid : b*cornerGradAPoly R b z =
        (b-R)*cornerGradAPoly 0 b z+R*cornerGradAPoly b b z := by
      unfold cornerGradAPoly
      ring
    have hscaled : 0 ≤ b*cornerGradAPoly R b z := by
      rw [hid]
      positivity
    exact (mul_nonneg_iff_of_pos_left hbp).mp hscaled

set_option maxHeartbeats 2000000 in
/-- In compact state-return coordinates, the derivative in the return-excursion third
moment is nonnegative at the simultaneous Erlang corner. -/
theorem transformed_cornerGradA_nonneg
    (R b z : ℝ) (hR : 0 ≤ R) (hRb : R ≤ b) (hb1 : b < 1) (hz : 0 < z) :
    0 ≤ excursionGradA ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
      (20/9*(1-R)^3) (z/((1-b)/(1-R)))
      (4/3*(z/((1-b)/(1-R)))^2) (20/9*(z/((1-b)/(1-R)))^3) := by
  have hR1 : R < 1 := lt_of_le_of_lt hRb hb1
  have h1R : 0 < 1-R := sub_pos.mpr hR1
  have h1b : 0 < 1-b := sub_pos.mpr hb1
  have hP := cornerGradAPoly_nonneg R b z hR hRb hb1.le hz.le
  have hid :
      excursionGradA ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
        (20/9*(1-R)^3) (z/((1-b)/(1-R)))
        (4/3*(z/((1-b)/(1-R)))^2) (20/9*(z/((1-b)/(1-R)))^3) =
      4*(b-R)*(1-R)^3*cornerGradAPoly R b z/(9*(1-b)^4) := by
    repeat rw [GradACompact_eq _ _ _ _ _ _ _ _ (by positivity) (by positivity)]
    dsimp only [GradACompact, excursionReducedGap]
    unfold cornerGradAPoly
    field_simp [ne_of_gt h1R, ne_of_gt h1b, ne_of_gt hz]
    ring
  rw [hid]
  positivity

/-- Scale-free form of `transformed_cornerGradA_nonneg` in the original renewal
coordinates. -/
theorem cornerGradA_nonneg
    (r x u v : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v) :
    0 ≤ excursionGradA r x u (4/3*u^2) (20/9*u^3)
      v (4/3*v^2) (20/9*v^3) := by
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
  have hz : 0 < z := by dsimp [z]; positivity
  have hnorm := transformed_cornerGradA_nonneg R b z hR0 hRb hb1 hz
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
  rw [hvnorm, hrnorm, huNorm] at hnorm
  have hid : l^3*excursionGradA r R (u/l) (4/3*(u/l)^2) (20/9*(u/l)^3)
      (v/l) (4/3*(v/l)^2) (20/9*(v/l)^3) =
    excursionGradA r x u (4/3*u^2) (20/9*u^3)
      v (4/3*v^2) (20/9*v^3) := by
    dsimp [R, l]
    repeat rw [GradACompact_eq _ _ _ _ _ _ _ _ (by positivity) (by positivity)]
    dsimp only [GradACompact, excursionReducedGap]
    field_simp [ne_of_gt hl, ne_of_gt hu, ne_of_gt hv]
  rw [← hid]
  positivity

noncomputable def cornerSidePoly (R b z : ℝ) : ℝ :=
  -110*R*b^2-54*R*b*z+112*R*b+54*R*z-2*R
    +29*b^3+81*b^2*z-4*b^2+54*b*z^2+54*b*z+2*b+2*z^3+2*z^2

noncomputable def cornerSideWeight (R b z : ℝ) : ℝ :=
  2*R*b-2*R+b^2+3*b*z+2*b+2*z^2

private theorem cornerSidePoly_nonneg
    (R b z : ℝ) (hR : 0 ≤ R) (hRb : R ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z) :
    0 ≤ cornerSidePoly R b z := by
  have hb0 : 0 ≤ b := le_trans hR hRb
  have hquad : 0 ≤ 29*b^2-4*b+2 := by
    have hid : 29*(29*b^2-4*b+2) = (29*b-2)^2+54 := by ring
    nlinarith [sq_nonneg (29*b-2)]
  have h0 : 0 ≤ cornerSidePoly 0 b z := by
    have hid : cornerSidePoly 0 b z =
        b*(29*b^2-4*b+2)+81*b^2*z+54*b*z^2+54*b*z+2*z^3+2*z^2 := by
      unfold cornerSidePoly
      ring
    rw [hid]
    positivity
  have hfour : 0 ≤ 4-3*b := by linarith
  have h1 : 0 ≤ cornerSidePoly b b z := by
    have hid : cornerSidePoly b b z =
        27*b^2*(4-3*b)+27*b^2*z+54*b*z^2+108*b*z+2*z^3+2*z^2 := by
      unfold cornerSidePoly
      ring
    rw [hid]
    positivity
  by_cases hb : b = 0
  · have hR0 : R = 0 := by linarith
    simpa [hR0] using h0
  · have hbp : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    have hid : b*cornerSidePoly R b z =
        (b-R)*cornerSidePoly 0 b z+R*cornerSidePoly b b z := by
      unfold cornerSidePoly
      ring
    have hscaled : 0 ≤ b*cornerSidePoly R b z := by
      rw [hid]
      positivity
    exact (mul_nonneg_iff_of_pos_left hbp).mp hscaled

private theorem cornerSideWeight_nonneg
    (R b z : ℝ) (hR : 0 ≤ R) (hRb : R ≤ b) (hz : 0 ≤ z) :
    0 ≤ cornerSideWeight R b z := by
  have hb0 : 0 ≤ b := le_trans hR hRb
  have h0 : 0 ≤ cornerSideWeight 0 b z := by
    have hid : cornerSideWeight 0 b z = b^2+3*b*z+2*b+2*z^2 := by
      unfold cornerSideWeight
      ring
    rw [hid]
    positivity
  have h1 : 0 ≤ cornerSideWeight b b z := by
    have hid : cornerSideWeight b b z = 3*b^2+3*b*z+2*z^2 := by
      unfold cornerSideWeight
      ring
    rw [hid]
    positivity
  by_cases hb : b = 0
  · have hR0 : R = 0 := by linarith
    simpa [hR0] using h0
  · have hbp : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    have hid : b*cornerSideWeight R b z =
        (b-R)*cornerSideWeight 0 b z+R*cornerSideWeight b b z := by
      unfold cornerSideWeight
      ring
    have hscaled : 0 ≤ b*cornerSideWeight R b z := by
      rw [hid]
      positivity
    exact (mul_nonneg_iff_of_pos_left hbp).mp hscaled

/-! ### Terminal-face certificate in the compact region `z ≤ b` -/

noncomputable def bern4 (c0 c1 c2 c3 c4 t : ℝ) : ℝ :=
  c0*(1-t)^4+4*c1*t*(1-t)^3+6*c2*t^2*(1-t)^2+4*c3*t^3*(1-t)+c4*t^4

private theorem bern4_nonneg (c0 c1 c2 c3 c4 t : ℝ)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hc4 : 0 ≤ c4) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ bern4 c0 c1 c2 c3 c4 t := by
  have ht' : 0 ≤ 1-t := sub_nonneg.mpr ht1
  unfold bern4
  positivity

noncomputable def faceCoeff0 (b z : ℝ) : ℝ :=
  -b*(7*b^5+54*b^4*z-136*b^4+391*b^3*z^2-108*b^3*z-12*b^3
    +788*b^2*z^3-424*b^2*z^2-1404*b^2*z-568*b^2+444*b*z^4
    -640*b*z^3-568*b*z^2-20*b-48*z^4-40*z^3-20*z^2)

noncomputable def faceCoeff1 (b z : ℝ) : ℝ :=
  -b*(-695*b^5-1566*b^4*z+944*b^4-331*b^3*z^2-864*b^3*z-2496*b^3
    +1684*b^2*z^3+136*b^2*z^2-864*b^2*z+80*b^2+1284*b*z^4
    -1280*b*z^3-1628*b*z^2-1080*b*z-20*b-96*z^4-80*z^3-40*z^2)/3

noncomputable def faceCoeff2 (b z : ℝ) : ℝ :=
  -b*(297*b^5-3078*b^4*z-4104*b^4-1343*b^3*z^2-756*b^3*z+2700*b^3
    +1004*b^2*z^3+560*b^2*z^2+540*b^2*z-1080*b^2+1236*b*z^4
    -640*b*z^3-1060*b*z^2-1080*b*z-48*z^4-40*z^3-20*z^2)/3

noncomputable def faceCoeff3 (b z : ℝ) : ℝ :=
  -9*b^2*(-27*b^2-27*b*z+22*z^2)*(3*b^2+3*b*z+2*z^2)

noncomputable def terminalFacePoly (R b z : ℝ) : ℝ :=
  faceCoeff0 b z*(b-R)^3+3*faceCoeff1 b z*R*(b-R)^2
    +3*faceCoeff2 b z*R^2*(b-R)+faceCoeff3 b z*R^3

/-! ### Terminal-face certificate in the complementary region `b ≤ z` -/

/-- After a positive rescaling, this is the derivative in the terminal-excursion third
moment at the deepest corner. -/
noncomputable def terminalGradPoly (R b z : ℝ) : ℝ :=
  -110*R*b^2-54*R*b*z+40*R*b+54*R*z+70*R
    +29*b^3+81*b^2*z-40*b^2+54*b*z^2-54*b*z-70*b+2*z^3

/-- First Bernstein coefficient of the quotient in the terminal-face division. -/
noncomputable def terminalQuotCoeff0 (b z : ℝ) : ℝ :=
  583541*b^6+2368872*b^5*z+1611095*b^5+4514474*b^4*z^2
    +8472411*b^4*z+2807405*b^4+4214132*b^3*z^3+7446593*b^3*z^2
    +5719410*b^3*z+1515475*b^3+1588407*b^2*z^4+2339319*b^2*z^3
    +2863431*b^2*z^2+1450035*b^2*z+398650*b^2+170016*b*z^5
    +342744*b*z^4+568140*b*z^3+415390*b*z^2+18900*b*z+12250*b
    +11718*z^6+36750*z^5+55860*z^4+43750*z^3+12250*z^2

/-- Middle Bernstein coefficient of the quotient.  Its only negative monomial has been
grouped with a larger positive one. -/
noncomputable def terminalQuotCoeff1 (b z : ℝ) : ℝ :=
  b^5*(2914990-363614*b)+2068740*b^5*z+4784648*b^4*z^2
    +8894043*b^4*z+3680815*b^4+4148144*b^3*z^3+6436055*b^3*z^2
    +5100570*b^3*z+689225*b^3+1510404*b^2*z^4+1991127*b^2*z^3
    +2946465*b^2*z^2+1626075*b^2*z+875*b^2+170016*b*z^5
    +420747*b*z^4+982320*b*z^3+1072720*b*z^2+340200*b*z+6125*b
    +11718*z^6+36750*z^5+55860*z^4+43750*z^3+12250*z^2

/-- Last Bernstein coefficient of the quotient. -/
noncomputable def terminalQuotCoeff2 (b z : ℝ) : ℝ :=
  1302831*b^6+4334688*b^5*z+2318085*b^5+5684678*b^4*z^2
    +5816475*b^4*z+1573425*b^4+4082156*b^3*z^3+4165805*b^3*z^2
    +3781890*b^3*z+1072575*b^3+1432401*b^2*z^4+1642935*b^2*z^3
    +3659355*b^2*z^2+3435075*b^2*z+661500*b^2+170016*b*z^5
    +498750*b*z^4+1396500*b*z^3+1730050*b*z^2+661500*b*z
    +11718*z^6+36750*z^5+55860*z^4+43750*z^3+12250*z^2

/-- Denominator-free quadratic Bernstein numerator of the quotient. -/
noncomputable def terminalQuotientPoly (R b z : ℝ) : ℝ :=
  terminalQuotCoeff0 b z*(b-R)^2
    +2*terminalQuotCoeff1 b z*R*(b-R)+terminalQuotCoeff2 b z*R^2

noncomputable def terminalRemainderP1 (b z : ℝ) : ℝ :=
  216*b^3+702*b^2*z+270*b^2+355*b*z^2+270*b*z+9*z^3+5*z^2

noncomputable def terminalRemainderP2 (b z : ℝ) : ℝ :=
  5211*b^6+17874*b^5*z+7965*b^5+24345*b^4*z^2+38475*b^4*z
    -3375*b^4+18080*b^3*z^3+24750*b^3*z^2-12960*b^3*z-14175*b^3
    +6596*b^2*z^4-9260*b^2*z^3+21645*b^2*z^2+4725*b^2*z
    +384*b*z^5-1060*b*z^4+7840*b*z^3+9450*b*z^2
    +186*z^6+480*z^5+620*z^4+350*z^3

private theorem terminalQuotientPoly_nonneg
    (R b z : ℝ) (hR : 0 ≤ R) (hRb : R ≤ b) (hb1 : b ≤ 1) (hz : 0 ≤ z) :
    0 ≤ terminalQuotientPoly R b z := by
  have hb0 : 0 ≤ b := le_trans hR hRb
  have hcoef : 0 ≤ 2914990-363614*b := by linarith
  have h0 : 0 ≤ terminalQuotCoeff0 b z := by
    unfold terminalQuotCoeff0
    positivity
  have h1 : 0 ≤ terminalQuotCoeff1 b z := by
    unfold terminalQuotCoeff1
    positivity
  have h2 : 0 ≤ terminalQuotCoeff2 b z := by
    unfold terminalQuotCoeff2
    positivity
  have hd : 0 ≤ b-R := sub_nonneg.mpr hRb
  unfold terminalQuotientPoly
  positivity

private theorem terminalRemainderP1_nonneg
    (b z : ℝ) (hb : 0 ≤ b) (hz : 0 ≤ z) :
    0 ≤ terminalRemainderP1 b z := by
  unfold terminalRemainderP1
  positivity

private theorem terminalRemainderP2_large_nonneg
    (b z : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hbz : b ≤ z) :
    0 ≤ terminalRemainderP2 b z := by
  let w := z-b
  have hw : 0 ≤ w := by dsimp [w]; linarith
  have h2 : 0 ≤ 41597*b^3-1530*b^2+16295*b+3500 := by
    have hsmall : 0 ≤ 16295*b-1530*b^2 := by
      nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hb1)]
    have hcubic : 0 ≤ 41597*b^3 := by positivity
    linarith
  have h3 : 0 ≤ 26012*b^3-4350*b^2+5160*b+175 := by
    have hsmall : 0 ≤ 5160*b-4350*b^2 := by
      nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hb1)]
    have hcubic : 0 ≤ 26012*b^3 := by positivity
    linarith
  have hid : terminalRemainderP2 b z =
      2*b^3*(36338*b^3+30675*b^2+6885*b+175)
        +b^2*(150224*b^3+58355*b^2+56330*b+24675)*w
        +3*b*(41597*b^3-1530*b^2+16295*b+3500)*w^2
        +2*(26012*b^3-4350*b^2+5160*b+175)*w^3
        +2*(5653*b^2+670*b+310)*w^4
        +60*(25*b+8)*w^5+186*w^6 := by
    dsimp [w]
    unfold terminalRemainderP2
    ring
  rw [hid]
  positivity

private theorem terminalFace_division_identity (R b z : ℝ) :
    -(55*b+27*z+35)^3*b^2*terminalFacePoly R b z =
      b^3*(terminalQuotientPoly R b z*terminalGradPoly R b z
        -14*b^2*terminalRemainderP1 b z*terminalRemainderP2 b z) := by
  unfold terminalFacePoly faceCoeff0 faceCoeff1 faceCoeff2 faceCoeff3
  unfold terminalQuotientPoly terminalQuotCoeff0 terminalQuotCoeff1 terminalQuotCoeff2
  unfold terminalGradPoly terminalRemainderP1 terminalRemainderP2
  ring

/-- If the terminal derivative points into its face, the terminal-face numerator is
nonnegative throughout the complementary region `b ≤ z`. -/
theorem terminalFacePoly_large_nonneg
    (R b z : ℝ) (hR : 0 ≤ R) (hRb : R < b) (hb1 : b ≤ 1)
    (hz : 0 ≤ z) (hbz : b ≤ z) (hgrad : terminalGradPoly R b z < 0) :
    0 ≤ terminalFacePoly R b z := by
  have hbp : 0 < b := lt_of_le_of_lt hR hRb
  have hden : 0 < 55*b+27*z+35 := by positivity
  have hQ := terminalQuotientPoly_nonneg R b z hR hRb.le hb1 hz
  have hP1 := terminalRemainderP1_nonneg b z hbp.le hz
  have hP2 := terminalRemainderP2_large_nonneg b z hbp.le hb1 hbz
  have hinside :
      terminalQuotientPoly R b z*terminalGradPoly R b z
          -14*b^2*terminalRemainderP1 b z*terminalRemainderP2 b z ≤ 0 := by
    have hfirst : terminalQuotientPoly R b z*terminalGradPoly R b z ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hQ hgrad.le
    have hsecond : 0 ≤ 14*b^2*terminalRemainderP1 b z*terminalRemainderP2 b z := by
      positivity
    linarith
  have hscaled :
      -(55*b+27*z+35)^3*b^2*terminalFacePoly R b z ≤ 0 := by
    rw [terminalFace_division_identity]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hinside
  have hscale : 0 < (55*b+27*z+35)^3*b^2 := by positivity
  nlinarith

private theorem faceCoeff0_small_nonneg (b y : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ faceCoeff0 b (b*y) := by
  let r0 := bern4 720 720 720 720 720 y
  let r1 := bern4 5832 5832 5862 5922 6012 y
  let r2 := bern4 11016 13122 15856 19278 23448 y
  let r3 := bern4 17496 24057 33048 46089 65232 y
  let r4 := bern4 26244 39366 56214 75816 82944 y
  have h0 : 0 ≤ r0 := by dsimp [r0]; apply bern4_nonneg <;> norm_num <;> assumption
  have h1 : 0 ≤ r1 := by dsimp [r1]; apply bern4_nonneg <;> norm_num <;> assumption
  have h2 : 0 ≤ r2 := by dsimp [r2]; apply bern4_nonneg <;> norm_num <;> assumption
  have h3 : 0 ≤ r3 := by dsimp [r3]; apply bern4_nonneg <;> norm_num <;> assumption
  have h4 : 0 ≤ r4 := by dsimp [r4]; apply bern4_nonneg <;> norm_num <;> assumption
  have hout : 0 ≤ bern4 r0 r1 r2 r3 r4 b :=
    bern4_nonneg r0 r1 r2 r3 r4 b h0 h1 h2 h3 h4 hb0 hb1
  have hid : 36*faceCoeff0 b (b*y) = b^2*bern4 r0 r1 r2 r3 r4 b := by
    dsimp [r0, r1, r2, r3, r4]
    unfold faceCoeff0 bern4
    ring
  have hscaled : 0 ≤ 36*faceCoeff0 b (b*y) := by rw [hid]; positivity
  nlinarith

private theorem faceCoeff1_small_nonneg (b y : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ faceCoeff1 b (b*y) := by
  let r0 := bern4 360 360 360 360 360 y
  let r1 := bern4 0 1215 2460 3735 5040 y
  let r2 := bern4 7128 10206 14158 19044 24924 y
  let r3 := bern4 17496 24057 33048 46089 65232 y
  let r4 := bern4 39366 59049 84321 113724 124416 y
  have h0 : 0 ≤ r0 := by dsimp [r0]; apply bern4_nonneg <;> norm_num <;> assumption
  have h1 : 0 ≤ r1 := by dsimp [r1]; apply bern4_nonneg <;> norm_num <;> assumption
  have h2 : 0 ≤ r2 := by dsimp [r2]; apply bern4_nonneg <;> norm_num <;> assumption
  have h3 : 0 ≤ r3 := by dsimp [r3]; apply bern4_nonneg <;> norm_num <;> assumption
  have h4 : 0 ≤ r4 := by dsimp [r4]; apply bern4_nonneg <;> norm_num <;> assumption
  have hout : 0 ≤ bern4 r0 r1 r2 r3 r4 b :=
    bern4_nonneg r0 r1 r2 r3 r4 b h0 h1 h2 h3 h4 hb0 hb1
  have hid : 54*faceCoeff1 b (b*y) = b^2*bern4 r0 r1 r2 r3 r4 b := by
    dsimp [r0, r1, r2, r3, r4]
    unfold faceCoeff1 bern4
    ring
  have hscaled : 0 ≤ 54*faceCoeff1 b (b*y) := by rw [hid]; positivity
  nlinarith

private theorem faceCoeff2_small_nonneg (b y : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ faceCoeff2 b (b*y) := by
  let r0 := bern4 0 0 0 0 0 y
  let r1 := bern4 9720 12150 14610 17100 19620 y
  let r2 := bern4 3240 7290 12460 18810 26400 y
  let r3 := bern4 17496 24057 33048 46089 65232 y
  let r4 := bern4 78732 118098 168642 227448 248832 y
  have h0 : 0 ≤ r0 := by dsimp [r0]; apply bern4_nonneg <;> norm_num <;> assumption
  have h1 : 0 ≤ r1 := by dsimp [r1]; apply bern4_nonneg <;> norm_num <;> assumption
  have h2 : 0 ≤ r2 := by dsimp [r2]; apply bern4_nonneg <;> norm_num <;> assumption
  have h3 : 0 ≤ r3 := by dsimp [r3]; apply bern4_nonneg <;> norm_num <;> assumption
  have h4 : 0 ≤ r4 := by dsimp [r4]; apply bern4_nonneg <;> norm_num <;> assumption
  have hout : 0 ≤ bern4 r0 r1 r2 r3 r4 b :=
    bern4_nonneg r0 r1 r2 r3 r4 b h0 h1 h2 h3 h4 hb0 hb1
  have hid : 108*faceCoeff2 b (b*y) = b^2*bern4 r0 r1 r2 r3 r4 b := by
    dsimp [r0, r1, r2, r3, r4]
    unfold faceCoeff2 bern4
    ring
  have hscaled : 0 ≤ 108*faceCoeff2 b (b*y) := by rw [hid]; positivity
  nlinarith

private theorem faceCoeff3_small_nonneg (b y : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ faceCoeff3 b (b*y) := by
  let r4 := bern4 1458 2187 3123 4212 4608 y
  have h4 : 0 ≤ r4 := by dsimp [r4]; apply bern4_nonneg <;> norm_num <;> assumption
  have hout : 0 ≤ bern4 0 0 0 0 r4 b :=
    bern4_nonneg 0 0 0 0 r4 b (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) h4 hb0 hb1
  have hid : 2*faceCoeff3 b (b*y) = b^2*bern4 0 0 0 0 r4 b := by
    dsimp [r4]
    unfold faceCoeff3 bern4
    ring
  have hscaled : 0 ≤ 2*faceCoeff3 b (b*y) := by rw [hid]; positivity
  nlinarith

/-- The terminal-face numerator is nonnegative on `0 ≤ R ≤ b` when `z ≤ b`. -/
theorem terminalFacePoly_small_nonneg
    (R b z : ℝ) (hR : 0 ≤ R) (hRb : R ≤ b) (hb1 : b ≤ 1)
    (hz0 : 0 ≤ z) (hzb : z ≤ b) :
    0 ≤ terminalFacePoly R b z := by
  have hb0 : 0 ≤ b := le_trans hR hRb
  by_cases hb : b = 0
  · subst b
    have hR0 : R = 0 := by linarith
    have hz' : z = 0 := by linarith
    subst R
    subst z
    norm_num [terminalFacePoly, faceCoeff0, faceCoeff1, faceCoeff2, faceCoeff3]
  · have hbp : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
    let y := z/b
    have hy0 : 0 ≤ y := by dsimp [y]; positivity
    have hy1 : y ≤ 1 := by dsimp [y]; rw [div_le_one hbp]; exact hzb
    have hzy : b*y = z := by dsimp [y]; field_simp [hb]
    have h0 := faceCoeff0_small_nonneg b y hb0 hb1 hy0 hy1
    have h1 := faceCoeff1_small_nonneg b y hb0 hb1 hy0 hy1
    have h2 := faceCoeff2_small_nonneg b y hb0 hb1 hy0 hy1
    have h3 := faceCoeff3_small_nonneg b y hb0 hb1 hy0 hy1
    rw [hzy] at h0 h1 h2 h3
    have hd : 0 ≤ b-R := sub_nonneg.mpr hRb
    unfold terminalFacePoly
    positivity

noncomputable def transformedTerminalFaceCert (R b z : ℝ) : ℝ :=
  2*excursionHBB ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
      (z/((1-b)/(1-R))) (4/3*(z/((1-b)/(1-R)))^2)
    *excursionReducedGap ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
      (20/9*(1-R)^3) (z/((1-b)/(1-R)))
      (4/3*(z/((1-b)/(1-R)))^2) (20/9*(z/((1-b)/(1-R)))^3)
    -(excursionGradB ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
      (20/9*(1-R)^3) (z/((1-b)/(1-R)))
      (4/3*(z/((1-b)/(1-R)))^2) (20/9*(z/((1-b)/(1-R)))^3))^2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Clearing denominators reduces the terminal-face certificate to `terminalFacePoly`. -/
theorem transformedTerminalFaceCert_nonneg_of_poly_nonneg
    (R b z : ℝ) (hR : 0 ≤ R) (hRb : R < b) (hb1 : b < 1)
    (hz : 0 < z) (hP : 0 ≤ terminalFacePoly R b z) :
    0 ≤ transformedTerminalFaceCert R b z := by
  have hbp : 0 < b := lt_of_le_of_lt hR hRb
  have hW := cornerSideWeight_nonneg R b z hR hRb.le hz.le
  have h1R : 0 < 1-R := sub_pos.mpr (lt_trans hRb hb1)
  have h1b : 0 < 1-b := sub_pos.mpr hb1
  have hid :
      45*b^3*z^2*(1-b)^6*transformedTerminalFaceCert R b z =
        32*(1-R)^6*cornerSideWeight R b z*terminalFacePoly R b z := by
    unfold transformedTerminalFaceCert
    rw [GradBCompact_eq _ _ _ _ _ _ _ _ (by positivity) (by positivity)]
    dsimp only [GradBCompact, excursionHBB, excursionReducedGap]
    unfold geomGap geomM4 geomM3 geomM2 geomM1
    unfold kernelM1 kernelM2 kernelM3 kernelM4
    dsimp only [terminalFacePoly, faceCoeff0, faceCoeff1, faceCoeff2, faceCoeff3]
    dsimp only [cornerSideWeight]
    field_simp [ne_of_gt hbp, ne_of_gt hz, ne_of_gt h1R, ne_of_gt h1b]
    ring
  have hscaled : 0 ≤ 45*b^3*z^2*(1-b)^6*transformedTerminalFaceCert R b z := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 45*b^3*z^2*(1-b)^6)).mp hscaled

/-- On `z ≤ b`, all coefficients of the cubic Bernstein numerator of the terminal-face
certificate are nonnegative. -/
theorem transformedTerminalFaceCert_small_nonneg
    (R b z : ℝ) (hR : 0 ≤ R) (hRb : R < b) (hb1 : b < 1)
    (hz : 0 < z) (hzb : z ≤ b) :
    0 ≤ transformedTerminalFaceCert R b z := by
  apply transformedTerminalFaceCert_nonneg_of_poly_nonneg R b z hR hRb hb1 hz
  exact terminalFacePoly_small_nonneg R b z hR hRb.le hb1.le hz.le hzb

set_option maxHeartbeats 2000000 in
/-- In the complementary region `b ≤ z`, negativity of the terminal derivative forces
the terminal-face certificate to be nonnegative. -/
theorem transformedTerminalFaceCert_large_nonneg
    (R b z : ℝ) (hR : 0 ≤ R) (hRb : R < b) (hb1 : b < 1)
    (hz : 0 < z)
    (hgrad :
      excursionGradB ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
        (20/9*(1-R)^3) (z/((1-b)/(1-R)))
        (4/3*(z/((1-b)/(1-R)))^2) (20/9*(z/((1-b)/(1-R)))^3) < 0)
    (hbz : b ≤ z) :
    0 ≤ transformedTerminalFaceCert R b z := by
  have h1R : 0 < 1-R := sub_pos.mpr (lt_trans hRb hb1)
  have h1b : 0 < 1-b := sub_pos.mpr hb1
  have hid :
      excursionGradB ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
          (20/9*(1-R)^3) (z/((1-b)/(1-R)))
          (4/3*(z/((1-b)/(1-R)))^2) (20/9*(z/((1-b)/(1-R)))^3) =
        (4*(1-R)^3/(9*(1-b)^3))*terminalGradPoly R b z := by
    rw [GradBCompact_eq _ _ _ _ _ _ _ _ (by positivity) (by positivity)]
    dsimp only [GradBCompact, terminalGradPoly]
    field_simp [ne_of_gt h1R, ne_of_gt h1b, ne_of_gt hz]
    ring
  have hfactor : 0 < 4*(1-R)^3/(9*(1-b)^3) := by positivity
  have hgradPoly : terminalGradPoly R b z < 0 := by
    rw [hid] at hgrad
    by_contra hn
    have hpoly : 0 ≤ terminalGradPoly R b z := le_of_not_gt hn
    have := mul_nonneg hfactor.le hpoly
    linarith
  apply transformedTerminalFaceCert_nonneg_of_poly_nonneg R b z hR hRb hb1 hz
  exact terminalFacePoly_large_nonneg R b z hR hRb hb1.le hz.le hbz hgradPoly

/-- The terminal-face certificate needed by the KKT reduction holds for every positive
`z`: use the Bernstein certificate below `b`, and polynomial division above `b`. -/
theorem transformedTerminalFaceCert_of_gradB_neg
    (R b z : ℝ) (hR : 0 ≤ R) (hRb : R < b) (hb1 : b < 1) (hz : 0 < z)
    (hgrad :
      excursionGradB ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
        (20/9*(1-R)^3) (z/((1-b)/(1-R)))
        (4/3*(z/((1-b)/(1-R)))^2) (20/9*(z/((1-b)/(1-R)))^3) < 0) :
    0 ≤ transformedTerminalFaceCert R b z := by
  by_cases hzb : z ≤ b
  · exact transformedTerminalFaceCert_small_nonneg R b z hR hRb hb1 hz hzb
  · exact transformedTerminalFaceCert_large_nonneg R b z hR hRb hb1 hz hgrad
      (le_of_not_ge hzb)

set_option maxHeartbeats 2000000 in
/-- At the deepest corner the terminal-face KKT side condition is automatic.  Therefore,
if the terminal derivative is negative, the constrained minimizer can only lie on that
face; the interior KKT case cannot occur. -/
theorem transformed_cornerSideB_nonneg
    (R b z : ℝ) (hR : 0 ≤ R) (hRb : R ≤ b) (hb1 : b < 1) (hz : 0 < z) :
    0 ≤
      excursionHBB ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
          (z/((1-b)/(1-R))) (4/3*(z/((1-b)/(1-R)))^2)
        *excursionGradA ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
          (20/9*(1-R)^3) (z/((1-b)/(1-R)))
          (4/3*(z/((1-b)/(1-R)))^2) (20/9*(z/((1-b)/(1-R)))^3)
      -excursionHAB ((b-R)/(1-b))
        *excursionGradB ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
          (20/9*(1-R)^3) (z/((1-b)/(1-R)))
          (4/3*(z/((1-b)/(1-R)))^2) (20/9*(z/((1-b)/(1-R)))^3) := by
  have hR1 : R < 1 := lt_of_le_of_lt hRb hb1
  have h1R : 0 < 1-R := sub_pos.mpr hR1
  have h1b : 0 < 1-b := sub_pos.mpr hb1
  have hP := cornerSidePoly_nonneg R b z hR hRb hb1.le hz.le
  have hW := cornerSideWeight_nonneg R b z hR hRb hz.le
  have hid :
      excursionHBB ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
          (z/((1-b)/(1-R))) (4/3*(z/((1-b)/(1-R)))^2)
        *excursionGradA ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
          (20/9*(1-R)^3) (z/((1-b)/(1-R)))
          (4/3*(z/((1-b)/(1-R)))^2) (20/9*(z/((1-b)/(1-R)))^3)
      -excursionHAB ((b-R)/(1-b))
        *excursionGradB ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
          (20/9*(1-R)^3) (z/((1-b)/(1-R)))
          (4/3*(z/((1-b)/(1-R)))^2) (20/9*(z/((1-b)/(1-R)))^3) =
      16*(b-R)*(1-R)^3*cornerSideWeight R b z*cornerSidePoly R b z
        /(5*z^2*(1-b)^4) := by
    rw [GradACompact_eq _ _ _ _ _ _ _ _ (by positivity) (by positivity),
      GradBCompact_eq _ _ _ _ _ _ _ _ (by positivity) (by positivity)]
    dsimp only [GradACompact, GradBCompact, excursionHAB, excursionHBB]
    unfold cornerSidePoly cornerSideWeight
    field_simp [ne_of_gt h1R, ne_of_gt h1b, ne_of_gt hz]
    ring
  rw [hid]
  positivity

/-- Exact four-candidate KKT reduction for the natural excursion-level quadratic. -/
theorem excursionReducedGap_quadrant_nonneg
    (r x u A C v B D s t : ℝ)
    (hr : 0 < r) (hx : 0 ≤ x) (hu : 0 < u) (hA : 0 < A)
    (hv : 0 < v) (hB : 0 < B) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hcorner : 0 ≤ excursionReducedGap r x u A C v B D)
    (hfaceA : excursionGradA r x u A C v B D < 0 →
      0 ≤ excursionHAA r x u A v B*excursionGradB r x u A C v B D
        -excursionHAB r*excursionGradA r x u A C v B D →
      0 ≤ 2*excursionHAA r x u A v B*excursionReducedGap r x u A C v B D
        -(excursionGradA r x u A C v B D)^2)
    (hfaceB : excursionGradB r x u A C v B D < 0 →
      0 ≤ excursionHBB r x u A v B*excursionGradA r x u A C v B D
        -excursionHAB r*excursionGradB r x u A C v B D →
      0 ≤ 2*excursionHBB r x u A v B*excursionReducedGap r x u A C v B D
        -(excursionGradB r x u A C v B D)^2)
    (hinterior :
      excursionHAA r x u A v B*excursionGradB r x u A C v B D
          -excursionHAB r*excursionGradA r x u A C v B D < 0 →
      excursionHBB r x u A v B*excursionGradA r x u A C v B D
          -excursionHAB r*excursionGradB r x u A C v B D < 0 →
      0 ≤ 2*(excursionHAA r x u A v B*excursionHBB r x u A v B
            -(excursionHAB r)^2)*excursionReducedGap r x u A C v B D
        -(excursionHBB r x u A v B*(excursionGradA r x u A C v B D)^2
          -2*excursionHAB r*excursionGradA r x u A C v B D
            *excursionGradB r x u A C v B D
          +excursionHAA r x u A v B*(excursionGradB r x u A C v B D)^2)) :
    0 ≤ excursionReducedGap r x u A (C+s) v B (D+t) := by
  obtain ⟨hhaa, hhbb, hdet⟩ := excursion_hessian_pos r x u A v B hr hx hu hA hv hB
  have hhab : excursionHAB r ≤ 0 := by
    unfold excursionHAB
    linarith
  have hq := quadratic_quadrant_nonneg
    (excursionReducedGap r x u A C v B D)
    (excursionGradA r x u A C v B D) (excursionGradB r x u A C v B D)
    (excursionHAA r x u A v B) (excursionHAB r) (excursionHBB r x u A v B)
    s t hs ht hhaa hhbb hhab hdet hcorner hfaceA hfaceB hinterior
  rw [excursionReducedGap_taylor r x u A C v B D s t hA.ne' hB.ne']
  exact hq

/-- At the simultaneous lower second-moment corner, all of the third-moment quadrant is
reduced to a single scalar certificate on the terminal face.  The corner value is supplied
by `transformed_lowerCorner_k3`; the return derivative and the terminal-face side condition
are automatically nonnegative by the two preceding polynomial certificates. -/
theorem transformed_deepCorner_of_terminalFace
    (R b z s t : ℝ) (hR : 0 ≤ R) (hRb : R < b) (hb1 : b < 1) (hz : 0 < z)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hterminalFace :
      excursionGradB ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
          (20/9*(1-R)^3) (z/((1-b)/(1-R)))
          (4/3*(z/((1-b)/(1-R)))^2) (20/9*(z/((1-b)/(1-R)))^3) < 0 →
      0 ≤
        2*excursionHBB ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
            (z/((1-b)/(1-R))) (4/3*(z/((1-b)/(1-R)))^2)
          *excursionReducedGap ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
            (20/9*(1-R)^3) (z/((1-b)/(1-R)))
            (4/3*(z/((1-b)/(1-R)))^2) (20/9*(z/((1-b)/(1-R)))^3)
        -(excursionGradB ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
          (20/9*(1-R)^3) (z/((1-b)/(1-R)))
          (4/3*(z/((1-b)/(1-R)))^2) (20/9*(z/((1-b)/(1-R)))^3))^2) :
    0 ≤ excursionReducedGap ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
      (20/9*(1-R)^3+s) (z/((1-b)/(1-R)))
      (4/3*(z/((1-b)/(1-R)))^2)
      (20/9*(z/((1-b)/(1-R)))^3+t) := by
  have hRle : R ≤ b := hRb.le
  have hR1 : R < 1 := lt_trans hRb hb1
  have hu : 0 < 1-R := sub_pos.mpr hR1
  have hq : 0 < (1-b)/(1-R) := div_pos (sub_pos.mpr hb1) hu
  have hv : 0 < z/((1-b)/(1-R)) := div_pos hz hq
  have hr : 0 < (b-R)/(1-b) := div_pos (sub_pos.mpr hRb) (sub_pos.mpr hb1)
  have hcorner := excursionReducedGap_lowerCorner ((b-R)/(1-b)) R (1-R)
    (z/((1-b)/(1-R))) hr.le hR hu hv
  have hgradA := transformed_cornerGradA_nonneg R b z hR hRle hb1 hz
  have hsideB := transformed_cornerSideB_nonneg R b z hR hRle hb1 hz
  apply excursionReducedGap_quadrant_nonneg
    ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2) (20/9*(1-R)^3)
    (z/((1-b)/(1-R))) (4/3*(z/((1-b)/(1-R)))^2)
    (20/9*(z/((1-b)/(1-R)))^3) s t hr hR hu (by positivity) hv (by positivity)
    hs ht hcorner
  · intro hneg _
    linarith
  · intro hneg _
    exact hterminalFace hneg
  · intro _ hneg
    linarith

/-- Complete third-moment result at the lower second-moment corner in the compact region
`z ≤ b`. -/
theorem transformed_deepCorner_small
    (R b z s t : ℝ) (hR : 0 ≤ R) (hRb : R < b) (hb1 : b < 1)
    (hz : 0 < z) (hzb : z ≤ b) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ excursionReducedGap ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
      (20/9*(1-R)^3+s) (z/((1-b)/(1-R)))
      (4/3*(z/((1-b)/(1-R)))^2)
      (20/9*(z/((1-b)/(1-R)))^3+t) := by
  apply transformed_deepCorner_of_terminalFace R b z s t hR hRb hb1 hz hs ht
  intro _
  simpa only [transformedTerminalFaceCert] using
    transformedTerminalFaceCert_small_nonneg R b z hR hRb hb1 hz hzb

/-- Complete third-moment result at the lower second-moment corner, with no restriction on
the relative sizes of `z` and `b`. -/
theorem transformed_deepCorner
    (R b z s t : ℝ) (hR : 0 ≤ R) (hRb : R < b) (hb1 : b < 1)
    (hz : 0 < z) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ excursionReducedGap ((b-R)/(1-b)) R (1-R) (4/3*(1-R)^2)
      (20/9*(1-R)^3+s) (z/((1-b)/(1-R)))
      (4/3*(z/((1-b)/(1-R)))^2)
      (20/9*(z/((1-b)/(1-R)))^3+t) := by
  apply transformed_deepCorner_of_terminalFace R b z s t hR hRb hb1 hz hs ht
  intro hgrad
  simpa only [transformedTerminalFaceCert] using
    transformedTerminalFaceCert_of_gradB_neg R b z hR hRb hb1 hz hgrad

/-- Scale-free form of `transformed_deepCorner` in the original renewal coordinates. -/
theorem deepCorner_posReturn
    (r x u v s t : ℝ) (hr : 0 < r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ excursionReducedGap r x u (4/3*u^2) (20/9*u^3+s)
      v (4/3*v^2) (20/9*v^3+t) := by
  let l := x+u
  let R := x/l
  let b := (r+R)/(1+r)
  let z := v/((1+r)*l)
  let s' := s/l^3
  let t' := t/l^3
  have hl : 0 < l := by dsimp [l]; linarith
  have hr1 : 0 < 1+r := by linarith
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R < 1 := by
    dsimp [R, l]
    rw [div_lt_one hl]
    linarith
  have hRb : R < b := by
    have hprod : 0 < r*(1-R) := mul_pos hr (sub_pos.mpr hR1)
    dsimp [b]
    rw [lt_div_iff₀ hr1]
    nlinarith
  have hb1 : b < 1 := by
    dsimp [b]
    rw [div_lt_one hr1]
    linarith
  have hz : 0 < z := by dsimp [z]; positivity
  have hs' : 0 ≤ s' := by dsimp [s']; positivity
  have ht' : 0 ≤ t' := by dsimp [t']; positivity
  have hnorm := transformed_deepCorner R b z s' t' hR0 hRb hb1 hz hs' ht'
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
  rw [hvnorm, hrnorm, huNorm] at hnorm
  have hid : l^6*excursionReducedGap r R (u/l) (4/3*(u/l)^2)
      (20/9*(u/l)^3+s') (v/l) (4/3*(v/l)^2) (20/9*(v/l)^3+t') =
    excursionReducedGap r x u (4/3*u^2) (20/9*u^3+s)
      v (4/3*v^2) (20/9*v^3+t) := by
    dsimp [R, l, s', t']
    unfold excursionReducedGap
    unfold geomGap geomM4 geomM3 geomM2 geomM1
    unfold kernelM1 kernelM2 kernelM3 kernelM4
    field_simp [ne_of_gt hl, ne_of_gt hu, ne_of_gt hv]
  rw [← hid]
  positivity

/-- At the sharp second-moment corner, the excursion-reduced gap is nonnegative for all
admissible third moments, including the no-return boundary. -/
theorem deepCorner
    (r x u v s t : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ excursionReducedGap r x u (4/3*u^2) (20/9*u^3+s)
      v (4/3*v^2) (20/9*v^3+t) := by
  by_cases hr0 : r = 0
  · subst r
    let B := 4/3*v^2
    let D := 20/9*v^3+t
    let F := 6*D^2/(5*B)
    have hB : 4*v^2 ≤ 3*B := by
      have heq : (3 : ℝ)*(4/3*v^2) = 4*v^2 := by ring
      dsimp [B]
      rw [heq]
    have hD : 5*B^2 ≤ 4*v*D := by
      dsimp [B, D]
      nlinarith [mul_nonneg hv.le ht]
    have hF : 6*D^2 ≤ 5*B*F := by
      dsimp [F]
      field_simp [ne_of_gt (show 0 < B by dsimp [B]; positivity)]
      exact le_rfl
    have hterminal := noReturn_k3 x v B D F hx hv hB hD hF
    have hterminal' := sub_nonneg.mpr hterminal
    simpa [excursionReducedGap, geomGap, geomM4, geomM3, geomM2, geomM1,
      kernelM2, kernelM3, B, D, F] using hterminal'
  · exact deepCorner_posReturn r x u v s t (lt_of_le_of_ne hr (Ne.symm hr0))
      hx hu hv hs ht

/-- The full renewal gap is nonnegative when both excursion second moments are sharp;
the third and fourth moments may be anywhere in their admissible regions. -/
theorem geomGap_nonneg_at_lowerSecond
    (r x u C E v D F : ℝ)
    (hr : 0 ≤ r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v)
    (hC : 20/9*u^3 ≤ C) (hD : 20/9*v^3 ≤ D)
    (hE : 6*C^2 ≤ 5*(4/3*u^2)*E) (hF : 6*D^2 ≤ 5*(4/3*v^2)*F) :
    0 ≤ geomGap r
      (kernelM1 x u) (kernelM2 x u (4/3*u^2)) (kernelM3 x u (4/3*u^2) C)
        (kernelM4 x u (4/3*u^2) C E)
      (kernelM1 x v) (kernelM2 x v (4/3*v^2)) (kernelM3 x v (4/3*v^2) D)
        (kernelM4 x v (4/3*v^2) D F) := by
  let s := C-20/9*u^3
  let t := D-20/9*v^3
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hred := deepCorner r x u v s t hr hx hu hv hs ht
  have hCs : 20/9*u^3+s = C := by dsimp [s]; ring
  have hDt : 20/9*v^3+t = D := by dsimp [t]; ring
  rw [hCs, hDt] at hred
  exact geomGap_nonneg_of_excursionReducedGap r x u (4/3*u^2) C E
    v (4/3*v^2) D F hr hx hu.le (by positivity) hv.le (by positivity) hE hF hred

end SSP.K3S4ExcursionKKT
