import Mathlib

/-!
# Algebraic certificates for the `k = 2`, `s = 4` renewal proof

This file formalizes the polynomial identities used in the final KKT analysis of
`k2_s4_progress.tex`.  The probabilistic state-return decomposition and the inequality
arguments remain in the paper; every large expansion used there is reduced here to `ring`.
-/

set_option autoImplicit false

namespace SSP.K2S4Renewal

noncomputable def Phi (r b z : ℝ) : ℝ :=
    -48*r^2*b^2 + 82*r*b^3 - 7*b^4 + 76*r*b^2*z - 22*b^3*z
      - 6*r*b*z^2 - 21*b^2*z^2 - 4*b*z^3 + 2*z^4
      + 96*r^2*b - 128*r*b^2 + 32*b^3 - 26*r*b*z + 26*b^2*z
      + 6*r*z^2 - 6*b*z^2 - 48*r^2 + 46*r*b + 2*b^2 - 50*r*z + 50*b*z

/-- Chord form of concavity of `Phi` in `r`. -/
theorem phi_chord (r b z : ℝ) :
    b * Phi r b z = (b-r) * Phi 0 b z + r * Phi b b z
      + 48*b*(1-b)^2*r*(b-r) := by
  unfold Phi
  ring

theorem phi_at_b (b z : ℝ) :
    Phi b b z = (3*b^2 + 8*b*z + 2*z^2) * (3*b-z)^2 := by
  unfold Phi
  ring

noncomputable def Acoef (y : ℝ) : ℝ :=
  2*y^4 - 4*y^3 - 21*y^2 - 22*y - 7

noncomputable def Bcoef (y : ℝ) : ℝ :=
  -6*y^2 + 26*y + 32

noncomputable def Ccoef (y : ℝ) : ℝ := 50*y + 2

theorem phi_at_zero_scaled (b y : ℝ) :
    Phi 0 b (b*y) = b^2 * (Acoef y*b^2 + Bcoef y*b + Ccoef y) := by
  unfold Phi Acoef Bcoef Ccoef
  ring

theorem endpoint_one_factor (y : ℝ) :
    Acoef y + Bcoef y + Ccoef y = (2*y^2 + 8*y + 3) * (y-3)^2 := by
  unfold Acoef Bcoef Ccoef
  ring

theorem corner_discriminant (y : ℝ) :
    Bcoef y ^ 2 - 4*Acoef y*Ccoef y
      = -20*(y+1)^2*(20*y^3 - 81*y^2 - 54*y - 54) := by
  unfold Acoef Bcoef Ccoef
  ring

noncomputable def SBeta (r b z : ℝ) : ℝ :=
  2*z^2 + 23*b*z + 21*b^2 - 48*(1+r)*b + 48*r

noncomputable def KBeta (r b z : ℝ) : ℝ :=
  2*(25*b+z)*Phi r b z - z*(SBeta r b z)^2

/-- Chord form of concavity of the first boundary discriminant in `r`. -/
theorem kBeta_chord (r t b z : ℝ) :
    t * KBeta r b z = (t-r) * KBeta 0 b z + r * KBeta t b z
      + 2400*t*(b+z)*(1-b)^2*r*(t-r) := by
  unfold KBeta SBeta Phi
  ring

noncomputable def TBeta (b z : ℝ) : ℝ :=
  70*b^2 + 171*b*z - 320*b - 36*z - 20

theorem kBeta_at_zero (b z : ℝ) :
    KBeta 0 b z = -5*b*(b+z)^2*TBeta b z := by
  unfold KBeta SBeta Phi TBeta
  ring

theorem kBeta_at_b (b z : ℝ) :
    KBeta b b z = 675*(2*b-z)*b^2*(b+z)^2 := by
  unfold KBeta SBeta Phi
  ring

theorem tBeta_boundary (y : ℝ) :
    48^2*(70+171*y) - 48*(320+36*y)*(2*y^2+23*y+21)
        - 20*(2*y^2+23*y+21)^2
      = -4*(y+25)*(20*y^3+824*y^2+81*y+1701) := by
  ring

noncomputable def SAlpha (r b z : ℝ) : ℝ :=
  48*r*b - 16*b^2 - 13*b*z + 3*z^2 - 48*r - 2*b - 50*z

noncomputable def RAlpha (r b z : ℝ) : ℝ :=
    r*(324*b^3 + 648*b^2*z - 135*b*z^2 + 21*z^3)
      + 20*z^4 - 61*b*z^3 - 135*b^2*z^2 - 108*b^3*z - 54*b^4

/-- Cleared discriminant identity for the second boundary stationary point. -/
theorem alpha_edge_factor (r b z : ℝ) :
    2*(25*(b+z) - 24*(b-r))*Phi r b z - (b-r)*(SAlpha r b z)^2
      = 5*(b+z)*RAlpha r b z := by
  unfold Phi SAlpha RAlpha
  ring

theorem alpha_r_coefficient_scaled (b y : ℝ) :
    324*b^3 + 648*b^2*(b*y) - 135*b*(b*y)^2 + 21*(b*y)^3
      = 3*b^3*(7*y^3 - 45*y^2 + 216*y + 108) := by
  ring

theorem alpha_at_zero_scaled (b y : ℝ) :
    RAlpha 0 b (b*y)
      = b^4*(20*y^4 - 61*y^3 - 135*y^2 - 108*y - 54) := by
  unfold RAlpha
  ring

noncomputable def InteriorR (x u v q : ℝ) : ℝ :=
    80*u^2*q^2 - 89*u*v*q^2 + 9*v^2*q^2 + 70*x*u*q - 170*u^2*q
      + 99*x*v*q + 99*u*v*q + 90*x^2 + 180*x*u + 90*u^2

noncomputable def InteriorR0 (x u : ℝ) : ℝ := 90*(x+u)^2

noncomputable def InteriorR1 (x u v : ℝ) : ℝ :=
  90*x^2 + 215*x*u + 5*u^2 + (99/2)*x*v + (99/2)*u*v

noncomputable def InteriorR2 (x u v : ℝ) : ℝ :=
  90*x^2 + 250*x*u + 99*x*v + 10*u*v + 9*v^2

theorem interior_bernstein (x u v q : ℝ) :
    InteriorR x u v q = InteriorR0 x u*(1-q)^2
      + 2*InteriorR1 x u v*q*(1-q) + InteriorR2 x u v*q^2 := by
  unfold InteriorR InteriorR0 InteriorR1 InteriorR2
  ring

end SSP.K2S4Renewal
