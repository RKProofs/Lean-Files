import SSPLean.K3S2Direct

/-!
# The `k = 3`, three-state canonical inequality

For the He--Zhang order-three canonical form, reciprocal-rate coordinates reduce the inverse
rate matrix, up to the harmless positive scalar `(1-u)⁻¹`, to

`B = !![a, u*b, u*c; a, b, u*c; a, b, c]`,

where `a,b,c \u2265 0` and `0 ≤ u ≤ 1`.  This file proves directly, for every starting
state, `10 z₂ z₄ \u2265 9 z₃²`, equivalently `5 m₂ m₄ \u2265 6 m₃²`.
-/

open Finset

set_option autoImplicit false

namespace SSP.K3S3Canonical

noncomputable def twoExpPoly (a b : ℝ) : ℝ :=
  a^6 + 2*a^5*b + 3*a^4*b^2 - 6*a^3*b^3 + 3*a^2*b^4 + 2*a*b^5 + b^6

theorem twoExpPoly_symm (a b : ℝ) : twoExpPoly a b = twoExpPoly b a := by
  unfold twoExpPoly
  ring

theorem twoExpPoly_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ twoExpPoly a b := by
  rcases le_total b a with hba | hab
  · have hd : 0 ≤ a-b := sub_nonneg.mpr hba
    have hid : twoExpPoly a b =
        (a-b)^6 + 8*(a-b)^5*b + 28*(a-b)^4*b^2 + 46*(a-b)^3*b^3
          + 38*(a-b)^2*b^4 + 18*(a-b)*b^5 + 6*b^6 := by
      unfold twoExpPoly
      ring
    rw [hid]
    positivity
  · rw [twoExpPoly_symm]
    have hd : 0 ≤ b-a := sub_nonneg.mpr hab
    have hid : twoExpPoly b a =
        (b-a)^6 + 8*(b-a)^5*a + 28*(b-a)^4*a^2 + 46*(b-a)^3*a^3
          + 38*(b-a)^2*a^4 + 18*(b-a)*a^5 + 6*a^6 := by
      unfold twoExpPoly
      ring
    rw [hid]
    positivity

noncomputable def quarticPoly (a b : ℝ) : ℝ :=
  a^4 + a^3*b - 3*a^2*b^2 + a*b^3 + b^4

theorem quarticPoly_symm (a b : ℝ) : quarticPoly a b = quarticPoly b a := by
  unfold quarticPoly
  ring

theorem quarticPoly_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ quarticPoly a b := by
  rcases le_total b a with hba | hab
  · have hd : 0 ≤ a-b := sub_nonneg.mpr hba
    have hid : quarticPoly a b =
        (a-b)^4 + 5*(a-b)^3*b + 6*(a-b)^2*b^2 + 2*(a-b)*b^3 + b^4 := by
      unfold quarticPoly
      ring
    rw [hid]
    positivity
  · rw [quarticPoly_symm]
    have hd : 0 ≤ b-a := sub_nonneg.mpr hab
    have hid : quarticPoly b a =
        (b-a)^4 + 5*(b-a)^3*a + 6*(b-a)^2*a^2 + 2*(b-a)*a^3 + a^4 := by
      unfold quarticPoly
      ring
    rw [hid]
    positivity

noncomputable def threeExpPoly (a b c : ℝ) : ℝ :=
  a^6 + 2*a^5*b + 2*a^5*c + 3*a^4*b^2 + 4*a^4*b*c + 3*a^4*c^2
    - 6*a^3*b^3 - 4*a^3*b^2*c - 4*a^3*b*c^2 - 6*a^3*c^3
    + 3*a^2*b^4 - 4*a^2*b^3*c - 3*a^2*b^2*c^2 - 4*a^2*b*c^3
    + 3*a^2*c^4 + 2*a*b^5 + 4*a*b^4*c - 4*a*b^3*c^2 - 4*a*b^2*c^3
    + 4*a*b*c^4 + 2*a*c^5 + b^6 + 2*b^5*c + 3*b^4*c^2 - 6*b^3*c^3
    + 3*b^2*c^4 + 2*b*c^5 + c^6

theorem threeExpPoly_swap12 (a b c : ℝ) :
    threeExpPoly a b c = threeExpPoly b a c := by
  unfold threeExpPoly
  ring

theorem threeExpPoly_swap23 (a b c : ℝ) :
    threeExpPoly a b c = threeExpPoly a c b := by
  unfold threeExpPoly
  ring

theorem threeExpPoly_ordered_nonneg (a b c : ℝ)
    (hc : 0 ≤ c) (hcb : c ≤ b) (hba : b ≤ a) :
    0 ≤ threeExpPoly a b c := by
  have hx : 0 ≤ a-b := sub_nonneg.mpr hba
  have hy : 0 ≤ b-c := sub_nonneg.mpr hcb
  have hid : threeExpPoly a b c =
      (a-b)^6 + 8*(a-b)^5*(b-c) + 10*(a-b)^5*c
      + 28*(a-b)^4*(b-c)^2 + 70*(a-b)^4*(b-c)*c + 45*(a-b)^4*c^2
      + 46*(a-b)^3*(b-c)^3 + 170*(a-b)^3*(b-c)^2*c
      + 210*(a-b)^3*(b-c)*c^2 + 80*(a-b)^3*c^3
      + 38*(a-b)^2*(b-c)^4 + 180*(a-b)^2*(b-c)^3*c
      + 315*(a-b)^2*(b-c)^2*c^2 + 220*(a-b)^2*(b-c)*c^3
      + 50*(a-b)^2*c^4 + 18*(a-b)*(b-c)^5 + 100*(a-b)*(b-c)^4*c
      + 210*(a-b)*(b-c)^3*c^2 + 180*(a-b)*(b-c)^2*c^3
      + 50*(a-b)*(b-c)*c^4 + 6*(b-c)^6 + 40*(b-c)^5*c
      + 105*(b-c)^4*c^2 + 120*(b-c)^3*c^3 + 50*(b-c)^2*c^4 := by
    unfold threeExpPoly
    ring
  rw [hid]
  positivity

theorem threeExpPoly_nonneg (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ threeExpPoly a b c := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · have h := threeExpPoly_ordered_nonneg c b a ha hab hbc
      unfold threeExpPoly at h ⊢
      nlinarith
    · rcases le_total a c with hac | hca
      · have h := threeExpPoly_ordered_nonneg b c a ha hac hcb
        unfold threeExpPoly at h ⊢
        nlinarith
      · have h := threeExpPoly_ordered_nonneg b a c hc hca hab
        unfold threeExpPoly at h ⊢
        nlinarith
  · rcases le_total a c with hac | hca
    · have h := threeExpPoly_ordered_nonneg c a b hb hba hac
      unfold threeExpPoly at h ⊢
      nlinarith
    · rcases le_total b c with hbc | hcb
      · have h := threeExpPoly_ordered_nonneg a c b hb hbc hca
        unfold threeExpPoly at h ⊢
        nlinarith
      · have h := threeExpPoly_ordered_nonneg a b c hc hcb hba
        exact h

/-- The only non-coefficientwise-positive Bernstein coefficient for canonical start one. -/
noncomputable def middlePoly (a b c : ℝ) : ℝ :=
  10*a^6 + 24*a^5*b + 24*a^5*c + 27*a^4*b^2 + 42*a^4*b*c + 27*a^4*c^2
    + 20*a^3*b^3 + 36*a^3*b^2*c + 36*a^3*b*c^2 + 20*a^3*c^3
    + 20*a^2*b^4 + 30*a^2*b^3*c + 34*a^2*b^2*c^2 + 30*a^2*b*c^3
    + 20*a^2*c^4 + 4*a*b^5 + 8*a*b^4*c - 8*a*b^3*c^2 - 8*a*b^2*c^3
    + 8*a*b*c^4 + 4*a*c^5 + b^6 + 2*b^5*c + 3*b^4*c^2 - 6*b^3*c^3
    + 3*b^2*c^4 + 2*b*c^5 + c^6

theorem middlePoly_nonneg (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ middlePoly a b c := by
  have hq := quarticPoly_nonneg b c hb hc
  have ht := twoExpPoly_nonneg b c hb hc
  have hid : middlePoly a b c =
      10*a^6 + 24*a^5*b + 24*a^5*c + 27*a^4*b^2 + 42*a^4*b*c + 27*a^4*c^2
      + 20*a^3*b^3 + 36*a^3*b^2*c + 36*a^3*b*c^2 + 20*a^3*c^3
      + 20*a^2*b^4 + 30*a^2*b^3*c + 34*a^2*b^2*c^2 + 30*a^2*b*c^3
      + 20*a^2*c^4 + 4*a*(b+c)*quarticPoly b c + twoExpPoly b c := by
    unfold middlePoly quarticPoly twoExpPoly
    ring
  rw [hid]
  positivity

noncomputable def B (a b c u : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, u*b, u*c; a, b, u*c; a, b, c]

noncomputable def z2 (a b c u : ℝ) (i : Fin 3) : ℝ :=
  (B a b c u).mulVec ((B a b c u).mulVec (fun _ => (1 : ℝ))) i

noncomputable def z3 (a b c u : ℝ) (i : Fin 3) : ℝ :=
  (B a b c u).mulVec ((B a b c u).mulVec
    ((B a b c u).mulVec (fun _ => (1 : ℝ)))) i

noncomputable def z4 (a b c u : ℝ) (i : Fin 3) : ℝ :=
  (B a b c u).mulVec ((B a b c u).mulVec
    ((B a b c u).mulVec ((B a b c u).mulVec (fun _ => (1 : ℝ))))) i

noncomputable def poly (a b c u : ℝ) (i : Fin 3) : ℝ :=
  10*z2 a b c u i*z4 a b c u i - 9*(z3 a b c u i)^2

set_option linter.flexible false in
theorem z2_nonneg (a b c u : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hu : 0 ≤ u) (i : Fin 3) : 0 ≤ z2 a b c u i := by
  fin_cases i <;>
    simp [z2, B, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> positivity

set_option linter.flexible false in
theorem z3_nonneg (a b c u : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hu : 0 ≤ u) (i : Fin 3) : 0 ≤ z3 a b c u i := by
  fin_cases i <;>
    simp [z3, B, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> positivity

set_option linter.flexible false in
theorem z4_nonneg (a b c u : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hu : 0 ≤ u) (i : Fin 3) : 0 ≤ z4 a b c u i := by
  fin_cases i <;>
    simp [z4, B, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> positivity

set_option maxHeartbeats 1500000 in
-- Expanding the three degree-six Bernstein identities requires extra normalization time.
/-- Bernstein certificate for all three deterministic starts of the normalized canonical
three-state matrix. -/
theorem poly_nonneg (a b c u : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (i : Fin 3) :
    0 ≤ poly a b c u i := by
  have hu' : 0 ≤ 1-u := sub_nonneg.mpr hu1
  fin_cases i
  · have hm := middlePoly_nonneg a b c ha hb hc
    have hdecomp : 10*poly a b c u 0 =
        10*a^6*(1-u)^5
      + 10*(5*a^4 + 6*a^3*b + 6*a^3*c + 4*a^2*b^2 + 4*a^2*b*c + 4*a^2*c^2
          + 2*a*b^3 + 2*a*b^2*c + 2*a*b*c^2 + 2*a*c^3
          + 10*b^4 + 10*b^3*c + 10*b^2*c^2 + 10*b*c^3 + 10*c^4)
          *a^2*u*(1-u)^4
      + 10*middlePoly a b c*u^2*(1-u)^3
      + 10*(a+b+c)^2*(10*a^4 + 16*a^3*b + 16*a^3*c + 15*a^2*b^2
          + 18*a^2*b*c + 15*a^2*c^2 + 8*a*b^3 + 12*a*b^2*c + 12*a*b*c^2
          + 8*a*c^3 + 3*b^4 + 4*b^3*c + 6*b^2*c^2 + 4*b*c^3 + 3*c^4)
          *u^3*(1-u)^2
      + 10*(a+b+c)^4*(5*a^2 + 4*a*b + 4*a*c + 3*b^2 + 2*b*c + 3*c^2)
          *u^4*(1-u)
      + 10*(a+b+c)^6*u^5 := by
      unfold poly z2 z3 z4 B middlePoly
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
    have hscaled : 0 ≤ 10*poly a b c u 0 := by
      rw [hdecomp]
      positivity
    have hmain : 0 ≤ poly a b c u 0 := by nlinarith [hscaled]
    simpa only [Fin.zero_eta] using hmain
  · have ht := twoExpPoly_nonneg a b ha hb
    have hdecomp : 10*poly a b c u 1 =
        10*twoExpPoly a b*(1-u)^4
      + 20*(2*a^6 + 6*a^5*b + 3*a^5*c + 10*a^4*b^2 + 7*a^4*b*c + 2*a^4*c^2
          + 7*a^3*b^3 + 10*a^3*b^2*c + 4*a^3*b*c^2 + a^3*c^3
          + 10*a^2*b^4 + 10*a^2*b^3*c + 19*a^2*b^2*c^2 + 11*a^2*b*c^3
          + 5*a^2*c^4 + 6*a*b^5 + 7*a*b^4*c + 4*a*b^3*c^2 + 11*a*b^2*c^3
          + 5*a*b*c^4 + 2*b^6 + 3*b^5*c + 2*b^4*c^2 + b^3*c^3 + 5*b^2*c^4)
          *u*(1-u)^3
      + 10*(a+b+c)^2*(6*a^4 + 12*a^3*b + 6*a^3*c + 16*a^2*b^2
          + 10*a^2*b*c + 5*a^2*c^2 + 12*a*b^3 + 10*a*b^2*c + 6*a*b*c^2
          + 2*a*c^3 + 6*b^4 + 6*b^3*c + 5*b^2*c^2 + 2*b*c^3 + c^4)
          *u^2*(1-u)^2
      + 20*(a+b+c)^4*(2*a^2 + 2*a*b + a*c + 2*b^2 + b*c + c^2)*u^3*(1-u)
      + 10*(a+b+c)^6*u^4 := by
      unfold poly z2 z3 z4 B twoExpPoly
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
    have hscaled : 0 ≤ 10*poly a b c u 1 := by
      rw [hdecomp]
      positivity
    have hmain : 0 ≤ poly a b c u 1 := by nlinarith [hscaled]
    simpa only [Fin.mk_one] using hmain
  · have ht := threeExpPoly_nonneg a b c ha hb hc
    have hdecomp : 10*poly a b c u 2 =
        10*threeExpPoly a b c*(1-u)^4
      + 20*(2*a^6 + 6*a^5*b + 6*a^5*c + 10*a^4*b^2 + 16*a^4*b*c + 10*a^4*c^2
          + 7*a^3*b^3 + 19*a^3*b^2*c + 19*a^3*b*c^2 + 7*a^3*c^3
          + 10*a^2*b^4 + 19*a^2*b^3*c + 30*a^2*b^2*c^2 + 19*a^2*b*c^3
          + 10*a^2*c^4 + 6*a*b^5 + 16*a*b^4*c + 19*a*b^3*c^2 + 19*a*b^2*c^3
          + 16*a*b*c^4 + 6*a*c^5 + 2*b^6 + 6*b^5*c + 10*b^4*c^2
          + 7*b^3*c^3 + 10*b^2*c^4 + 6*b*c^5 + 2*c^6)*u*(1-u)^3
      + 20*(a+b+c)^2*(3*a^4 + 6*a^3*b + 6*a^3*c + 8*a^2*b^2
          + 11*a^2*b*c + 8*a^2*c^2 + 6*a*b^3 + 11*a*b^2*c + 11*a*b*c^2
          + 6*a*c^3 + 3*b^4 + 6*b^3*c + 8*b^2*c^2 + 6*b*c^3 + 3*c^4)
          *u^2*(1-u)^2
      + 40*(a+b+c)^4*(a^2 + a*b + a*c + b^2 + b*c + c^2)*u^3*(1-u)
      + 10*(a+b+c)^6*u^4 := by
      unfold poly z2 z3 z4 B threeExpPoly
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
    have hscaled : 0 ≤ 10*poly a b c u 2 := by
      rw [hdecomp]
      positivity
    have hmain : 0 ≤ poly a b c u 2 := by nlinarith [hscaled]
    change 0 ≤ poly a b c u (2 : Fin 3)
    exact hmain

noncomputable def scaledB (t a b c u : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => t * B a b c u i j

theorem scaledB_z2 (t a b c u : ℝ) (i : Fin 3) :
    (scaledB t a b c u).mulVec
        ((scaledB t a b c u).mulVec (fun _ => (1 : ℝ))) i =
      t^2*z2 a b c u i := by
  fin_cases i <;>
    simp [scaledB, B, z2, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem scaledB_z3 (t a b c u : ℝ) (i : Fin 3) :
    (scaledB t a b c u).mulVec ((scaledB t a b c u).mulVec
        ((scaledB t a b c u).mulVec (fun _ => (1 : ℝ)))) i =
      t^3*z3 a b c u i := by
  fin_cases i <;>
    simp [scaledB, B, z3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem scaledB_z4 (t a b c u : ℝ) (i : Fin 3) :
    (scaledB t a b c u).mulVec ((scaledB t a b c u).mulVec
        ((scaledB t a b c u).mulVec
          ((scaledB t a b c u).mulVec (fun _ => (1 : ℝ))))) i =
      t^4*z4 a b c u i := by
  fin_cases i <;>
    simp [scaledB, B, z4, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem scaledB_k3 (t a b c u : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (i : Fin 3) :
    9*((scaledB t a b c u).mulVec ((scaledB t a b c u).mulVec
        ((scaledB t a b c u).mulVec (fun _ => (1 : ℝ)))) i)^2 ≤
      10*((scaledB t a b c u).mulVec
        ((scaledB t a b c u).mulVec (fun _ => (1 : ℝ))) i) *
        ((scaledB t a b c u).mulVec ((scaledB t a b c u).mulVec
          ((scaledB t a b c u).mulVec
            ((scaledB t a b c u).mulVec (fun _ => (1 : ℝ))))) i) := by
  rw [scaledB_z2, scaledB_z3, scaledB_z4]
  have hp := poly_nonneg a b c u ha hb hc hu0 hu1 i
  unfold poly at hp
  have ht6 : 0 ≤ t^6 := by positivity
  nlinarith [mul_nonneg ht6 hp]

theorem canonical_inv_eq_scaledB (x1 x2 x3 x13 : ℝ)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3) (hx13lt : x13 < x1) :
    (SSP.Canonical.negA x1 x2 x3 x13)⁻¹ =
      scaledB (1/(1-x13/x1)) (1/x1) (1/x2) (1/x3) (x13/x1) := by
  let A := SSP.Canonical.negA x1 x2 x3 x13
  have h1u : 1-x13/x1 ≠ 0 := by
    have : x13/x1 < 1 := (div_lt_one hx1).mpr hx13lt
    linarith
  have hdiff : x1-x13 ≠ 0 := by linarith
  have hAunit : IsUnit A.det := by
    dsimp [A]
    exact SSP.Canonical.negA_isUnit_det x1 x2 x3 x13
      (ne_of_gt (SSP.Canonical.canDen_pos x1 x2 x3 x13 hx1 hx2 hx3 hx13lt))
  have hmul : A * scaledB (1/(1-x13/x1)) (1/x1) (1/x2) (1/x3) (x13/x1) = 1 := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [A, SSP.Canonical.negA, scaledB, B, Matrix.mul_apply, Fin.sum_univ_three] <;>
      field_simp [hx1.ne', hx2.ne', hx3.ne', h1u, hdiff] <;> ring
  change A⁻¹ = _
  calc
    A⁻¹ = A⁻¹ * 1 := by rw [Matrix.mul_one]
    _ = A⁻¹ * (A * scaledB (1/(1-x13/x1)) (1/x1) (1/x2) (1/x3) (x13/x1)) := by
      rw [hmul]
    _ = (A⁻¹ * A) * scaledB (1/(1-x13/x1)) (1/x1) (1/x2) (1/x3) (x13/x1) := by
      rw [Matrix.mul_assoc]
    _ = 1 * scaledB (1/(1-x13/x1)) (1/x1) (1/x2) (1/x3) (x13/x1) := by
      rw [Matrix.nonsing_inv_mul A hAunit]
    _ = scaledB (1/(1-x13/x1)) (1/x1) (1/x2) (1/x3) (x13/x1) := by
      rw [Matrix.one_mul]

/-- The `k = 3`, `s = 3` inequality for each deterministic start of the He--Zhang
canonical matrix. -/
theorem canonical_matrix_k3 (x1 x2 x3 x13 : ℝ)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3)
    (hx13 : 0 ≤ x13) (hx13lt : x13 < x1) (i : Fin 3) :
    let A := SSP.Canonical.negA x1 x2 x3 x13
    9*(A⁻¹.mulVec (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ)))) i)^2 ≤
      10*(A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ))) i) *
        (A⁻¹.mulVec (A⁻¹.mulVec (A⁻¹.mulVec
          (A⁻¹.mulVec (fun _ => (1 : ℝ))))) i) := by
  dsimp only
  let a := 1/x1
  let b := 1/x2
  let c := 1/x3
  let u := x13/x1
  let t := 1/(1-u)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; exact (div_le_one hx1).mpr hx13lt.le
  have h1u : 1-u ≠ 0 := by
    have : u < 1 := by dsimp [u]; exact (div_lt_one hx1).mpr hx13lt
    linarith
  let A := SSP.Canonical.negA x1 x2 x3 x13
  have hinv : A⁻¹ = scaledB t a b c u := by
    simpa [A, a, b, c, u, t] using
      canonical_inv_eq_scaledB x1 x2 x3 x13 hx1 hx2 hx3 hx13lt
  rw [hinv]
  exact scaledB_k3 t a b c u ha hb hc hu0 hu1 i

theorem canonical_z234_nonneg (x1 x2 x3 x13 : ℝ)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3)
    (hx13 : 0 ≤ x13) (hx13lt : x13 < x1) (i : Fin 3) :
    let A := SSP.Canonical.negA x1 x2 x3 x13
    0 ≤ A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ))) i ∧
    0 ≤ A⁻¹.mulVec (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ)))) i ∧
    0 ≤ A⁻¹.mulVec (A⁻¹.mulVec (A⁻¹.mulVec
      (A⁻¹.mulVec (fun _ => (1 : ℝ))))) i := by
  dsimp only
  let a := 1/x1
  let b := 1/x2
  let c := 1/x3
  let u := x13/x1
  let t := 1/(1-u)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have ht : 0 ≤ t := by
    have hu1 : u < 1 := by dsimp [u]; exact (div_lt_one hx1).mpr hx13lt
    dsimp [t]
    positivity
  have hinv : (SSP.Canonical.negA x1 x2 x3 x13)⁻¹ = scaledB t a b c u := by
    simpa [a, b, c, u, t] using
      canonical_inv_eq_scaledB x1 x2 x3 x13 hx1 hx2 hx3 hx13lt
  rw [hinv, scaledB_z2, scaledB_z3, scaledB_z4]
  exact ⟨mul_nonneg (sq_nonneg t) (z2_nonneg a b c u ha hb hc hu i),
    mul_nonneg (pow_nonneg ht 3) (z3_nonneg a b c u ha hb hc hu i),
    mul_nonneg (pow_nonneg ht 4) (z4_nonneg a b c u ha hb hc hu i)⟩

end SSP.K3S3Canonical

namespace SSP.K2Concrete

/-- Conditional only on a He--Zhang similarity certificate, every deterministic three-state
law satisfies the `k = 3` hierarchy inequality. -/
theorem transientStageBoundK3_three_of_similarity (X : TransientStart 3)
    (c : TransientOrderThreeSimilarityRepresentation X) :
    K3StageBound 3 (transientMoment2 3 X) (transientMoment3 3 X)
      (transientMoment4 3 X) := by
  let A := SSP.Canonical.negA c.x1 c.x2 c.x3 c.x13
  let v2 : Fin 3 → ℝ := fun i =>
    A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ))) i
  let v3 : Fin 3 → ℝ := fun i =>
    A⁻¹.mulVec (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ)))) i
  let v4 : Fin 3 → ℝ := fun i =>
    A⁻¹.mulVec (A⁻¹.mulVec (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ))))) i
  have h2 :
      ((1-X.Q)⁻¹.mulVec ((1-X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) X.i =
        ∑ i, c.pi i * v2 i := by
    have h := similarity_resolvent_power_at_start X c 2
    simpa [v2, A, pow_two, Matrix.mulVec_mulVec] using h
  have h3 :
      ((1-X.Q)⁻¹.mulVec ((1-X.Q)⁻¹.mulVec
        ((1-X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) X.i =
        ∑ i, c.pi i * v3 i := by
    have h := similarity_resolvent_power_at_start X c 3
    simpa [v3, A, pow_succ, Matrix.mulVec_mulVec, Matrix.mul_assoc] using h
  have h4 :
      ((1-X.Q)⁻¹.mulVec ((1-X.Q)⁻¹.mulVec
        ((1-X.Q)⁻¹.mulVec ((1-X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))))) X.i =
        ∑ i, c.pi i * v4 i := by
    have h := similarity_resolvent_power_at_start X c 4
    simpa [v4, A, pow_succ, Matrix.mulVec_mulVec, Matrix.mul_assoc] using h
  have hnonneg : ∀ i, 0 ≤ v2 i ∧ 0 ≤ v3 i ∧ 0 ≤ v4 i := by
    intro i
    exact SSP.K3S3Canonical.canonical_z234_nonneg c.x1 c.x2 c.x3 c.x13
      c.x1_pos c.x2_pos c.x3_pos c.x13_nonneg c.x13_lt i
  have hcomp : ∀ i, (9/10 : ℝ)*(v3 i)^2 ≤ v2 i*v4 i := by
    intro i
    have h := SSP.K3S3Canonical.canonical_matrix_k3 c.x1 c.x2 c.x3 c.x13
      c.x1_pos c.x2_pos c.x3_pos c.x13_nonneg c.x13_lt i
    dsimp only at h
    change 9*(v3 i)^2 ≤ 10*(v2 i)*(v4 i) at h
    nlinarith
  have hmix := SSP.Chain.mixture_closure_sq (Finset.univ : Finset (Fin 3)) c.pi
    v2 v3 v4 (9/10 : ℝ) (by norm_num) (fun i _ => c.pi_nonneg i)
    (fun i _ => (hnonneg i).1) (fun i _ => (hnonneg i).2.2)
    (fun i _ => (hnonneg i).2.1) (fun i _ => hcomp i)
  unfold K3StageBound transientMoment2 transientMoment3 transientMoment4
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
  rw [h2, h3, h4]
  norm_num at hmix ⊢
  nlinarith

/-- The `k = 3`, `s = 3` deterministic theorem, assuming the standard He--Zhang order-three
representation theorem. -/
theorem transientStageBoundK3_three
    (hrep : HeZhangOrderThreeRepresentationTheorem) (X : TransientStart 3) :
    K3StageBound 3 (transientMoment2 3 X) (transientMoment3 3 X)
      (transientMoment4 3 X) := by
  rcases hrep X with ⟨c⟩
  exact transientStageBoundK3_three_of_similarity X c

/-- The corresponding theorem for an arbitrary subprobability initial vector. -/
theorem transientInitialStageBoundK3_three
    (hrep : HeZhangOrderThreeRepresentationTheorem) (X : TransientInitial 3) :
    K3StageBound 3 (transientInitialMoment2 3 X) (transientInitialMoment3 3 X)
      (transientInitialMoment4 3 X) := by
  have hmix := SSP.Chain.mixture_closure_sq (Finset.univ : Finset (Fin 3)) X.weight
    (fun i => transientMoment2 3 (X.component i))
    (fun i => transientMoment3 3 (X.component i))
    (fun i => transientMoment4 3 (X.component i)) (6/5 : ℝ)
    (by norm_num) (fun i _ => X.weight_nonneg i)
    (fun i _ => transientMoment2_nonneg (X.component i))
    (fun i _ => transientMoment4_nonneg (X.component i))
    (fun i _ => transientMoment3_nonneg (X.component i))
    (fun i _ => by
      have h := transientStageBoundK3_three hrep (X.component i)
      unfold K3StageBound at h
      norm_num at h ⊢
      nlinarith)
  unfold K3StageBound transientInitialMoment2 transientInitialMoment3
    transientInitialMoment4
  norm_num at hmix ⊢
  nlinarith

end SSP.K2Concrete
