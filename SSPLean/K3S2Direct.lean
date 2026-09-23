import SSPLean.K2S3Direct

/-!
# The `k = 3`, two-state inequality

For a two-state transient chain, normalize its inverse rate matrix to
`B = !![x, u; x*v, 1]`, where `x > 0` and `u,v ∈ [0,1]`.  This file proves directly that
`16 z₂ z₄ ≥ 15 z₃²`, where `zᵣ` is the first coordinate of `Bᵣ 1`.  In raw moments
this is `4 m₂ m₄ ≥ 5 m₃²`, the conjectured `k = 3`, `s = 2` inequality.
-/

open Finset

set_option autoImplicit false

namespace SSP.K3S2Direct

noncomputable def z2 (x u v : ℝ) : ℝ :=
  u*v*x + u*x + u + x^2

noncomputable def z3 (x u v : ℝ) : ℝ :=
  u^2*v*x + 2*u*v*x^2 + u*v*x + u*x^2 + u*x + u + x^3

noncomputable def z4 (x u v : ℝ) : ℝ :=
  u^2*v^2*x^2 + 2*u^2*v*x^2 + 2*u^2*v*x + 3*u*v*x^3
    + 2*u*v*x^2 + u*v*x + u*x^3 + u*x^2 + u*x + u + x^4

noncomputable def poly (x u v : ℝ) : ℝ :=
  16*z2 x u v*z4 x u v - 15*(z3 x u v)^2

/-- Six elementary univariate certificates used by the Bernstein expansion. -/
theorem coefficient_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 2*x^4+x^3+x^2-7*x+8 ∧
    0 ≤ 6*x^4+5*x^3+4*x^2-13*x+24 ∧
    0 ≤ 6*x^4+7*x^3+5*x^2-5*x+24 ∧
    0 ≤ 6*x^6+6*x^5+7*x^4-40*x^3+35*x^2+2*x+1 ∧
    0 ≤ 18*x^6+30*x^5+33*x^4-34*x^3+79*x^2+8*x+3 ∧
    0 ≤ 2*x^6+3*x^5+4*x^4-19*x^3+11*x^2+2*x+1 := by
  have hs : 0 ≤ (x-1)^2 := sq_nonneg (x-1)
  have h1 : 36*(2*x^4+x^3+x^2-7*x+8) =
      18*(x-1)^2*(9+4*x+x^2) + 126 + 54*x^4 := by ring
  have h2 : 3*(6*x^4+5*x^3+4*x^2-13*x+24) =
      (x-1)^2*(22+5*x) + 50 + 10*x^3 + 18*x^4 := by ring
  have h3 : 2*(6*x^4+7*x^3+5*x^2-5*x+24) =
      5*(x-1)^2 + 43 + 5*x^2 + 14*x^3 + 12*x^4 := by ring
  have h4 : 6*x^6+6*x^5+7*x^4-40*x^3+35*x^2+2*x+1 =
      (x-1)^2*(25*x^2+10*x^3+2*x^4) + 1+2*x+10*x^2+4*x^6 := by ring
  have h5 : 18*x^6+30*x^5+33*x^4-34*x^3+79*x^2+8*x+3 =
      (x-1)^2*(17*x^2) + 3+8*x+62*x^2+16*x^4+30*x^5+18*x^6 := by ring
  have h6 : 5*(2*x^6+3*x^5+4*x^4-19*x^3+11*x^2+2*x+1) =
      (x-1)^2*(2*x+59*x^2+21*x^3+3*x^4) + 5+8*x+7*x^6 := by ring
  constructor
  · nlinarith [h1]
  constructor
  · nlinarith [h2]
  constructor
  · nlinarith [h3]
  constructor
  · rw [h4]
    positivity
  constructor
  · rw [h5]
    positivity
  · have hrhs : 0 ≤
        (x-1)^2*(2*x+59*x^2+21*x^3+3*x^4) + 5+8*x+7*x^6 := by positivity
    nlinarith [h6]

/-- Bernstein-basis certificate for the normalized two-state polynomial. -/
theorem poly_nonneg (x u v : ℝ) (hx : 0 ≤ x)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ poly x u v := by
  rcases coefficient_nonneg x hx with ⟨h10, h11, h12, h20, h21, h30⟩
  have hu' : 0 ≤ 1-u := sub_nonneg.mpr hu1
  have hv' : 0 ≤ 1-v := sub_nonneg.mpr hv1
  have hdecomp : 18*poly x u v =
      18*x^6*(1-u)^4*(1-v)^3
    + 54*x^6*(1-u)^4*v*(1-v)^2
    + 54*x^6*(1-u)^4*v^2*(1-v)
    + 18*x^6*(1-u)^4*v^3
    + 36*x^2*(2*x^4+x^3+x^2-7*x+8)*u*(1-u)^3*(1-v)^3
    + 36*x^2*(6*x^4+5*x^3+4*x^2-13*x+24)*u*(1-u)^3*v*(1-v)^2
    + 36*x^2*(6*x^4+7*x^3+5*x^2-5*x+24)*u*(1-u)^3*v^2*(1-v)
    + 36*x^2*(2*x^4+3*x^3+2*x^2+x+8)*u*(1-u)^3*v^3
    + 18*(6*x^6+6*x^5+7*x^4-40*x^3+35*x^2+2*x+1)*u^2*(1-u)^2*(1-v)^3
    + 18*(18*x^6+30*x^5+33*x^4-34*x^3+79*x^2+8*x+3)*u^2*(1-u)^2*v*(1-v)^2
    + 18*(18*x^6+42*x^5+49*x^4+24*x^3+54*x^2+10*x+3)*u^2*(1-u)^2*v^2*(1-v)
    + 18*(x+1)^2*(3*x^2+1)*(2*x^2+2*x+1)*u^2*(1-u)^2*v^3
    + 36*(2*x^6+3*x^5+4*x^4-19*x^3+11*x^2+2*x+1)*u^3*(1-u)*(1-v)^3
    + 108*(2*x^6+5*x^5+7*x^4+2*x^3+8*x^2+3*x+1)*u^3*(1-u)*v*(1-v)^2
    + 36*(x+1)^2*(6*x^4+9*x^3+10*x^2+6*x+3)*u^3*(1-u)*v^2*(1-v)
    + 36*(x+1)^4*(2*x^2+x+1)*u^3*(1-u)*v^3
    + 18*(x-1)^2*(x^4+4*x^3+10*x^2+4*x+1)*u^4*(1-v)^3
    + 18*(x+1)^2*(x^2+1)*(3*x^2+4*x+3)*u^4*v*(1-v)^2
    + 18*(x+1)^4*(3*x^2+2*x+3)*u^4*v^2*(1-v)
    + 18*(x+1)^6*u^4*v^3 := by
    unfold poly z2 z3 z4
    ring
  have hscaled : 0 ≤ 18*poly x u v := by
    rw [hdecomp]
    positivity
  nlinarith

end SSP.K3S2Direct

namespace SSP.K2Concrete

/-- Fourth raw resolvent moment in the full transient model. -/
noncomputable def transientMoment4 (s : ℕ) (X : TransientStart s) : ℝ :=
  24 * ((1-X.Q)⁻¹.mulVec ((1-X.Q)⁻¹.mulVec
    ((1-X.Q)⁻¹.mulVec ((1-X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))))) X.i

theorem transientMoment4_nonneg {s : ℕ} (X : TransientStart s) :
    0 ≤ transientMoment4 s X := by
  unfold transientMoment4 Matrix.mulVec dotProduct
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (inverse_one_sub_nonneg X.Q X.hQ X.hrow X.hu X.i i)
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (inverse_one_sub_nonneg X.Q X.hQ X.hrow X.hu i j)
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (inverse_one_sub_nonneg X.Q X.hQ X.hrow X.hu j k)
  exact Finset.sum_nonneg fun l _ =>
    mul_nonneg (inverse_one_sub_nonneg X.Q X.hQ X.hrow X.hu k l) zero_le_one

noncomputable def transientInitialMoment4 (s : ℕ) (X : TransientInitial s) : ℝ :=
  ∑ i, X.weight i * transientMoment4 s (X.component i)

/-- The `k = 3` hierarchy assertion at phase order `s`. -/
def K3StageBound (s : ℕ) (m₂ m₃ m₄ : ℝ) : Prop :=
  (s+3)*m₃^2 ≤ (s+2)*m₂*m₄

/-- Scalar two-cycle calculation for `k = 3`. -/
theorem twoCycleK3Closed (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hδ : a * b * (1 - u * v) ≠ 0) :
    let δ := a*b*(1-u*v)
    let z2 := (b*(b+a*u) + a*u*(b*v+a))/δ^2
    let z3 := (b*(b*(b+a*u) + a*u*(b*v+a))
      + a*u*(b*v*(b+a*u) + a*(b*v+a)))/δ^3
    let z4 := (a^4*u + 2*a^3*b*u^2*v + a^3*b*u*v + a^3*b*u
      + a^2*b^2*u^2*v^2 + 2*a^2*b^2*u^2*v + 2*a^2*b^2*u*v
      + a^2*b^2*u + 3*a*b^3*u*v + a*b^3*u + b^4)/δ^4
    15*z3^2 ≤ 16*z2*z4 := by
  dsimp only
  have hx : 0 ≤ b/a := div_nonneg hb.le ha.le
  have hp := SSP.K3S2Direct.poly_nonneg (b/a) u v hx hu0 hu1 hv0 hv1
  have hpoly :
      a^6 * SSP.K3S2Direct.poly (b/a) u v =
        a^6*u^2 + 2*a^5*b*u^3*v + 2*a^5*b*u^2*v + 2*a^5*b*u^2
        - 15*a^4*b^2*u^4*v^2 + 18*a^4*b^2*u^3*v^2 + 34*a^4*b^2*u^3*v
        + a^4*b^2*u^2*v^2 - 26*a^4*b^2*u^2*v - 13*a^4*b^2*u^2
        + 16*a^4*b^2*u + 16*a^3*b^3*u^3*v^3 - 12*a^3*b^3*u^3*v^2
        + 2*a^3*b^3*u^3*v - 28*a^3*b^3*u^2*v^2 + 38*a^3*b^3*u^2*v
        + 2*a^3*b^3*u^2 + 16*a^3*b^3*u*v - 14*a^3*b^3*u
        + 4*a^2*b^4*u^2*v^2 + 6*a^2*b^4*u^2*v + a^2*b^4*u^2
        + 2*a^2*b^4*u*v + 2*a^2*b^4*u + 4*a*b^5*u*v + 2*a*b^5*u + b^6 := by
    unfold SSP.K3S2Direct.poly SSP.K3S2Direct.z2 SSP.K3S2Direct.z3
      SSP.K3S2Direct.z4
    field_simp [ha.ne']
    ring
  have hnum : 0 ≤
        a^6*u^2 + 2*a^5*b*u^3*v + 2*a^5*b*u^2*v + 2*a^5*b*u^2
        - 15*a^4*b^2*u^4*v^2 + 18*a^4*b^2*u^3*v^2 + 34*a^4*b^2*u^3*v
        + a^4*b^2*u^2*v^2 - 26*a^4*b^2*u^2*v - 13*a^4*b^2*u^2
        + 16*a^4*b^2*u + 16*a^3*b^3*u^3*v^3 - 12*a^3*b^3*u^3*v^2
        + 2*a^3*b^3*u^3*v - 28*a^3*b^3*u^2*v^2 + 38*a^3*b^3*u^2*v
        + 2*a^3*b^3*u^2 + 16*a^3*b^3*u*v - 14*a^3*b^3*u
        + 4*a^2*b^4*u^2*v^2 + 6*a^2*b^4*u^2*v + a^2*b^4*u^2
        + 2*a^2*b^4*u*v + 2*a^2*b^4*u + 4*a*b^5*u*v + 2*a*b^5*u + b^6 := by
    rw [← hpoly]
    exact mul_nonneg (by positivity) hp
  have h1uv : 1-u*v ≠ 0 := by
    intro h
    apply hδ
    rw [h]
    ring
  have hδpos : 0 < a*b*(1-u*v) := by
    have huv : u*v ≤ 1 := calc
      u*v ≤ u*1 := mul_le_mul_of_nonneg_left hv1 hu0
      _ ≤ 1 := by simpa using hu1
    exact mul_pos (mul_pos ha hb)
      (lt_of_le_of_ne (sub_nonneg.mpr huv) h1uv.symm)
  have hid : (a*b*(1-u*v))^6 *
      (16*((b*(b+a*u) + a*u*(b*v+a))/(a*b*(1-u*v))^2) *
        ((a^4*u + 2*a^3*b*u^2*v + a^3*b*u*v + a^3*b*u
          + a^2*b^2*u^2*v^2 + 2*a^2*b^2*u^2*v + 2*a^2*b^2*u*v
          + a^2*b^2*u + 3*a*b^3*u*v + a*b^3*u + b^4)/(a*b*(1-u*v))^4)
      - 15*((b*(b*(b+a*u) + a*u*(b*v+a))
          + a*u*(b*v*(b+a*u) + a*(b*v+a)))/(a*b*(1-u*v))^3)^2) =
      a^6*u^2 + 2*a^5*b*u^3*v + 2*a^5*b*u^2*v + 2*a^5*b*u^2
        - 15*a^4*b^2*u^4*v^2 + 18*a^4*b^2*u^3*v^2 + 34*a^4*b^2*u^3*v
        + a^4*b^2*u^2*v^2 - 26*a^4*b^2*u^2*v - 13*a^4*b^2*u^2
        + 16*a^4*b^2*u + 16*a^3*b^3*u^3*v^3 - 12*a^3*b^3*u^3*v^2
        + 2*a^3*b^3*u^3*v - 28*a^3*b^3*u^2*v^2 + 38*a^3*b^3*u^2*v
        + 2*a^3*b^3*u^2 + 16*a^3*b^3*u*v - 14*a^3*b^3*u
        + 4*a^2*b^4*u^2*v^2 + 6*a^2*b^4*u^2*v + a^2*b^4*u^2
        + 2*a^2*b^4*u*v + 2*a^2*b^4*u + 4*a*b^5*u*v + 2*a*b^5*u + b^6 := by
    field_simp [h1uv, ha.ne', hb.ne']
    ring
  have hscaled : 0 ≤ (a*b*(1-u*v))^6 *
      (16*((b*(b+a*u) + a*u*(b*v+a))/(a*b*(1-u*v))^2) *
        ((a^4*u + 2*a^3*b*u^2*v + a^3*b*u*v + a^3*b*u
          + a^2*b^2*u^2*v^2 + 2*a^2*b^2*u^2*v + 2*a^2*b^2*u*v
          + a^2*b^2*u + 3*a*b^3*u*v + a*b^3*u + b^4)/(a*b*(1-u*v))^4)
      - 15*((b*(b*(b+a*u) + a*u*(b*v+a))
          + a*u*(b*v*(b+a*u) + a*(b*v+a)))/(a*b*(1-u*v))^3)^2) := by
    rw [hid]
    exact hnum
  have hgap : 0 ≤
      16*((b*(b+a*u) + a*u*(b*v+a))/(a*b*(1-u*v))^2) *
        ((a^4*u + 2*a^3*b*u^2*v + a^3*b*u*v + a^3*b*u
          + a^2*b^2*u^2*v^2 + 2*a^2*b^2*u^2*v + 2*a^2*b^2*u*v
          + a^2*b^2*u + 3*a*b^3*u*v + a*b^3*u + b^4)/(a*b*(1-u*v))^4)
      - 15*((b*(b*(b+a*u) + a*u*(b*v+a))
          + a*u*(b*v*(b+a*u) + a*(b*v+a)))/(a*b*(1-u*v))^3)^2 :=
    (mul_nonneg_iff_of_pos_left (pow_pos hδpos 6)).mp hscaled
  linarith

set_option maxHeartbeats 1500000 in
-- Four symbolic powers of a general `2 × 2` inverse require extra normalization time.
/-- Resolvent form of the `k = 3`, `s = 2` inequality, for either starting state. -/
theorem twoCycleMatrixK3 (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hδ : a * b * (1 - u * v) ≠ 0) (i : Fin 2) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![a, -a*u; -b*v, b]
    let N := A⁻¹
    15*(N.mulVec (N.mulVec (N.mulVec (fun _ => (1 : ℝ)))) i)^2 ≤
      16*(N.mulVec (N.mulVec (fun _ => (1 : ℝ))) i) *
        (N.mulVec (N.mulVec (N.mulVec (N.mulVec (fun _ => (1 : ℝ))))) i) := by
  dsimp only
  have hn :
      (!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ =
        !![b/(a*b*(1-u*v)), (a*u)/(a*b*(1-u*v));
            (b*v)/(a*b*(1-u*v)), a/(a*b*(1-u*v))] := by
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two,
        Ring.inverse_eq_inv] <;> field_simp [hδ]
  have hδ' : b*a*(1-v*u) ≠ 0 := by
    intro h
    apply hδ
    nlinarith
  fin_cases i
  · have hz2 :
        ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
          ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
            (fun _ => (1 : ℝ)))) 0 =
          (b*(b+a*u)+a*u*(b*v+a))/(a*b*(1-u*v))^2 := by
      rw [hn]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp [hδ]
    have hz3 :
        ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
          ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
            ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
              (fun _ => (1 : ℝ))))) 0 =
          (b*(b*(b+a*u)+a*u*(b*v+a))+a*u*(b*v*(b+a*u)+a*(b*v+a))) /
            (a*b*(1-u*v))^3 := by
      rw [hn]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp [hδ]
    have hz4 :
        ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
          ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
            ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
              ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
                (fun _ => (1 : ℝ)))))) 0 =
          (a^4*u + 2*a^3*b*u^2*v + a^3*b*u*v + a^3*b*u
            + a^2*b^2*u^2*v^2 + 2*a^2*b^2*u^2*v + 2*a^2*b^2*u*v
            + a^2*b^2*u + 3*a*b^3*u*v + a*b^3*u + b^4)/(a*b*(1-u*v))^4 := by
      rw [hn]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp [hδ]
      ring
    simp only [Fin.zero_eta]
    rw [hz2, hz3, hz4]
    exact twoCycleK3Closed a b u v ha hb hu0 hu1 hv0 hv1 hδ
  · have hz2 :
        ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
          ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
            (fun _ => (1 : ℝ)))) 1 =
          (a*(a+b*v)+b*v*(a*u+b))/(b*a*(1-v*u))^2 := by
      rw [hn]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp [hδ, hδ']
      ring
    have hz3 :
        ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
          ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
            ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
              (fun _ => (1 : ℝ))))) 1 =
          (a*(a*(a+b*v)+b*v*(a*u+b))+b*v*(a*u*(a+b*v)+b*(a*u+b))) /
            (b*a*(1-v*u))^3 := by
      rw [hn]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp [hδ, hδ']
      ring
    have hz4 :
        ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
          ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
            ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
              ((!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹.mulVec
                (fun _ => (1 : ℝ)))))) 1 =
          (b^4*v + 2*b^3*a*v^2*u + b^3*a*v*u + b^3*a*v
            + b^2*a^2*v^2*u^2 + 2*b^2*a^2*v^2*u + 2*b^2*a^2*v*u
            + b^2*a^2*v + 3*b*a^3*v*u + b*a^3*v + a^4)/(b*a*(1-v*u))^4 := by
      rw [hn]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp [hδ, hδ']
      ring
    simp only [Fin.mk_one]
    rw [hz2, hz3, hz4]
    exact twoCycleK3Closed b a v u hb ha hv0 hv1 hu0 hu1 hδ'

/-- Every two-state transient phase-type law satisfies the `k = 3` hierarchy inequality. -/
theorem transientStageBoundK3_two (X : TransientStart 2) :
    K3StageBound 2 (transientMoment2 2 X) (transientMoment3 2 X)
      (transientMoment4 2 X) := by
  let a := 1-X.Q 0 0
  let b := 1-X.Q 1 1
  let u := X.Q 0 1/a
  let v := X.Q 1 0/b
  have hrow0 := X.hrow (0 : Fin 2)
  have hrow1 := X.hrow (1 : Fin 2)
  rw [Fin.sum_univ_two] at hrow0 hrow1
  have hca : X.Q 0 1 ≤ a := by dsimp [a]; linarith
  have hdb : X.Q 1 0 ≤ b := by dsimp [b]; linarith
  have ha0 : 0 ≤ a := (X.hQ 0 1).trans hca
  have hb0 : 0 ≤ b := (X.hQ 1 0).trans hdb
  have hdetunit := (Matrix.isUnit_iff_isUnit_det _).mp X.hu
  have ha : 0 < a := by
    rcases eq_or_lt_of_le ha0 with ha' | ha'
    · exfalso
      have hc : X.Q 0 1 = 0 := by
        rw [← ha'] at hca
        exact le_antisymm hca (X.hQ 0 1)
      apply hdetunit.ne_zero
      rw [Matrix.det_fin_two]
      simp only [Matrix.sub_apply, Matrix.one_apply]
      norm_num
      rw [show 1-X.Q 0 0=0 from ha'.symm, hc]
      ring
    · exact ha'
  have hb : 0 < b := by
    rcases eq_or_lt_of_le hb0 with hb' | hb'
    · exfalso
      have hd : X.Q 1 0 = 0 := by
        rw [← hb'] at hdb
        exact le_antisymm hdb (X.hQ 1 0)
      apply hdetunit.ne_zero
      rw [Matrix.det_fin_two]
      simp only [Matrix.sub_apply, Matrix.one_apply]
      norm_num
      rw [show 1-X.Q 1 1=0 from hb'.symm, hd]
      ring
    · exact hb'
  have hu0 : 0 ≤ u := div_nonneg (X.hQ 0 1) ha.le
  have hu1 : u ≤ 1 := (div_le_one ha).mpr hca
  have hv0 : 0 ≤ v := div_nonneg (X.hQ 1 0) hb.le
  have hv1 : v ≤ 1 := (div_le_one hb).mpr hdb
  have hau : a*u = X.Q 0 1 := by dsimp [u]; field_simp [ha.ne']
  have hbv : b*v = X.Q 1 0 := by dsimp [v]; field_simp [hb.ne']
  have hA : 1-X.Q = (!![a, -a*u; -b*v, b] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [a, Matrix.sub_apply]
    · simp only [Matrix.sub_apply, Matrix.one_apply]
      norm_num
      rw [hau]
    · simp only [Matrix.sub_apply, Matrix.one_apply]
      norm_num
      rw [hbv]
    · simp [b, Matrix.sub_apply]
  have hδ : a*b*(1-u*v) ≠ 0 := by
    intro hz
    apply hdetunit.ne_zero
    rw [hA, Matrix.det_fin_two]
    norm_num
    calc a*b-a*u*(b*v) = a*b*(1-u*v) := by ring
      _ = 0 := hz
  have hmain := twoCycleMatrixK3 a b u v ha hb hu0 hu1 hv0 hv1 hδ X.i
  unfold K3StageBound transientMoment2 transientMoment3 transientMoment4
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
  rw [hA]
  nlinarith

/-- The `k = 3`, `s = 2` inequality for an arbitrary subprobability initial vector. -/
theorem transientInitialStageBoundK3_two (X : TransientInitial 2) :
    K3StageBound 2 (transientInitialMoment2 2 X) (transientInitialMoment3 2 X)
      (transientInitialMoment4 2 X) := by
  have hmix := SSP.Chain.mixture_closure_sq (Finset.univ : Finset (Fin 2)) X.weight
    (fun i => transientMoment2 2 (X.component i))
    (fun i => transientMoment3 2 (X.component i))
    (fun i => transientMoment4 2 (X.component i)) (5/4 : ℝ)
    (by norm_num) (fun i _ => X.weight_nonneg i)
    (fun i _ => transientMoment2_nonneg (X.component i))
    (fun i _ => transientMoment4_nonneg (X.component i))
    (fun i _ => transientMoment3_nonneg (X.component i))
    (fun i _ => by
      have h := transientStageBoundK3_two (X.component i)
      unfold K3StageBound at h
      norm_num at h ⊢
      nlinarith)
  unfold K3StageBound transientInitialMoment2 transientInitialMoment3
    transientInitialMoment4
  norm_num at hmix ⊢
  nlinarith

end SSP.K2Concrete
