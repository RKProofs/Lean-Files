import Mathlib

/-!
# The three-cycle support pattern at `s = 3`

Companion to `SSPLean.ChainInequality`; see `k2_hierarchy.tex` (cyclic routings) for context.

Pattern F is the last support pattern carrying a genuinely three-dimensional cycle:
`p₁₂ = u`, `p₂₃ = w`, `p₃₁ = v`, with `det(D(I−P)) = −d₁d₂d₃(uwv − 1)`.

Two structural facts carry the proof.

*Cyclic symmetry.*  Rotating states, `(d₁,d₂,d₃;u,w,v) ↦ (d₂,d₃,d₁;w,v,u)`, is an automorphism
of the pattern shifting the starting state by one, so the three start-state numerators form one
orbit and a single start state suffices.  We take start `1`.

*Concavity in the closing edge.*  The numerator is quadratic in `v` with leading coefficient
`−2d₁²d₂²d₃²u²w²·L`, `L > 0`, so its minimum over `v ∈ [0,1]` is at an endpoint.  `v = 0` is the
acyclic chain `1 → 2 → 3` (the triangular theorem).  For `v = 1`, writing `s = uw` for the loop
gain makes the face *quadratic in `u`*, its linear coefficient is positive, and so — convex or
concave — the minimum over `u ∈ [s,1]` is again at an endpoint, namely `w = 1` or `u = 1`.

Throughout, `d₁, d₂, d₃ > 0`: they are the diagonal entries of the invertible rate matrix `D`.
-/

set_option autoImplicit false
set_option linter.style.whitespace false

namespace SSP.Chain

set_option maxHeartbeats 4000000 in
/-- Numerator of `12a₁a₃ − 10a₂²` for pattern F started at state `1`, cleared of the
denominator `d₁⁴d₂⁴d₃⁴(uwv−1)⁴`. -/
noncomputable def cycFN (d₁ d₂ d₃ u w v : ℝ) : ℝ :=
    2*d₁^4*d₂^4*u^2*w^2 + 12*d₁^4*d₂^3*d₃*u^3*w^3*v - 8*d₁^4*d₂^3*d₃*u^3*w^2*v
      - 8*d₁^4*d₂^3*d₃*u^2*w^2 + 12*d₁^4*d₂^3*d₃*u^2*w - 10*d₁^4*d₂^2*d₃^2*u^4*w^2*v^2
      + 16*d₁^4*d₂^2*d₃^2*u^3*w^2*v + 12*d₁^4*d₂^2*d₃^2*u^3*w*v + 2*d₁^4*d₂^2*d₃^2*u^2*w^2
      - 8*d₁^4*d₂^2*d₃^2*u^2*w + 4*d₁^4*d₂*d₃^3*u^3*w*v + 4*d₁^4*d₂*d₃^3*u^2*w + 2*d₁^4*d₃^4*u^2
      + 12*d₁^3*d₂^4*d₃*u^3*w^3*v - 8*d₁^3*d₂^4*d₃*u^2*w^2*v - 8*d₁^3*d₂^4*d₃*u^2*w^2
      + 12*d₁^3*d₂^4*d₃*u*w + 12*d₁^3*d₂^3*d₃^2*u^3*w^3*v^2 + 12*d₁^3*d₂^3*d₃^2*u^3*w^3*v
      - 20*d₁^3*d₂^3*d₃^2*u^3*w^2*v^2 + 16*d₁^3*d₂^3*d₃^2*u^3*w^2*v - 16*d₁^3*d₂^3*d₃^2*u^2*w^2*v
      - 8*d₁^3*d₂^3*d₃^2*u^2*w^2 + 24*d₁^3*d₂^3*d₃^2*u^2*w*v - 8*d₁^3*d₂^3*d₃^2*u^2*w
      + 12*d₁^3*d₂^3*d₃^2*u*w - 8*d₁^3*d₂^2*d₃^3*u^3*w^2*v^2 + 24*d₁^3*d₂^2*d₃^3*u^3*w^2*v
      + 4*d₁^3*d₂^2*d₃^3*u^3*w*v - 8*d₁^3*d₂^2*d₃^3*u^2*w^2*v + 16*d₁^3*d₂^2*d₃^3*u^2*w*v
      - 16*d₁^3*d₂^2*d₃^3*u^2*w + 12*d₁^3*d₂^2*d₃^3*u*w + 12*d₁^3*d₂*d₃^4*u^3*w*v
      - 8*d₁^3*d₂*d₃^4*u^2*w*v - 8*d₁^3*d₂*d₃^4*u^2 + 12*d₁^3*d₂*d₃^4*u
      - 10*d₁^2*d₂^4*d₃^2*u^2*w^2*v^2 + 16*d₁^2*d₂^4*d₃^2*u^2*w^2*v + 2*d₁^2*d₂^4*d₃^2*u^2*w^2
      + 12*d₁^2*d₂^4*d₃^2*u*w*v - 8*d₁^2*d₂^4*d₃^2*u*w - 8*d₁^2*d₂^3*d₃^3*u^2*w^2*v^2
      + 16*d₁^2*d₂^3*d₃^3*u^2*w^2*v + 8*d₁^2*d₂^3*d₃^3*u^2*w*v + 4*d₁^2*d₂^3*d₃^3*u^2*w
      + 12*d₁^2*d₂^3*d₃^3*u*w*v - 8*d₁^2*d₂^3*d₃^3*u*w - 10*d₁^2*d₂^2*d₃^4*u^2*w^2*v^2
      + 16*d₁^2*d₂^2*d₃^4*u^2*w*v + 2*d₁^2*d₂^2*d₃^4*u^2 + 12*d₁^2*d₂^2*d₃^4*u*w*v
      - 8*d₁^2*d₂^2*d₃^4*u + 4*d₁*d₂^4*d₃^3*u*w*v + 4*d₁*d₂^4*d₃^3*u*w + 4*d₁*d₂^3*d₃^4*u*w*v
      + 4*d₁*d₂^3*d₃^4*u + 2*d₂^4*d₃^4

/-- The cofactor in the `v²` coefficient of `cycFN`. -/
noncomputable def cycFL (d₁ d₂ d₃ u w : ℝ) : ℝ :=
    5*d₁^2*u^2 - 6*d₁*d₂*u*w + 10*d₁*d₂*u + 4*d₁*d₃*u + 5*d₂^2 + 4*d₂*d₃ + 5*d₃^2

/-- **Quadratic in the closing edge.**  Lagrange form of `cycFN` in `v`, exhibiting the
leading coefficient as `−2d₁²d₂²d₃²u²w²·L`. -/
theorem cycF_quadratic_in_v (d₁ d₂ d₃ u w v : ℝ) :
    cycFN d₁ d₂ d₃ u w v
      = (-(2*d₁^2*d₂^2*d₃^2*u^2*w^2) * cycFL d₁ d₂ d₃ u w) * v^2
        + (cycFN d₁ d₂ d₃ u w 1 - cycFN d₁ d₂ d₃ u w 0
            + 2*d₁^2*d₂^2*d₃^2*u^2*w^2 * cycFL d₁ d₂ d₃ u w) * v
        + cycFN d₁ d₂ d₃ u w 0 := by
  unfold cycFN cycFL; ring

/-- **The certificate for `L`.**  The one negative monomial `−6d₁d₂uw` is absorbed by
`10d₁d₂u`, leaving `4d₁d₂u + 6d₁d₂u(1−w)` plus positive terms. -/
theorem cycFL_decomp (d₁ d₂ d₃ u w : ℝ) :
    cycFL d₁ d₂ d₃ u w
      = 4*d₁*d₂*u + 6*d₁*d₂*u*(1 - w)
        + 5*d₁^2*u^2 + 4*d₁*d₃*u + 5*d₂^2 + 4*d₂*d₃ + 5*d₃^2 := by
  unfold cycFL; ring

/-- `L > 0` on the admissible box. -/
theorem cycF_L_pos (d₁ d₂ d₃ u w : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (hu : 0 ≤ u) (_hw0 : 0 ≤ w) (hw1 : w ≤ 1) : 0 < cycFL d₁ d₂ d₃ u w := by
  rw [cycFL_decomp]
  have h1w : (0:ℝ) ≤ 1 - w := by linarith
  have e1 : 0 ≤ 6*d₁*d₂*u*(1 - w) := by positivity
  have e2 : 0 ≤ 4*d₁*d₂*u := by positivity
  have e3 : 0 ≤ 5*d₁^2*u^2 := by positivity
  have e4 : 0 ≤ 4*d₁*d₃*u := by positivity
  have e5 : 0 < 5*d₂^2 := by positivity
  have e6 : 0 ≤ 4*d₂*d₃ := by positivity
  have e7 : 0 < 5*d₃^2 := by positivity
  linarith

/-- **Concavity endpoint reduction.**  A quadratic with nonpositive leading coefficient
attains its minimum on `[0,1]` at an endpoint. -/
theorem concave_quad_ge_min_endpoints (A B C v : ℝ) (hA : A ≤ 0)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (h0 : 0 ≤ C) (h1 : 0 ≤ A + B + C) :
    0 ≤ A*v^2 + B*v + C := by
  nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hv1),
    mul_nonpos_of_nonpos_of_nonneg hA (mul_nonneg hv0 (sub_nonneg.mpr hv1))]

/-! ### The `v = 1` face

Write `s = uw` for the loop gain.  The face is then a quadratic in `u`. -/

/-- `u²` coefficient of the `v = 1` face. -/
noncomputable def cycFB2 (d₁ d₂ d₃ s : ℝ) : ℝ :=
    -10*d₁^4*d₂^2*d₃^2*s^2 + 12*d₁^4*d₂^2*d₃^2*s + 4*d₁^4*d₂*d₃^3*s + 2*d₁^4*d₃^4
      + 4*d₁^3*d₂^2*d₃^3*s + 12*d₁^3*d₂*d₃^4*s - 8*d₁^3*d₂*d₃^4 + 2*d₁^2*d₂^2*d₃^4

/-- `u¹` coefficient of the `v = 1` face. -/
noncomputable def cycFB1 (d₁ d₂ d₃ s : ℝ) : ℝ :=
    -8*d₁^4*d₂^3*d₃*s^2 + 12*d₁^4*d₂^3*d₃*s + 16*d₁^4*d₂^2*d₃^2*s^2 - 8*d₁^4*d₂^2*d₃^2*s
      + 4*d₁^4*d₂*d₃^3*s - 4*d₁^3*d₂^3*d₃^2*s^2 + 16*d₁^3*d₂^3*d₃^2*s + 16*d₁^3*d₂^2*d₃^3*s^2
      - 8*d₁^3*d₂*d₃^4*s + 12*d₁^3*d₂*d₃^4 + 12*d₁^2*d₂^3*d₃^3*s + 16*d₁^2*d₂^2*d₃^4*s
      - 8*d₁^2*d₂^2*d₃^4 + 4*d₁*d₂^3*d₃^4

/-- `u⁰` coefficient of the `v = 1` face. -/
noncomputable def cycFB0 (d₁ d₂ d₃ s : ℝ) : ℝ :=
    2*d₁^4*d₂^4*s^2 + 12*d₁^4*d₂^3*d₃*s^3 - 8*d₁^4*d₂^3*d₃*s^2 + 2*d₁^4*d₂^2*d₃^2*s^2
      + 12*d₁^3*d₂^4*d₃*s^3 - 16*d₁^3*d₂^4*d₃*s^2 + 12*d₁^3*d₂^4*d₃*s + 24*d₁^3*d₂^3*d₃^2*s^3
      - 24*d₁^3*d₂^3*d₃^2*s^2 + 12*d₁^3*d₂^3*d₃^2*s - 8*d₁^3*d₂^2*d₃^3*s^2 + 12*d₁^3*d₂^2*d₃^3*s
      + 8*d₁^2*d₂^4*d₃^2*s^2 + 4*d₁^2*d₂^4*d₃^2*s + 8*d₁^2*d₂^3*d₃^3*s^2 + 4*d₁^2*d₂^3*d₃^3*s
      - 10*d₁^2*d₂^2*d₃^4*s^2 + 12*d₁^2*d₂^2*d₃^4*s + 8*d₁*d₂^4*d₃^3*s + 4*d₁*d₂^3*d₃^4*s
      + 2*d₂^4*d₃^4

/-- **The `v = 1` face is quadratic in `u`** once the loop gain `s = uw` is held fixed. -/
theorem cycF_face_quadratic (d₁ d₂ d₃ u w : ℝ) :
    cycFN d₁ d₂ d₃ u w 1
      = cycFB2 d₁ d₂ d₃ (u*w) * u^2 + cycFB1 d₁ d₂ d₃ (u*w) * u
        + cycFB0 d₁ d₂ d₃ (u*w) := by
  unfold cycFN cycFB2 cycFB1 cycFB0; ring

/-- `−J`, where `B₁ = −4d₁d₂d₃·J`. -/
noncomputable def cycFmJ (d₁ d₂ d₃ s : ℝ) : ℝ :=
    -2*d₁^3*d₂^2*s^2 + 3*d₁^3*d₂^2*s + 4*d₁^3*d₂*d₃*s^2 - 2*d₁^3*d₂*d₃*s + d₁^3*d₃^2*s
      - d₁^2*d₂^2*d₃*s^2 + 4*d₁^2*d₂^2*d₃*s + 4*d₁^2*d₂*d₃^2*s^2 - 2*d₁^2*d₃^3*s + 3*d₁^2*d₃^3
      + 3*d₁*d₂^2*d₃^2*s + 4*d₁*d₂*d₃^3*s - 2*d₁*d₂*d₃^3 + d₂^2*d₃^3

/-- `B₁ = 4d₁d₂d₃·(−J)`. -/
theorem cycFB1_eq (d₁ d₂ d₃ s : ℝ) :
    cycFB1 d₁ d₂ d₃ s = 4*d₁*d₂*d₃ * cycFmJ d₁ d₂ d₃ s := by
  unfold cycFB1 cycFmJ; ring

/-- **The certificate for `−J`.**  Grouping by `d`-monomial leaves exactly two negative
groups, both carrying the factor `(2s−1)`; the two squares `d₃³(d₁−d₂)²` and `s·d₁³(d₃−d₂)²`
absorb them, and every remaining coefficient is nonnegative for `0 ≤ s ≤ 1`. -/
theorem cycFmJ_certificate (d₁ d₂ d₃ s : ℝ) :
    cycFmJ d₁ d₂ d₃ s
      = d₃^3*(d₁ - d₂)^2 + s*d₁^3*(d₃ - d₂)^2
        + 2*s*(1 - s)*d₁^3*d₂^2 + 4*s^2*d₁^3*d₂*d₃ + s*(4 - s)*d₁^2*d₂^2*d₃
        + 4*s^2*d₁^2*d₂*d₃^2 + 2*(1 - s)*d₁^2*d₃^3
        + 3*s*d₁*d₂^2*d₃^2 + 4*s*d₁*d₂*d₃^3 := by
  unfold cycFmJ; ring

/-- `−J > 0`, hence `B₁ > 0`. -/
theorem cycFmJ_pos (d₁ d₂ d₃ s : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : 0 < cycFmJ d₁ d₂ d₃ s := by
  rw [cycFmJ_certificate]
  have h1s : (0:ℝ) ≤ 1 - s := by linarith
  have h4s : (0:ℝ) ≤ 4 - s := by linarith
  have t1 : 0 < d₃^3*(d₁ - d₂)^2 ∨ d₁ = d₂ := by
    rcases eq_or_ne d₁ d₂ with h | h
    · right; exact h
    · left
      have : (0:ℝ) < (d₁ - d₂)^2 := by positivity
      positivity
  have e1 : 0 ≤ s*d₁^3*(d₃ - d₂)^2 := by positivity
  have e2 : 0 ≤ 2*s*(1 - s)*d₁^3*d₂^2 := by positivity
  have e3 : 0 ≤ 4*s^2*d₁^3*d₂*d₃ := by positivity
  have e4 : 0 ≤ s*(4 - s)*d₁^2*d₂^2*d₃ := by positivity
  have e5 : 0 ≤ 4*s^2*d₁^2*d₂*d₃^2 := by positivity
  have e6 : 0 ≤ 2*(1 - s)*d₁^2*d₃^3 := by positivity
  have e7 : 0 ≤ 3*s*d₁*d₂^2*d₃^2 := by positivity
  have e8 : 0 ≤ 4*s*d₁*d₂*d₃^3 := by positivity
  have e0 : 0 ≤ d₃^3*(d₁ - d₂)^2 := by positivity
  -- strictness: if `s > 0` use `4s²d₁³d₂d₃ > 0`; if `s = 0` the `2(1−s)d₁²d₃³` term is positive
  rcases eq_or_lt_of_le hs0 with hs | hs
  · have : 0 < 2*(1 - s)*d₁^2*d₃^3 := by rw [← hs]; norm_num; positivity
    linarith
  · have : 0 < 4*s^2*d₁^3*d₂*d₃ := by positivity
    linarith

/-- **`B₁ > 0`.** -/
theorem cycFB1_pos (d₁ d₂ d₃ s : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : 0 < cycFB1 d₁ d₂ d₃ s := by
  rw [cycFB1_eq]
  have := cycFmJ_pos d₁ d₂ d₃ s hd₁ hd₂ hd₃ hs0 hs1
  have h4 : (0:ℝ) < 4*d₁*d₂*d₃ := by positivity
  exact mul_pos h4 this


/-! ### The two endpoints of the `v = 1` face

Both are handled by the same device: on `[0,1]` a monomial dominates its higher powers
(`x^{k+1} ≤ x^k`), so a negative coefficient can be pushed down one degree, and the resulting
merged coefficient is certifiably nonnegative. -/

/-- **The auxiliary quartic `Q`.**  `Q = d₁⁴ + 2d₁³d₂ − 3d₁²d₂² + 2d₁d₂³ + d₂⁴ > 0`; the single
negative monomial is beaten by `(d₁²−d₂²)² + 2d₁d₂(d₁−d₂)² ≥ 6d₁²d₂²`. -/
theorem cycFQ_certificate (d₁ d₂ : ℝ) :
    d₁^4 + 2*d₁^3*d₂ - 3*d₁^2*d₂^2 + 2*d₁*d₂^3 + d₂^4
      = (d₁^2 - d₂^2)^2 + 2*d₁*d₂*(d₁ - d₂)^2 + 3*d₁^2*d₂^2 := by
  ring

theorem cycFQ_pos (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    0 < d₁^4 + 2*d₁^3*d₂ - 3*d₁^2*d₂^2 + 2*d₁*d₂^3 + d₂^4 := by
  rw [cycFQ_certificate]
  have e1 : (0:ℝ) ≤ (d₁^2 - d₂^2)^2 := sq_nonneg _
  have e2 : (0:ℝ) ≤ 2*d₁*d₂*(d₁ - d₂)^2 := by positivity
  have e3 : (0:ℝ) < 3*d₁^2*d₂^2 := by positivity
  linarith

/-! #### Endpoint `u = 1`: cubic in `w` -/

/-- The merged coefficient `b + c` of the `u = 1` face, divided by `2d₁d₂`. -/
noncomputable def cycFW (d₁ d₂ d₃ : ℝ) : ℝ :=
    d₁^3*d₂^3 - 2*d₁^3*d₂^2*d₃ + 6*d₁^3*d₂*d₃^2 + 4*d₁^3*d₃^3 - 2*d₁^2*d₂^3*d₃
      + 12*d₁^2*d₂*d₃^3 + 2*d₁^2*d₃^4 + 6*d₁*d₂^3*d₃^2 + 12*d₁*d₂^2*d₃^3
      + 9*d₁*d₂*d₃^4 + 4*d₂^3*d₃^3 + 2*d₂^2*d₃^4

/-- **Certificate for `W`.**  Two weighted AM-GM steps at `λ = μ = ½` clear both negative
monomials, and every remaining coefficient is positive. -/
theorem cycFW_certificate (d₁ d₂ d₃ : ℝ) :
    cycFW d₁ d₂ d₃
      = d₁^3*d₂*(d₂ - 2*d₃)^2/2 + d₁*d₂^3*(d₁ - 2*d₃)^2/2
        + 4*d₁^3*d₂*d₃^2 + 4*d₁^3*d₃^3 + 12*d₁^2*d₂*d₃^3 + 2*d₁^2*d₃^4
        + 4*d₁*d₂^3*d₃^2 + 12*d₁*d₂^2*d₃^3 + 9*d₁*d₂*d₃^4
        + 4*d₂^3*d₃^3 + 2*d₂^2*d₃^4 := by
  unfold cycFW; ring

theorem cycFW_pos (d₁ d₂ d₃ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃) :
    0 < cycFW d₁ d₂ d₃ := by
  rw [cycFW_certificate]
  have e1 : (0:ℝ) ≤ d₁^3*d₂*(d₂ - 2*d₃)^2/2 := by positivity
  have e2 : (0:ℝ) ≤ d₁*d₂^3*(d₁ - 2*d₃)^2/2 := by positivity
  have e3 : (0:ℝ) < 4*d₁^3*d₂*d₃^2 := by positivity
  have e4 : (0:ℝ) < 4*d₁^3*d₃^3 := by positivity
  have e5 : (0:ℝ) < 12*d₁^2*d₂*d₃^3 := by positivity
  have e6 : (0:ℝ) < 2*d₁^2*d₃^4 := by positivity
  have e7 : (0:ℝ) < 4*d₁*d₂^3*d₃^2 := by positivity
  have e8 : (0:ℝ) < 12*d₁*d₂^2*d₃^3 := by positivity
  have e9 : (0:ℝ) < 9*d₁*d₂*d₃^4 := by positivity
  have e10 : (0:ℝ) < 4*d₂^3*d₃^3 := by positivity
  have e11 : (0:ℝ) < 2*d₂^2*d₃^4 := by positivity
  linarith

/-! #### Endpoint `w = 1`: quartic in `u` -/

/-- The merged coefficient `a₁ + a₂` of the `w = 1` face, divided by `2d₁`. -/
noncomputable def cycFV (d₁ d₂ d₃ : ℝ) : ℝ :=
    d₁^3*d₂^4 + 2*d₁^3*d₂^3*d₃ - 3*d₁^3*d₂^2*d₃^2 + 2*d₁^3*d₂*d₃^3 + d₁^3*d₃^4
      - 2*d₁^2*d₂^4*d₃ + 2*d₁^2*d₂^3*d₃^2 + 2*d₁^2*d₂^2*d₃^3 - 2*d₁^2*d₂*d₃^4
      + 6*d₁*d₂^4*d₃^2 + 12*d₁*d₂^3*d₃^3 + 6*d₁*d₂^2*d₃^4 + 4*d₂^4*d₃^3 + 4*d₂^3*d₃^4

/-- **Certificate for `V`.**  The `d₁³` block is the auxiliary quartic `Q` in `(d₂,d₃)` with
half its slack spent; the two `d₁²` negatives are cleared by AM-GM at `λ = μ = ½`. -/
theorem cycFV_certificate (d₁ d₂ d₃ : ℝ) :
    cycFV d₁ d₂ d₃
      = d₁*d₂^4*(d₁ - 2*d₃)^2/2 + d₁*d₃^4*(d₁ - 2*d₂)^2/2
        + d₁^3*((d₂^2 - d₃^2)^2/2 + 2*d₂*d₃*(d₂ - d₃)^2 + 2*d₂^2*d₃^2)
        + 2*d₁^2*d₂^3*d₃^2 + 2*d₁^2*d₂^2*d₃^3
        + 4*d₁*d₂^4*d₃^2 + 12*d₁*d₂^3*d₃^3 + 4*d₁*d₂^2*d₃^4
        + 4*d₂^4*d₃^3 + 4*d₂^3*d₃^4 := by
  unfold cycFV; ring

theorem cycFV_pos (d₁ d₂ d₃ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃) :
    0 < cycFV d₁ d₂ d₃ := by
  rw [cycFV_certificate]
  have e1 : (0:ℝ) ≤ d₁*d₂^4*(d₁ - 2*d₃)^2/2 := by positivity
  have e2 : (0:ℝ) ≤ d₁*d₃^4*(d₁ - 2*d₂)^2/2 := by positivity
  have e3 : (0:ℝ) < d₁^3*((d₂^2 - d₃^2)^2/2 + 2*d₂*d₃*(d₂ - d₃)^2 + 2*d₂^2*d₃^2) := by
    have h : (0:ℝ) < (d₂^2 - d₃^2)^2/2 + 2*d₂*d₃*(d₂ - d₃)^2 + 2*d₂^2*d₃^2 := by
      have f1 : (0:ℝ) ≤ (d₂^2 - d₃^2)^2/2 := by positivity
      have f2 : (0:ℝ) ≤ 2*d₂*d₃*(d₂ - d₃)^2 := by positivity
      have f3 : (0:ℝ) < 2*d₂^2*d₃^2 := by positivity
      linarith
    have : (0:ℝ) < d₁^3 := by positivity
    exact mul_pos this h
  have e4 : (0:ℝ) < 2*d₁^2*d₂^3*d₃^2 := by positivity
  have e5 : (0:ℝ) < 2*d₁^2*d₂^2*d₃^3 := by positivity
  have e6 : (0:ℝ) < 4*d₁*d₂^4*d₃^2 := by positivity
  have e7 : (0:ℝ) < 12*d₁*d₂^3*d₃^3 := by positivity
  have e8 : (0:ℝ) < 4*d₁*d₂^2*d₃^4 := by positivity
  have e9 : (0:ℝ) < 4*d₂^4*d₃^3 := by positivity
  have e10 : (0:ℝ) < 4*d₂^3*d₃^4 := by positivity
  linarith

/-! ### The degree-lowering lemmas

On `[0,1]`, `x^{k+1} ≤ x^k`, so a term with a negative coefficient may be replaced by the same
coefficient on the next lower power. -/

/-- **Cubic reduction.**  If `a, c, d ≥ 0` and `b + c ≥ 0`, then
`a x³ + b x² + c x + d ≥ 0` on `[0,1]`.

When `b ≥ 0` every term is nonnegative.  When `b < 0`, `x² ≤ x` gives `b x² ≥ b x`, so the
expression is at least `a x³ + (b+c)x + d ≥ 0`.

The hypothesis `c ≥ 0` cannot be dropped: `a = d = 0`, `b = 4`, `c = −4`, `x = ½` satisfies
`b + c ≥ 0` yet the value is `−1`. -/
theorem cubic_nonneg_of_merge (a b c d x : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hbc : 0 ≤ b + c) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ a*x^3 + b*x^2 + c*x + d := by
  have hax : 0 ≤ a*x^3 := by positivity
  rcases le_or_gt 0 b with hb | hb
  · have t2 : 0 ≤ b*x^2 := by positivity
    have t3 : 0 ≤ c*x := mul_nonneg hc hx0
    linarith
  · have hgap : 0 ≤ x - x^2 := by nlinarith
    have hnb : 0 ≤ -b := by linarith
    have t2 : b*x ≤ b*x^2 := by nlinarith [mul_nonneg hnb hgap]
    have t4 : 0 ≤ (b + c)*x := mul_nonneg hbc hx0
    nlinarith

/-- **Quartic reduction.**  If `a₄ ≤ 0`, `a₁, a₀ ≥ 0`, `a₃ + a₄ ≥ 0` and `a₁ + a₂ ≥ 0`, then
`a₄x⁴ + a₃x³ + a₂x² + a₁x + a₀ ≥ 0` on `[0,1]`.  Push `a₄x⁴` down to `x³` using `x⁴ ≤ x³`,
then apply the cubic reduction. -/
theorem quartic_nonneg_of_merges (a₄ a₃ a₂ a₁ a₀ x : ℝ) (h4 : a₄ ≤ 0) (h1 : 0 ≤ a₁)
    (h0 : 0 ≤ a₀) (h34 : 0 ≤ a₃ + a₄) (h12 : 0 ≤ a₁ + a₂) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ a₄*x^4 + a₃*x^3 + a₂*x^2 + a₁*x + a₀ := by
  have hx3 : 0 ≤ x^3 := by positivity
  have hgap3 : 0 ≤ x^3 - x^4 := by nlinarith
  have hstep : a₄*x^3 ≤ a₄*x^4 := by nlinarith [mul_nonneg (neg_nonneg.mpr h4) hgap3]
  have hcubic : 0 ≤ (a₃ + a₄)*x^3 + a₂*x^2 + a₁*x + a₀ :=
    cubic_nonneg_of_merge (a₃ + a₄) a₂ a₁ a₀ x h34 h1 h0 (by linarith) hx0 hx1
  linarith

/-! ### The two endpoints, certified -/

/-- **Endpoint `u = 1` of the `v = 1` face.**  A cubic in `w` whose `w³`, `w¹`, `w⁰`
coefficients are positive and whose `w²` coefficient is merged into `w¹` via `cycFW`. -/
theorem cycF_face_u1_nonneg (d₁ d₂ d₃ w : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : 0 ≤ cycFN d₁ d₂ d₃ 1 w 1 := by
  have key : cycFN d₁ d₂ d₃ 1 w 1
      = (12*d₁^3*d₂^3*d₃*(d₁ + d₂ + 2*d₃)) * w^3
        + (2*d₁*d₂*cycFW d₁ d₂ d₃
            - 4*d₁*d₂*d₃*(3*d₁^3*d₂^2 + d₁^3*d₂*d₃ + 2*d₁^3*d₃^2 + 3*d₁^2*d₂^3
              + 7*d₁^2*d₂^2*d₃ + 4*d₁^2*d₂*d₃^2 + d₁^2*d₃^3 + d₁*d₂^3*d₃
              + 4*d₁*d₂^2*d₃^2 + 7*d₁*d₂*d₃^3 + 2*d₂^3*d₃^2 + d₂^2*d₃^3)) * w^2
        + (4*d₁*d₂*d₃*(3*d₁^3*d₂^2 + d₁^3*d₂*d₃ + 2*d₁^3*d₃^2 + 3*d₁^2*d₂^3
              + 7*d₁^2*d₂^2*d₃ + 4*d₁^2*d₂*d₃^2 + d₁^2*d₃^3 + d₁*d₂^3*d₃
              + 4*d₁*d₂^2*d₃^2 + 7*d₁*d₂*d₃^3 + 2*d₂^3*d₃^2 + d₂^2*d₃^3)) * w
        + 2*d₃^4*(d₁^4 + 2*d₁^3*d₂ - 3*d₁^2*d₂^2 + 2*d₁*d₂^3 + d₂^4) := by
    unfold cycFN cycFW; ring
  rw [key]
  refine cubic_nonneg_of_merge _ _ _ _ w (by positivity) (by positivity) ?_ ?_ hw0 hw1
  · have := cycFQ_pos d₁ d₂ hd₁ hd₂
    have h : (0:ℝ) < 2*d₃^4 := by positivity
    exact le_of_lt (mul_pos h this)
  · have := cycFW_pos d₁ d₂ d₃ hd₁ hd₂ hd₃
    have h : (0:ℝ) < 2*d₁*d₂ := by positivity
    nlinarith [mul_pos h this]

/-- **Endpoint `w = 1` of the `v = 1` face.**  A quartic in `u` with negative lead; the lead is
absorbed into `u³` and the indefinite `u²` coefficient into `u¹` via `cycFV`. -/
theorem cycF_face_w1_nonneg (d₁ d₂ d₃ u : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ cycFN d₁ d₂ d₃ u 1 1 := by
  have key : cycFN d₁ d₂ d₃ u 1 1
      = (-(10*d₁^4*d₂^2*d₃^2)) * u^4
        + (4*d₁^3*d₂*d₃*(d₁*d₂^2 + 7*d₁*d₂*d₃ + d₁*d₃^2 + 3*d₂^3 + 5*d₂^2*d₃
            + 5*d₂*d₃^2 + 3*d₃^3)) * u^3
        + (2*d₁*cycFV d₁ d₂ d₃
            - 4*d₁*d₂*d₃*(3*d₁^2*d₂^3 + 3*d₁^2*d₂^2*d₃ + 3*d₁^2*d₂*d₃^2 + 3*d₁^2*d₃^3
              + d₁*d₂^3*d₃ + d₁*d₂^2*d₃^2 + d₁*d₂*d₃^3 + 2*d₂^3*d₃^2 + 2*d₂^2*d₃^3)) * u^2
        + (4*d₁*d₂*d₃*(3*d₁^2*d₂^3 + 3*d₁^2*d₂^2*d₃ + 3*d₁^2*d₂*d₃^2 + 3*d₁^2*d₃^3
              + d₁*d₂^3*d₃ + d₁*d₂^2*d₃^2 + d₁*d₂*d₃^3 + 2*d₂^3*d₃^2 + 2*d₂^2*d₃^3)) * u
        + 2*d₂^4*d₃^4 := by
    unfold cycFN cycFV; ring
  rw [key]
  refine quartic_nonneg_of_merges _ _ _ _ _ u ?_ (by positivity) (by positivity) ?_ ?_ hu0 hu1
  · have : (0:ℝ) < 10*d₁^4*d₂^2*d₃^2 := by positivity
    linarith
  · nlinarith [mul_pos (mul_pos (mul_pos (pow_pos hd₁ 3) hd₂) hd₃)
      (show (0:ℝ) < 2*d₁*d₂^2 + 9*d₁*d₂*d₃ + 2*d₁*d₃^2 + 6*d₂^3 + 10*d₂^2*d₃
        + 10*d₂*d₃^2 + 6*d₃^3 by positivity)]
  · have := cycFV_pos d₁ d₂ d₃ hd₁ hd₂ hd₃
    have h : (0:ℝ) < 2*d₁ := by positivity
    nlinarith [mul_pos h this]

/-! ### The `v = 1` face, assembled

With the loop gain `s = uw` held fixed the face is `B₂u² + B₁u + B₀`, and `B₁ > 0`.  Because
`u ≥ s = uw` (as `w ≤ 1`) and `u ≤ 1`, the argument runs on `[s,1]`:

* if `B₂ ≤ 0` the quadratic is concave, so its minimum is at `u = s` or `u = 1`;
* if `B₂ > 0` it is convex with vertex at `−B₁/(2B₂) < 0 ≤ s`, hence increasing on `[s,1]`,
  so the minimum is at `u = s`.

Either way only the two endpoints matter, and `u = s` means `w = 1` while `u = 1` means `w = s`.
Both are certified above. -/

/-- **Secant bound for a concave quadratic.**  Scaled to avoid division:
`(q−p)(Ay²+By+C) = (q−y)(Ap²+Bp+C) + (y−p)(Aq²+Bq+C) − A(y−p)(q−y)(q−p)`.
With `A ≤ 0` and `p ≤ y ≤ q` every term on the right is nonnegative. -/
theorem quad_secant_identity (A B C p q y : ℝ) :
    (q - p)*(A*y^2 + B*y + C)
      = (q - y)*(A*p^2 + B*p + C) + (y - p)*(A*q^2 + B*q + C)
        - A*(y - p)*(q - y)*(q - p) := by
  ring

/-- A concave quadratic on `[p,q]` is bounded below by its endpoint values. -/
theorem quad_ge_endpoints_of_concave (A B C p q y : ℝ) (hA : A ≤ 0)
    (hpy : p ≤ y) (hyq : y ≤ q)
    (hp : 0 ≤ A*p^2 + B*p + C) (hq : 0 ≤ A*q^2 + B*q + C) :
    0 ≤ A*y^2 + B*y + C := by
  rcases eq_or_lt_of_le (le_trans hpy hyq) with hpq | hpq
  · -- degenerate: p = q forces y = p
    have hy : y = p := le_antisymm (by rw [hpq]; exact hyq) hpy
    subst hy; exact hp
  · have hyp : (0:ℝ) ≤ y - p := sub_nonneg.mpr hpy
    have hqy : (0:ℝ) ≤ q - y := sub_nonneg.mpr hyq
    have hqp : (0:ℝ) < q - p := sub_pos.mpr hpq
    have t1 : 0 ≤ (q - y)*(A*p^2 + B*p + C) := mul_nonneg hqy hp
    have t2 : 0 ≤ (y - p)*(A*q^2 + B*q + C) := mul_nonneg hyp hq
    have t3 : 0 ≤ -A*((y - p)*((q - y)*(q - p))) :=
      mul_nonneg (neg_nonneg.mpr hA) (mul_nonneg hyp (mul_nonneg hqy (le_of_lt hqp)))
    have key := quad_secant_identity A B C p q y
    nlinarith [key, t1, t2, t3]

/-- A quadratic with nonnegative leading and linear coefficients is increasing on `[0,∞)`,
hence bounded below by its value at the left endpoint. -/
theorem quad_ge_left_of_convex (A B C p y : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 ≤ p)
    (hpy : p ≤ y) (hleft : 0 ≤ A*p^2 + B*p + C) :
    0 ≤ A*y^2 + B*y + C := by
  have hy : 0 ≤ y := le_trans hp hpy
  have h1 : A*p^2 ≤ A*y^2 := by
    have : p^2 ≤ y^2 := by nlinarith
    nlinarith
  have h2 : B*p ≤ B*y := by nlinarith
  linarith

/-- **The `v = 1` face is nonnegative.** -/
theorem cycF_face_nonneg (d₁ d₂ d₃ u w : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    0 ≤ cycFN d₁ d₂ d₃ u w 1 := by
  set s := u*w with hs
  have hs0 : 0 ≤ s := mul_nonneg hu0 hw0
  have hsu : s ≤ u := by
    rw [hs]; nlinarith
  have hs1 : s ≤ 1 := le_trans hsu hu1
  have hB1 : 0 < cycFB1 d₁ d₂ d₃ s := cycFB1_pos d₁ d₂ d₃ s hd₁ hd₂ hd₃ hs0 hs1
  rw [cycF_face_quadratic]
  -- endpoint `u = s` (i.e. `w = 1`) and endpoint `u = 1` (i.e. `w = s`)
  have hleft : 0 ≤ cycFB2 d₁ d₂ d₃ s * s^2 + cycFB1 d₁ d₂ d₃ s * s + cycFB0 d₁ d₂ d₃ s := by
    have e : cycFB2 d₁ d₂ d₃ s * s^2 + cycFB1 d₁ d₂ d₃ s * s + cycFB0 d₁ d₂ d₃ s
        = cycFN d₁ d₂ d₃ s 1 1 := by
      unfold cycFB2 cycFB1 cycFB0 cycFN; ring
    rw [e]; exact cycF_face_w1_nonneg d₁ d₂ d₃ s hd₁ hd₂ hd₃ hs0 hs1
  have hright : 0 ≤ cycFB2 d₁ d₂ d₃ s * 1^2 + cycFB1 d₁ d₂ d₃ s * 1 + cycFB0 d₁ d₂ d₃ s := by
    have e : cycFB2 d₁ d₂ d₃ s * 1^2 + cycFB1 d₁ d₂ d₃ s * 1 + cycFB0 d₁ d₂ d₃ s
        = cycFN d₁ d₂ d₃ 1 s 1 := by
      unfold cycFB2 cycFB1 cycFB0 cycFN; ring
    rw [e]; exact cycF_face_u1_nonneg d₁ d₂ d₃ s hd₁ hd₂ hd₃ hs0 hs1
  rcases le_or_gt (cycFB2 d₁ d₂ d₃ s) 0 with hB2 | hB2
  · exact quad_ge_endpoints_of_concave _ _ _ s 1 u hB2 hsu hu1 hleft hright
  · exact quad_ge_left_of_convex _ _ _ s u (le_of_lt hB2) (le_of_lt hB1) hs0 hsu hleft

/-- **Pattern F at `s = 3`, started at state `1`.**  The numerator of `12a₁a₃ − 10a₂²` is
nonnegative on the admissible box, given the `v = 0` (acyclic) endpoint.

The acyclic endpoint `cycFN d₁ d₂ d₃ u w 0` is the routing `1 → 2 → 3` with no return, i.e. an
upper-triangular substochastic `A`; it is covered by the triangular theorem
(`k2_hierarchy.tex`, `thm:triangular`) and is taken here as a hypothesis. -/
theorem cycF_nonneg (d₁ d₂ d₃ u w v : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hacyclic : 0 ≤ cycFN d₁ d₂ d₃ u w 0) :
    0 ≤ cycFN d₁ d₂ d₃ u w v := by
  have hL : 0 < cycFL d₁ d₂ d₃ u w := cycF_L_pos d₁ d₂ d₃ u w hd₁ hd₂ hd₃ hu0 hw0 hw1
  have hface : 0 ≤ cycFN d₁ d₂ d₃ u w 1 :=
    cycF_face_nonneg d₁ d₂ d₃ u w hd₁ hd₂ hd₃ hu0 hu1 hw0 hw1
  rw [cycF_quadratic_in_v]
  refine concave_quad_ge_min_endpoints _ _ _ v ?_ hv0 hv1 hacyclic ?_
  · have h : (0:ℝ) ≤ 2*d₁^2*d₂^2*d₃^2*u^2*w^2 := by positivity
    nlinarith [mul_nonneg h (le_of_lt hL)]
  · linarith



/-! ## Toward the patterns that feed into state 3

The five cases still open at `s = 3` are start `3` of the two-cycle-plus-`3→1` pattern and
starts `1` and `2` of the two patterns carrying an edge *into* state `3`.  All five share a
structure worth recording, and one of its ingredients is proved here.

**The admissible region is a simplex, not a box.**  In the patterns with an edge `1→3` (or
`2→3`) the state `1` (resp. `2`) row of `P` carries *two* entries, so substochasticity reads
`u + z ≤ 1` rather than `u ≤ 1`, `z ≤ 1`.  Ignoring this reports spurious violations on the
`z = 1` face, which is inadmissible unless `u = 0`.

In every one of the five cases the numerator is quadratic in the extra edge `z`, with
`z = 0` reproducing (`d₃⁴` times) an already-settled pattern.  The leading coefficient `C₂` is
sign-indefinite, so the concave branch gives an endpoint argument and the convex branch needs
the vertex `−C₁/(2C₂)` to fall outside the admissible interval — that is, `C₁ ≥ 0`.  The
discriminant route is unavailable: `4C₂C₀ − C₁²` was negative in *every* one of ~4.6·10⁶
convex-branch samples, across all five cases.

What remains is the conditional `C₂ > 0 ⟹ C₁ ≥ 0`.  Both `C₁` and `C₂` are quadratic in the
back-edge `w` with leading coefficients sharing the factor `(d₂ − d₃)`; the statement survived
6.1·10⁶ convex-branch samples and a systematic grid of 5·10⁴ points spanning twelve decades,
with no violation.  The `w = 0` slice of it is proved below. -/

/-- `A`, `B`, `C` for the `w = 0` slice of the `2`-cycle-plus-`1→3` pattern started at state `1`:
after `d₃ = t·d₁`, the linear coefficient `C₁` at `w = 0` is `A t² + B t + C`. -/
noncomputable def sliceA (d₁ d₂ : ℝ) : ℝ := 3*d₁^3 - 2*d₁^2*d₂ + d₁*d₂^2 + d₂^3

noncomputable def sliceB (d₁ d₂ : ℝ) : ℝ := -(d₂*(5*d₁^2 + 2*d₁*d₂ + 2*d₂^2))

noncomputable def sliceC (d₁ d₂ : ℝ) : ℝ := 3*d₂^2*(d₁ + d₂)

/-- `A > 0`, by `2d₁²d₂ ≤ d₁³ + d₁d₂²`. -/
theorem sliceA_pos (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) : 0 < sliceA d₁ d₂ := by
  have key : sliceA d₁ d₂ = d₁*(d₁ - d₂)^2 + 2*d₁^3 + d₂^3 := by unfold sliceA; ring
  rw [key]
  have e1 : (0:ℝ) ≤ d₁*(d₁ - d₂)^2 := by positivity
  have e2 : (0:ℝ) < 2*d₁^3 := by positivity
  have e3 : (0:ℝ) < d₂^3 := by positivity
  linarith

theorem sliceC_pos (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) : 0 < sliceC d₁ d₂ := by
  unfold sliceC; positivity

/-- **The vertex bound.**  `4A + B > 0`, so the vertex `−B/(2A)` is below `2`.  The certificate
is `4A + B = 2d₂(d₂−d₁)² + 6d₁(d₂ − 5d₁/4)² + (21/8)d₁³`. -/
theorem slice_vertex_bound (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    0 < 4 * sliceA d₁ d₂ + sliceB d₁ d₂ := by
  have key : 4 * sliceA d₁ d₂ + sliceB d₁ d₂
      = 2*d₂*(d₂ - d₁)^2 + 6*d₁*(d₂ - (5/4)*d₁)^2 + (21/8)*d₁^3 := by
    unfold sliceA sliceB; ring
  rw [key]
  have e1 : (0:ℝ) ≤ 2*d₂*(d₂ - d₁)^2 := by positivity
  have e2 : (0:ℝ) ≤ 6*d₁*(d₂ - (5/4)*d₁)^2 := by positivity
  have e3 : (0:ℝ) < (21/8)*d₁^3 := by positivity
  linarith

/-- **The upper branch.**  The hypothesis `A₀ = d₁² − 4d₁d₃ + d₃² > 0` says `t² > 4t − 1` for
`t = d₃/d₁`.  With `t > 2` this gives `q(t) > (4A+B)t + (C − A) ≥ 2(4A+B) + C − A = 7A+2B+C`,
and `7A + 2B + C = 3[2d₂(d₂−d₁)² + 6d₁(d₂ − 5d₁/6)² + (17/6)d₁³] > 0`. -/
theorem slice_upper_value_pos (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    0 < 7 * sliceA d₁ d₂ + 2 * sliceB d₁ d₂ + sliceC d₁ d₂ := by
  have key : 7 * sliceA d₁ d₂ + 2 * sliceB d₁ d₂ + sliceC d₁ d₂
      = 3*(2*d₂*(d₂ - d₁)^2 + 6*d₁*(d₂ - (5/6)*d₁)^2 + (17/6)*d₁^3) := by
    unfold sliceA sliceB sliceC; ring
  rw [key]
  have e1 : (0:ℝ) ≤ 2*d₂*(d₂ - d₁)^2 := by positivity
  have e2 : (0:ℝ) ≤ 6*d₁*(d₂ - (5/6)*d₁)^2 := by positivity
  have e3 : (0:ℝ) < (17/6)*d₁^3 := by positivity
  linarith

/-- **The upper branch, assembled.**  If `t > 2` and `t² ≥ 4t − 1` then `A t² + B t + C > 0`. -/
theorem slice_upper_pos (d₁ d₂ t : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (ht : 2 < t) (hA₀ : 4*t - 1 ≤ t^2) :
    0 < sliceA d₁ d₂ * t^2 + sliceB d₁ d₂ * t + sliceC d₁ d₂ := by
  have hA : 0 < sliceA d₁ d₂ := sliceA_pos d₁ d₂ hd₁ hd₂
  have hvb : 0 < 4 * sliceA d₁ d₂ + sliceB d₁ d₂ := slice_vertex_bound d₁ d₂ hd₁ hd₂
  have hval : 0 < 7 * sliceA d₁ d₂ + 2 * sliceB d₁ d₂ + sliceC d₁ d₂ :=
    slice_upper_value_pos d₁ d₂ hd₁ hd₂
  -- A t² ≥ A(4t − 1), then (4A+B)t > 2(4A+B)
  have h1 : sliceA d₁ d₂ * (4*t - 1) ≤ sliceA d₁ d₂ * t^2 :=
    mul_le_mul_of_nonneg_left hA₀ (le_of_lt hA)
  have h2 : 2 * (4 * sliceA d₁ d₂ + sliceB d₁ d₂) < (4 * sliceA d₁ d₂ + sliceB d₁ d₂) * t := by
    nlinarith
  nlinarith

/-- **`r > 0` on `[0,½]`**, where `r(s) = 8s⁴ + 16s³ − 36s² − 8s + 11` controls the sign of the
discriminant `4AC − B² = d₂²d₁⁴·s²·r(s)` with `s = d₂/d₁`.  Certificate:
`r − ½ = (2s−1)(8s³ + 20s² − 26s − 21)/2`, and on `[0,½]` the second factor is at most
`6 − 21 < 0` while `2s − 1 ≤ 0`. -/
theorem slice_r_pos (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2) :
    0 < 8*s^4 + 16*s^3 - 36*s^2 - 8*s + 11 := by
  have hfac : 8*s^4 + 16*s^3 - 36*s^2 - 8*s + 11
      = 1/2 + (2*s - 1)*(8*s^3 + 20*s^2 - 26*s - 21)/2 := by ring
  have hg : 8*s^3 + 20*s^2 - 26*s - 21 < 0 := by
    have h3 : s^3 ≤ 1/8 := by nlinarith
    have h2 : s^2 ≤ 1/4 := by nlinarith
    nlinarith
  have h2s : 2*s - 1 ≤ 0 := by linarith
  have : 0 ≤ (2*s - 1)*(8*s^3 + 20*s^2 - 26*s - 21)/2 := by
    have := mul_nonneg (neg_nonneg.mpr h2s) (neg_nonneg.mpr (le_of_lt hg))
    nlinarith
  rw [hfac]; linarith


/-! ## `C₂ > 0 ⟹ C₁ ≥ 0` for the `1→3` pattern started at state 1

This is the statement all five remaining `s = 3` cases reduce to (Section `sec:cycfive` of
`k2_hierarchy.tex`).  It is proved here for the two-cycle-plus-`1→3` pattern started at state
`1`.  The whole argument is driven by one change of variables.

**The loop-gain substitution.**  Put `y = 1 − uw`, i.e. `w = (1−y)/u`.  After clearing `u²`,

* `C₂` becomes **free of `u`** (call it `C₂y`, normalised by `2d₁²d₂²u²`), and
* `C₁/(4d₁d₂d₃)` becomes **linear in `u`**: `C₁y = d₁·k₁·u + d₂·k₀`.

Substochasticity gives `w ≤ 1`, i.e. `u ≥ 1 − y`, and `u ≤ 1`.  So `u` ranges over `[1−y, 1]`
and, `C₁y` being linear there, only the two endpoints matter — no vertex, no discriminant.

**Both endpoints beat `d₂·C₂y`.**  At each endpoint the excess over `d₂·C₂y` is a quadratic in
`d₃` whose `d₃²` and `d₃⁰` coefficients are positive and whose `d₃¹` coefficient is the only
indefinite one.  So each endpoint splits: either the middle coefficient is already nonnegative
and the quadratic is nonnegative termwise, or it is negative and the discriminant is nonpositive.
The two discriminant certificates are `PhiDr_cert` (for `u = 1`) and, after `d₂ = s d₁` and
`y = 1 − v`, `inner2_cert` (for `u = 1 − y`). -/

/-- `inner`, the cofactor of the `d₃²` coefficient at both endpoints. -/
noncomputable def sliceInner (d₁ d₂ y : ℝ) : ℝ :=
    2*d₁^2*y + d₁^2 - 4*d₁*d₂*y + 2*d₁*d₂ + d₂^2

/-- **`inner > 0`.**  Certificate: `d₁² + y d₁² + 2(1−y)d₁d₂ + (1−y)d₂² + y(d₁−d₂)²`. -/
theorem sliceInner_pos (d₁ d₂ y : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 < sliceInner d₁ d₂ y := by
  have key : sliceInner d₁ d₂ y
      = d₁^2 + y*d₁^2 + 2*(1 - y)*d₁*d₂ + (1 - y)*d₂^2 + y*(d₁ - d₂)^2 := by
    unfold sliceInner; ring
  rw [key]
  have h1y : (0:ℝ) ≤ 1 - y := by linarith
  have e1 : (0:ℝ) < d₁^2 := by positivity
  have e2 : (0:ℝ) ≤ y*d₁^2 := by positivity
  have e3 : (0:ℝ) ≤ 2*(1 - y)*d₁*d₂ := by positivity
  have e4 : (0:ℝ) ≤ (1 - y)*d₂^2 := by positivity
  have e5 : (0:ℝ) ≤ y*(d₁ - d₂)^2 := by positivity
  linarith

/-- `H`, the cofactor of the `d₃¹` coefficient at the `u = 1` endpoint (with a minus sign):
the `d₃` coefficient is `−d₁d₂y·H`. -/
noncomputable def sliceH (d₁ d₂ y : ℝ) : ℝ := 3*d₁^2*y + 2*d₁^2 + 2*d₁*d₂*y - 2*d₂^2

/-- **The `u = 1` discriminant certificate**, 13 terms.  `4c₂c₀ − c₁² = d₁²d₂²y²·Dr` with
`Dr = 2H d₂² + (\text{manifestly nonnegative})`, so `H > 0` forces `Dr > 0`. -/
theorem sliceDr_cert (d₁ d₂ y : ℝ) :
    -9*d₁^4*y^2 + 12*d₁^4*y + 8*d₁^4 - 12*d₁^3*d₂*y^2 - 40*d₁^3*d₂*y + 32*d₁^3*d₂
      - 4*d₁^2*d₂^2*y^2 - 20*d₁^2*d₂^2*y + 36*d₁^2*d₂^2 + 8*d₁*d₂^3*y + 8*d₁*d₂^3 - 4*d₂^4
    = 2 * sliceH d₁ d₂ y * d₂^2
      + 38*(1 - y)*d₁^3*d₂ + (67/2)*(1 - y)*d₁^2*d₂^2 + 12*(1 - y)*d₁^4*y
      + (17/2)*(1 - y)*d₁^2*d₂^2*y + 6*(1 - y)*d₁^3*d₂*y
      + (9/2)*(d₁ - d₂*y)^2*d₁^2 + 3*(1 - y)*d₁^4*y^2
      + 3*(d₁*y - d₂)^2*d₁^2*y + 2*(d₁ - 2*d₂)^2*d₁*d₂
      + (3/2)*(d₁ - 2*d₂)^2*d₁^2 + (d₁ - 2*d₂)^2*d₁*d₂*y
      + (1/2)*(2*d₁ - d₂)^2*d₁^2 := by
  unfold sliceH; ring

/-- `H > 0 ⟹ Dr > 0`. -/
theorem sliceDr_pos_of_H_pos (d₁ d₂ y : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hH : 0 < sliceH d₁ d₂ y) :
    0 < -9*d₁^4*y^2 + 12*d₁^4*y + 8*d₁^4 - 12*d₁^3*d₂*y^2 - 40*d₁^3*d₂*y + 32*d₁^3*d₂
      - 4*d₁^2*d₂^2*y^2 - 20*d₁^2*d₂^2*y + 36*d₁^2*d₂^2 + 8*d₁*d₂^3*y + 8*d₁*d₂^3 - 4*d₂^4 := by
  rw [sliceDr_cert]
  have h1y : (0:ℝ) ≤ 1 - y := by linarith
  have t0 : (0:ℝ) < 2 * sliceH d₁ d₂ y * d₂^2 := by
    have : (0:ℝ) < d₂^2 := by positivity
    nlinarith
  have e1 : (0:ℝ) ≤ 38*(1 - y)*d₁^3*d₂ := by positivity
  have e2 : (0:ℝ) ≤ (67/2)*(1 - y)*d₁^2*d₂^2 := by positivity
  have e3 : (0:ℝ) ≤ 12*(1 - y)*d₁^4*y := by positivity
  have e4 : (0:ℝ) ≤ (17/2)*(1 - y)*d₁^2*d₂^2*y := by positivity
  have e5 : (0:ℝ) ≤ 6*(1 - y)*d₁^3*d₂*y := by positivity
  have e6 : (0:ℝ) ≤ (9/2)*(d₁ - d₂*y)^2*d₁^2 := by positivity
  have e7 : (0:ℝ) ≤ 3*(1 - y)*d₁^4*y^2 := by positivity
  have e8 : (0:ℝ) ≤ 3*(d₁*y - d₂)^2*d₁^2*y := by positivity
  have e9 : (0:ℝ) ≤ 2*(d₁ - 2*d₂)^2*d₁*d₂ := by positivity
  have e10 : (0:ℝ) ≤ (3/2)*(d₁ - 2*d₂)^2*d₁^2 := by positivity
  have e11 : (0:ℝ) ≤ (d₁ - 2*d₂)^2*d₁*d₂*y := by positivity
  have e12 : (0:ℝ) ≤ (1/2)*(2*d₁ - d₂)^2*d₁^2 := by positivity
  linarith

/-- **A nonnegative quadratic from its coefficients.**  `c₂ x² + c₁ x + c₀ ≥ 0` for `x ≥ 0` when
either `c₁ ≥ 0` and all coefficients are nonnegative, or `4c₂c₀ ≥ c₁²` with `c₂ > 0`. -/
theorem quad_nonneg_two_branches (c₂ c₁ c₀ x : ℝ) (h2 : 0 < c₂) (h0 : 0 ≤ c₀) (hx : 0 ≤ x)
    (hbr : 0 ≤ c₁ ∨ c₁^2 ≤ 4*c₂*c₀) : 0 ≤ c₂*x^2 + c₁*x + c₀ := by
  rcases hbr with h | h
  · have t1 : 0 ≤ c₂*x^2 := by positivity
    have t2 : 0 ≤ c₁*x := mul_nonneg h hx
    linarith
  · -- 4c₂(c₂x² + c₁x + c₀) = (2c₂x + c₁)² + (4c₂c₀ − c₁²)
    have key : 4*c₂*(c₂*x^2 + c₁*x + c₀) = (2*c₂*x + c₁)^2 + (4*c₂*c₀ - c₁^2) := by ring
    have hsq : (0:ℝ) ≤ (2*c₂*x + c₁)^2 := sq_nonneg _
    have hrest : (0:ℝ) ≤ 4*c₂*c₀ - c₁^2 := by linarith
    have h4 : (0:ℝ) < 4*c₂ := by linarith
    nlinarith [key, hsq, hrest]

/-- `inner₂ > 0` on the region: the certificate for the `u = 1−y` endpoint after `d₂ = s d₁`,
`y = 1 − v`.  Needs only `0 ≤ v ≤ 1` and `s ≤ 47/18`. -/
theorem sliceInner2_pos (s v : ℝ) (hs : 0 ≤ s) (hsb : s ≤ 47/18)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ 8*s^3 + 38*s^2*v - 6*s^2 + 48*s*v^2 - 40*s*v + 24*s - 9*v^3 + 6*v^2 + 11*v := by
  have key : 8*s^3 + 38*s^2*v - 6*s^2 + 48*s*v^2 - 40*s*v + 24*s - 9*v^3 + 6*v^2 + 11*v
      = 8*s^3 + 38*s^2*v + s*(47/3 - 6*s) + v*(11 - 3*v)
        + 48*s*(v - 5/12)^2 + 9*v^2*(1 - v) := by ring
  rw [key]
  have h1v : (0:ℝ) ≤ 1 - v := by linarith
  have e1 : (0:ℝ) ≤ 8*s^3 := by positivity
  have e2 : (0:ℝ) ≤ 38*s^2*v := by positivity
  have e3 : (0:ℝ) ≤ s*(47/3 - 6*s) := by
    have : (0:ℝ) ≤ 47/3 - 6*s := by linarith
    exact mul_nonneg hs this
  have e4 : (0:ℝ) ≤ v*(11 - 3*v) := by
    have : (0:ℝ) ≤ 11 - 3*v := by linarith
    exact mul_nonneg hv0 this
  have e5 : (0:ℝ) ≤ 48*s*(v - 5/12)^2 := by positivity
  have e6 : (0:ℝ) ≤ 9*v^2*(1 - v) := by positivity
  linarith

/-- **The side condition is implied by the region.**  On the branch where the middle coefficient
is negative, `2s² ≤ v(5−3v)`; since `v(5−3v) ≤ 25/12` on `[0,1]`, we get `s² ≤ 25/24 < 4`, hence
`s < 2 < 47/18`. -/
theorem slice_s_bound (s v : ℝ) (hs : 0 ≤ s)
    (hreg : 2*s^2 ≤ v*(5 - 3*v)) : s ≤ 47/18 := by
  -- `v(5−3v) ≤ 25/12` holds for every real `v`, since `25/12 − v(5−3v) = 3(v − 5/6)²`
  have hmax : v*(5 - 3*v) ≤ 25/12 := by nlinarith [sq_nonneg (v - 5/6)]
  have hsq : s^2 ≤ 25/24 := by linarith
  nlinarith

/-- **`inner₂ ≥ 0` on the region**, with the side condition discharged. -/
theorem sliceInner2_pos_of_region (s v : ℝ) (hs : 0 ≤ s) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hreg : 2*s^2 ≤ v*(5 - 3*v)) :
    0 ≤ 8*s^3 + 38*s^2*v - 6*s^2 + 48*s*v^2 - 40*s*v + 24*s - 9*v^3 + 6*v^2 + 11*v :=
  sliceInner2_pos s v hs (slice_s_bound s v hs hreg) hv0 hv1

/-- **The `u = 1−y` discriminant, assembled.**  After `d₂ = s d₁`, `y = 1 − v`, the normalised
discriminant is `Dv`, and `Dv = v·inner₂ − 2s²·(2s² − v(5−3v))`.  On the branch where the middle
coefficient is negative we have `2s² ≤ v(5−3v)`, so both parts are nonnegative. -/
theorem sliceDv_nonneg (s v : ℝ) (hs : 0 ≤ s) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hreg : 2*s^2 ≤ v*(5 - 3*v)) :
    0 ≤ -4*s^4 + 8*s^3*v + 32*s^2*v^2 + 4*s^2*v + 48*s*v^3 - 40*s*v^2 + 24*s*v
        - 9*v^4 + 6*v^3 + 11*v^2 := by
  have key : -4*s^4 + 8*s^3*v + 32*s^2*v^2 + 4*s^2*v + 48*s*v^3 - 40*s*v^2 + 24*s*v
        - 9*v^4 + 6*v^3 + 11*v^2
      = v*(8*s^3 + 38*s^2*v - 6*s^2 + 48*s*v^2 - 40*s*v + 24*s - 9*v^3 + 6*v^2 + 11*v)
        - 2*s^2*(2*s^2 - v*(5 - 3*v)) := by ring
  rw [key]
  have h1 : 0 ≤ v*(8*s^3 + 38*s^2*v - 6*s^2 + 48*s*v^2 - 40*s*v + 24*s - 9*v^3 + 6*v^2 + 11*v) :=
    mul_nonneg hv0 (sliceInner2_pos_of_region s v hs hv0 hv1 hreg)
  have h2 : 0 ≤ 2*s^2*(v*(5 - 3*v) - 2*s^2) := by
    have : (0:ℝ) ≤ v*(5 - 3*v) - 2*s^2 := by linarith
    positivity
  nlinarith


/-! ## The loop-gain substitution for the other patterns

The substitution `y = 1 − uw` behaves uniformly across the remaining cases.  Writing `f` for the
free cycle edge (`u` for the patterns whose extra edge leaves state `1`, `w` for those leaving
state `2`), in each case `C₂` becomes free of `f` and `C₁` linear in `f`, exactly as in
`sliceInner_pos` and the lemmas above.

Three facts recorded here, all machine-checked.

**The interval is `[0, 1−r]`, not `[0,1]`.**  The extra edge `z` shares its row with the cycle
edge `r`, so `z ≤ 1 − r`.  Getting this wrong makes the vertex look admissible when it is not:
sampling the convex branch over `[0,1]` produced apparent obstructions, while over `[0, 1−r]` the
vertex landed inside in **zero** of ~5.8·10⁶ convex-branch samples across all four cases.  Every
such case had `C₁ ≥ 0` (vertex `≤ 0`); the alternative "vertex above `1−r`" never occurred.

**Three of the four `d₃`-quadratic cofactors are nonnegative outright.**  Each is a quadratic in
`d₃` with positive outer coefficients and nonpositive discriminant; the certificates are below.

**Two of the four cases coincide.**  After the substitution, the two-cycle-plus-`1→3` pattern
started at state `2` and the two-cycle-plus-`2→3` pattern started at state `1` have the *same*
`C₂y` and the same minimum-endpoint value.  So the four open cases are three distinct problems. -/

/-- The `d₃²` cofactor shared by the `P₁` and `P₅` cofactors. -/
noncomputable def coefA (d₁ d₂ y : ℝ) : ℝ :=
    d₁^2 - 4*d₁*d₂*y + 2*d₁*d₂ + 2*d₂^2*y + d₂^2

/-- The `d₃²` cofactor of the `P₃` case. -/
noncomputable def coefB (d₁ d₂ y : ℝ) : ℝ :=
    2*d₁^2*y + d₁^2 - 4*d₁*d₂*y + 2*d₁*d₂ + d₂^2

/-- The `d₃²` cofactor of the `P₄` case. -/
noncomputable def coefC (d₁ d₂ y : ℝ) : ℝ :=
    d₁^2 - 2*d₁*d₂*y + 2*d₁*d₂ - 5*d₂^2*y^2 + 4*d₂^2*y + d₂^2

theorem coefA_pos (d₁ d₂ y : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 < coefA d₁ d₂ y := by
  have key : coefA d₁ d₂ y
      = 2*(1 - y)*d₁*d₂ + d₂^2 + y*d₂^2 + (1 - y)*y*d₂^2 + (d₁ - d₂*y)^2 := by
    unfold coefA; ring
  rw [key]
  have h1y : (0:ℝ) ≤ 1 - y := by linarith
  have e1 : (0:ℝ) ≤ 2*(1 - y)*d₁*d₂ := by positivity
  have e2 : (0:ℝ) < d₂^2 := by positivity
  have e3 : (0:ℝ) ≤ y*d₂^2 := by positivity
  have e4 : (0:ℝ) ≤ (1 - y)*y*d₂^2 := by positivity
  have e5 : (0:ℝ) ≤ (d₁ - d₂*y)^2 := sq_nonneg _
  linarith

theorem coefB_pos (d₁ d₂ y : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 < coefB d₁ d₂ y := by
  have key : coefB d₁ d₂ y
      = 2*(1 - y)*d₁*d₂ + d₁^2 + y*d₁^2 + (1 - y)*d₂^2 + y*(d₁ - d₂)^2 := by
    unfold coefB; ring
  rw [key]
  have h1y : (0:ℝ) ≤ 1 - y := by linarith
  have e1 : (0:ℝ) ≤ 2*(1 - y)*d₁*d₂ := by positivity
  have e2 : (0:ℝ) < d₁^2 := by positivity
  have e3 : (0:ℝ) ≤ y*d₁^2 := by positivity
  have e4 : (0:ℝ) ≤ (1 - y)*d₂^2 := by positivity
  have e5 : (0:ℝ) ≤ y*(d₁ - d₂)^2 := by positivity
  linarith

theorem coefC_pos (d₁ d₂ y : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 < coefC d₁ d₂ y := by
  have key : coefC d₁ d₂ y
      = 5*(1 - y)*d₂^2*y + 2*(1 - y)*d₁*d₂ + d₁^2 + (1 - y)*d₂^2 := by
    unfold coefC; ring
  rw [key]
  have h1y : (0:ℝ) ≤ 1 - y := by linarith
  have e1 : (0:ℝ) ≤ 5*(1 - y)*d₂^2*y := by positivity
  have e2 : (0:ℝ) ≤ 2*(1 - y)*d₁*d₂ := by positivity
  have e3 : (0:ℝ) < d₁^2 := by positivity
  have e4 : (0:ℝ) ≤ (1 - y)*d₂^2 := by positivity
  linarith

/-! ### The three discriminant certificates

Each cofactor is `c₂d₃² + c₁d₃ + 3d₁²d₂²y²` with `c₂` one of `coefA`, `coefB`, `coefC`.  In each
case `4c₂c₀ − c₁² ≥ 0`, so the quadratic in `d₃` is nonnegative outright. -/

/-- `P₁`: `c₁ = d₁d₂y(−2d₁ + 5d₂y − 2d₂)`, and `4c₂c₀ − c₁² ≥ 0` by a seven-term certificate. -/
theorem coefA_disc_nonneg (d₁ d₂ y : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ 4 * coefA d₁ d₂ y * (3*d₁^2*d₂^2*y^2) - (d₁*d₂*y*(-2*d₁ + 5*d₂*y - 2*d₂))^2 := by
  have key : 4 * coefA d₁ d₂ y * (3*d₁^2*d₂^2*y^2) - (d₁*d₂*y*(-2*d₁ + 5*d₂*y - 2*d₂))^2
      = 25*(1 - y)*d₁^2*d₂^4*y^3 + 16*d₁^3*d₂^3*y^2 + 9*(1 - y)*d₁^3*d₂^3*y^2
        + (19/4)*(1 - y)*d₁^4*d₂^2*y^2 + (19/4)*(d₁ - 2*d₂)^2*d₁^2*d₂^2*y^3
        + (23/12)*(d₁ - 2*d₂)^2*d₁^2*d₂^2*y^2 + (1/3)*(2*d₁ - d₂)^2*d₁^2*d₂^2*y^2 := by
    unfold coefA; ring
  rw [key]
  have h1y : (0:ℝ) ≤ 1 - y := by linarith
  have e1 : (0:ℝ) ≤ 25*(1 - y)*d₁^2*d₂^4*y^3 := by positivity
  have e2 : (0:ℝ) ≤ 16*d₁^3*d₂^3*y^2 := by positivity
  have e3 : (0:ℝ) ≤ 9*(1 - y)*d₁^3*d₂^3*y^2 := by positivity
  have e4 : (0:ℝ) ≤ (19/4)*(1 - y)*d₁^4*d₂^2*y^2 := by positivity
  have e5 : (0:ℝ) ≤ (19/4)*(d₁ - 2*d₂)^2*d₁^2*d₂^2*y^3 := by positivity
  have e6 : (0:ℝ) ≤ (23/12)*(d₁ - 2*d₂)^2*d₁^2*d₂^2*y^2 := by positivity
  have e7 : (0:ℝ) ≤ (1/3)*(2*d₁ - d₂)^2*d₁^2*d₂^2*y^2 := by positivity
  linarith

/-- `P₃`: `c₁ = d₁d₂y(5d₁y − 2d₁ − 2d₂)`. -/
theorem coefB_disc_nonneg (d₁ d₂ y : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ 4 * coefB d₁ d₂ y * (3*d₁^2*d₂^2*y^2) - (d₁*d₂*y*(5*d₁*y - 2*d₁ - 2*d₂))^2 := by
  have key : 4 * coefB d₁ d₂ y * (3*d₁^2*d₂^2*y^2) - (d₁*d₂*y*(5*d₁*y - 2*d₁ - 2*d₂))^2
      = 25*(1 - y)*d₁^4*d₂^2*y^3 + (41/4)*d₁^3*d₂^3*y^2 + 9*(1 - y)*d₁^3*d₂^3*y^2
        + (115/16)*d₁^4*d₂^2*y^2 + (19/4)*(1 - y)*d₁^2*d₂^4*y^2
        + (19/4)*(2*d₁ - d₂)^2*d₁^2*d₂^2*y^3 + (13/16)*(d₁ - 2*d₂)^2*d₁^2*d₂^2*y^2 := by
    unfold coefB; ring
  rw [key]
  have h1y : (0:ℝ) ≤ 1 - y := by linarith
  have e1 : (0:ℝ) ≤ 25*(1 - y)*d₁^4*d₂^2*y^3 := by positivity
  have e2 : (0:ℝ) ≤ (41/4)*d₁^3*d₂^3*y^2 := by positivity
  have e3 : (0:ℝ) ≤ 9*(1 - y)*d₁^3*d₂^3*y^2 := by positivity
  have e4 : (0:ℝ) ≤ (115/16)*d₁^4*d₂^2*y^2 := by positivity
  have e5 : (0:ℝ) ≤ (19/4)*(1 - y)*d₁^2*d₂^4*y^2 := by positivity
  have e6 : (0:ℝ) ≤ (19/4)*(2*d₁ - d₂)^2*d₁^2*d₂^2*y^3 := by positivity
  have e7 : (0:ℝ) ≤ (13/16)*(d₁ - 2*d₂)^2*d₁^2*d₂^2*y^2 := by positivity
  linarith

/-- `P₄`: `c₁ = 2d₁d₂y(−d₁ + d₂y − d₂)`.  Only four terms are needed here. -/
theorem coefC_disc_nonneg (d₁ d₂ y : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ 4 * coefC d₁ d₂ y * (3*d₁^2*d₂^2*y^2) - (2*d₁*d₂*y*(-d₁ + d₂*y - d₂))^2 := by
  have key : 4 * coefC d₁ d₂ y * (3*d₁^2*d₂^2*y^2) - (2*d₁*d₂*y*(-d₁ + d₂*y - d₂))^2
      = 64*(1 - y)*d₁^2*d₂^4*y^3 + 16*(1 - y)*d₁^3*d₂^3*y^2 + 8*d₁^4*d₂^2*y^2
        + 8*(1 - y)*d₁^2*d₂^4*y^2 := by
    unfold coefC; ring
  rw [key]
  have h1y : (0:ℝ) ≤ 1 - y := by linarith
  have e1 : (0:ℝ) ≤ 64*(1 - y)*d₁^2*d₂^4*y^3 := by positivity
  have e2 : (0:ℝ) ≤ 16*(1 - y)*d₁^3*d₂^3*y^2 := by positivity
  have e3 : (0:ℝ) ≤ 8*d₁^4*d₂^2*y^2 := by positivity
  have e4 : (0:ℝ) ≤ 8*(1 - y)*d₁^2*d₂^4*y^2 := by positivity
  linarith

/-- **Nonnegativity of the three cofactors.**  A quadratic in `d₃` with positive leading
coefficient and nonpositive discriminant is nonnegative for every `d₃`. -/
theorem quad_nonneg_of_disc (c₂ c₁ c₀ x : ℝ) (h2 : 0 < c₂) (hd : 0 ≤ 4*c₂*c₀ - c₁^2) :
    0 ≤ c₂*x^2 + c₁*x + c₀ := by
  have key : 4*c₂*(c₂*x^2 + c₁*x + c₀) = (2*c₂*x + c₁)^2 + (4*c₂*c₀ - c₁^2) := by ring
  have hsq : (0:ℝ) ≤ (2*c₂*x + c₁)^2 := sq_nonneg _
  have h4 : (0:ℝ) < 4*c₂ := by linarith
  nlinarith [key, hsq, hd]

/-- The `P₁` cofactor is nonnegative. -/
theorem coefA_cofactor_nonneg (d₁ d₂ d₃ y : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ coefA d₁ d₂ y * d₃^2 + (d₁*d₂*y*(-2*d₁ + 5*d₂*y - 2*d₂)) * d₃ + 3*d₁^2*d₂^2*y^2 :=
  quad_nonneg_of_disc _ _ _ d₃ (coefA_pos d₁ d₂ y hd₁ hd₂ hy0 hy1)
    (coefA_disc_nonneg d₁ d₂ y hd₁ hd₂ hy0 hy1)

/-- The `P₃` cofactor is nonnegative. -/
theorem coefB_cofactor_nonneg (d₁ d₂ d₃ y : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ coefB d₁ d₂ y * d₃^2 + (d₁*d₂*y*(5*d₁*y - 2*d₁ - 2*d₂)) * d₃ + 3*d₁^2*d₂^2*y^2 :=
  quad_nonneg_of_disc _ _ _ d₃ (coefB_pos d₁ d₂ y hd₁ hd₂ hy0 hy1)
    (coefB_disc_nonneg d₁ d₂ y hd₁ hd₂ hy0 hy1)

/-- The `P₄` cofactor is nonnegative. -/
theorem coefC_cofactor_nonneg (d₁ d₂ d₃ y : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ coefC d₁ d₂ y * d₃^2 + (2*d₁*d₂*y*(-d₁ + d₂*y - d₂)) * d₃ + 3*d₁^2*d₂^2*y^2 :=
  quad_nonneg_of_disc _ _ _ d₃ (coefC_pos d₁ d₂ y hd₁ hd₂ hy0 hy1)
    (coefC_disc_nonneg d₁ d₂ y hd₁ hd₂ hy0 hy1)

end SSP.Chain
