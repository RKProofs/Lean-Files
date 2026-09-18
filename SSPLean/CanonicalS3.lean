import SSPLean.CycleThree
import SSPLean.ChainInequality

/-!
# Conjecture 1 at `k = 2`, `s = 3`, via the canonical representation

This file formalises the proof in `k2_s3_complete.tex`.  The point of that argument is that it
avoids the eighteen-case enumeration of `k2_hierarchy.tex` entirely: instead of classifying
cyclic support patterns, it invokes the unicyclic canonical form for order-three phase-type
laws, which is a *single* routing graph.

The statement is `12a₁a₃ ≥ 10a₂²`, where `aⱼ = α(−T)^{-j}𝟙 = E[Xʲ]/j!`.

## The argument

1.  **The unicyclic representation.**  Every order-three phase-type law has a
    distribution-equivalent Markovian representation `(π, A)` with
    `A = [[-x₁,0,x₁₃],[x₂,-x₂,0],[0,x₃,-x₃]]`, `x₁ ≥ x₂ ≥ x₃ > 0`, `0 ≤ x₁₃ < x₁`.

    *Attribution.*  This is **He–Zhang**, *A note on unicyclic representation of
    PH-distributions*, Stochastic Models **21** (2005) 465–483.  It appears as Theorem 1 of
    Horváth–Telek, *On the canonical representation of phase type distributions*, Performance
    Evaluation **66** (2009) 396–409, where it is cited to He–Zhang rather than proved;
    Horváth–Telek's own contribution (their Theorems 2 and 3) is to fix the free parameter `x₁`
    so that the *initial vector* `π` is also Markovian, and to handle non-Markovian input
    representations.  `k2_s3_complete.tex` cites Horváth–Telek for the representation; the
    primary source for the statement used here is He–Zhang.

    It is a cited theorem, not proved here and not stated as a Lean definition: it is the one
    step this file takes on faith.  Everything below works with the canonical `A` written out
    explicitly, so the gap is exactly "every order-three phase-type law has such a
    representation" — nothing more.

2.  **The canonical routing graph is a three-cycle.**  With `D = diag(x₁,x₂,x₃)` and
    `A = −D(I−P)`, one gets `p₁₃ = x₁₃/x₁`, `p₂₁ = 1`, `p₃₂ = 1`: the directed cycle
    `1 → 3 → 2 → 1`, with loop gain `x₁₃/x₁ < 1`.  Relabelling states `2 ↔ 3` turns it into
    the cycle `1 → 2 → 3 → 1` of `SSPLean.CycleThree`, under the correspondence
    `(d₁,d₂,d₃) = (x₁,x₃,x₂)` and `(u,w,v) = (x₁₃/x₁, 1, 1)`.

3.  **Each deterministic start.**  Two of the three starts land on the `v = 1` face and are
    given by `cycF_face_nonneg` outright.  The third needs `cycFN d₁ d₂ d₃ 1 1 v`, which is
    *concave* in `v`; its `v = 1` endpoint is again `cycF_face_nonneg`, and its `v = 0` endpoint
    is the acyclic value, certified here by a symmetric six-term sum of squares
    (`cycF_v0_at_uw_one_cert`).

4.  **Mixing over `π`.**  `mixture_closure_sq` (already in `SSPLean.ChainInequality`) transfers
    the inequality from deterministic starts to any initial distribution, by Cauchy–Schwarz.

Only step 1 is an external input.  Steps 2–4 are proved.
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.style.whitespace false

namespace SSP.Canonical

open SSP.Chain

/-! ### The acyclic endpoint at `u = w = 1` -/

/-- The `v = 0` value of `cycFN` at `u = w = 1`, over the factor `2`. -/
noncomputable def cycFV0 (d₁ d₂ d₃ : ℝ) : ℝ :=
    d₁^4*d₂^4 + 2*d₁^4*d₂^3*d₃ - 3*d₁^4*d₂^2*d₃^2 + 2*d₁^4*d₂*d₃^3 + d₁^4*d₃^4
      + 2*d₁^3*d₂^4*d₃ - 2*d₁^3*d₂^3*d₃^2 - 2*d₁^3*d₂^2*d₃^3 + 2*d₁^3*d₂*d₃^4
      - 3*d₁^2*d₂^4*d₃^2 - 2*d₁^2*d₂^3*d₃^3 - 3*d₁^2*d₂^2*d₃^4
      + 2*d₁*d₂^4*d₃^3 + 2*d₁*d₂^3*d₃^4 + d₂^4*d₃^4

/-- **A symmetric sum-of-squares certificate.**  Fully symmetric in `d₁, d₂, d₃`, as it must be:
at `u = w = v` the three-cycle is invariant under the rotation. -/
theorem cycFV0_cert (d₁ d₂ d₃ : ℝ) :
    cycFV0 d₁ d₂ d₃
      = 2*d₁^4*d₂*d₃*(d₂ - d₃)^2 + 2*d₁*d₂^4*d₃*(d₁ - d₃)^2 + 2*d₁*d₂*d₃^4*(d₁ - d₂)^2
        + d₁^2*d₂^2*(d₁*d₂ - d₃^2)^2 + d₂^2*d₃^2*(d₁^2 - d₂*d₃)^2
        + d₁^2*d₃^2*(d₂^2 - d₁*d₃)^2 := by
  unfold cycFV0; ring

theorem cycFV0_nonneg (d₁ d₂ d₃ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃) :
    0 ≤ cycFV0 d₁ d₂ d₃ := by
  rw [cycFV0_cert]
  have e1 : (0:ℝ) ≤ 2*d₁^4*d₂*d₃*(d₂ - d₃)^2 := by positivity
  have e2 : (0:ℝ) ≤ 2*d₁*d₂^4*d₃*(d₁ - d₃)^2 := by positivity
  have e3 : (0:ℝ) ≤ 2*d₁*d₂*d₃^4*(d₁ - d₂)^2 := by positivity
  have e4 : (0:ℝ) ≤ d₁^2*d₂^2*(d₁*d₂ - d₃^2)^2 := by positivity
  have e5 : (0:ℝ) ≤ d₂^2*d₃^2*(d₁^2 - d₂*d₃)^2 := by positivity
  have e6 : (0:ℝ) ≤ d₁^2*d₃^2*(d₂^2 - d₁*d₃)^2 := by positivity
  linarith

/-- `cycFN d₁ d₂ d₃ 1 1 0 = 2·cycFV0 d₁ d₂ d₃`. -/
theorem cycFN_uw_one_v_zero (d₁ d₂ d₃ : ℝ) :
    cycFN d₁ d₂ d₃ 1 1 0 = 2 * cycFV0 d₁ d₂ d₃ := by
  unfold cycFN cycFV0; ring

/-! ### The `u = w = 1` slice is concave in `v` -/

/-- The `v²` cofactor of `cycFN d₁ d₂ d₃ 1 1 v`. -/
noncomputable def cycFLone (d₁ d₂ d₃ : ℝ) : ℝ :=
    5*d₁^2 + 4*d₁*d₂ + 4*d₁*d₃ + 5*d₂^2 + 4*d₂*d₃ + 5*d₃^2

theorem cycFLone_pos (d₁ d₂ d₃ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃) :
    0 < cycFLone d₁ d₂ d₃ := by
  unfold cycFLone; positivity

/-- Lagrange form of `cycFN d₁ d₂ d₃ 1 1 v` in `v`, exhibiting the negative leading
coefficient `−2d₁²d₂²d₃²·cycFLone`. -/
theorem cycFN_uw_one_quadratic (d₁ d₂ d₃ v : ℝ) :
    cycFN d₁ d₂ d₃ 1 1 v
      = (-(2*d₁^2*d₂^2*d₃^2) * cycFLone d₁ d₂ d₃) * v^2
        + (cycFN d₁ d₂ d₃ 1 1 1 - cycFN d₁ d₂ d₃ 1 1 0
            + 2*d₁^2*d₂^2*d₃^2 * cycFLone d₁ d₂ d₃) * v
        + cycFN d₁ d₂ d₃ 1 1 0 := by
  unfold cycFN cycFLone; ring

/-- **The `u = w = 1` slice is nonnegative for every `v ∈ [0,1]`.**  Concave in `v`, with the
`v = 1` endpoint given by `cycF_face_nonneg` and the `v = 0` endpoint by `cycFV0_nonneg`. -/
theorem cycFN_uw_one_nonneg (d₁ d₂ d₃ v : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : 0 ≤ cycFN d₁ d₂ d₃ 1 1 v := by
  have hzero : 0 ≤ cycFN d₁ d₂ d₃ 1 1 0 := by
    rw [cycFN_uw_one_v_zero]
    have := cycFV0_nonneg d₁ d₂ d₃ hd₁ hd₂ hd₃
    linarith
  have hone : 0 ≤ cycFN d₁ d₂ d₃ 1 1 1 :=
    cycF_face_nonneg d₁ d₂ d₃ 1 1 hd₁ hd₂ hd₃ zero_le_one le_rfl zero_le_one le_rfl
  rw [cycFN_uw_one_quadratic]
  refine concave_quad_ge_min_endpoints _ _ _ v ?_ hv0 hv1 hzero ?_
  · have hL := cycFLone_pos d₁ d₂ d₃ hd₁ hd₂ hd₃
    have h : (0:ℝ) ≤ 2*d₁^2*d₂^2*d₃^2 := by positivity
    nlinarith [mul_nonneg h (le_of_lt hL)]
  · linarith

/-! ### The three deterministic starts of the canonical form

Under the correspondence `(d₁,d₂,d₃) = (x₁,x₃,x₂)`, `u = x₁₃/x₁`, `w = v = 1`, the cyclic
symmetry of the three-cycle sends the three start-state numerators to

* canonical start `1` ↦ `cycFN x₁ x₃ x₂ u 1 1`,
* canonical start `2` ↦ `cycFN x₂ x₁ x₃ 1 u 1`,
* canonical start `3` ↦ `cycFN x₃ x₂ x₁ 1 1 u`,

the first two of which are `v = 1` faces and the third the `u = w = 1` slice above. -/

/-- **Canonical start 1.** -/
theorem canonical_start1 (x₁ x₂ x₃ u : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ cycFN x₁ x₃ x₂ u 1 1 :=
  cycF_face_nonneg x₁ x₃ x₂ u 1 hx₁ hx₃ hx₂ hu0 hu1 zero_le_one le_rfl

/-- **Canonical start 2.** -/
theorem canonical_start2 (x₁ x₂ x₃ u : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ cycFN x₂ x₁ x₃ 1 u 1 :=
  cycF_face_nonneg x₂ x₁ x₃ 1 u hx₂ hx₁ hx₃ zero_le_one le_rfl hu0 hu1

/-- **Canonical start 3.**  This is the slice needing the concavity argument. -/
theorem canonical_start3 (x₁ x₂ x₃ u : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ cycFN x₃ x₂ x₁ 1 1 u :=
  cycFN_uw_one_nonneg x₃ x₂ x₁ u hx₃ hx₂ hx₁ hu0 hu1

/-! ### The canonical moments, explicitly

For the canonical `A` the resolvent is rational with the single denominator
`x₂x₃(x₁−x₁₃)`, so `aⱼ` from start `i` is `canA{i}_{j} / (x₂x₃(x₁−x₁₃))^j`.  The definitions
below are the numerators; they come straight from `(−A)^{-j}𝟙`. -/

/-- Numerator of `a1` from canonical start `1`, over `(x₂x₃(x₁−x₁₃))^1`. -/
noncomputable def canA1_1 (x₁ x₂ x₃ x₁₃ : ℝ) : ℝ :=
    x₁₃*x₂ + x₁₃*x₃ + x₂*x₃

/-- Numerator of `a2` from canonical start `1`, over `(x₂x₃(x₁−x₁₃))^2`. -/
noncomputable def canA1_2 (x₁ x₂ x₃ x₁₃ : ℝ) : ℝ :=
    x₁*x₁₃*x₂^2 + x₁*x₁₃*x₂*x₃ + x₁*x₁₃*x₃^2 + x₁₃^2*x₂*x₃ + 2*x₁₃*x₂^2*x₃ + 2*x₁₃*x₂*x₃^2
      + x₂^2*x₃^2

/-- Numerator of `a3` from canonical start `1`, over `(x₂x₃(x₁−x₁₃))^3`. -/
noncomputable def canA1_3 (x₁ x₂ x₃ x₁₃ : ℝ) : ℝ :=
    x₁^2*x₁₃*x₂^3 + x₁^2*x₁₃*x₂^2*x₃ + x₁^2*x₁₃*x₂*x₃^2 + x₁^2*x₁₃*x₃^3 + 2*x₁*x₁₃^2*x₂^2*x₃
      + 2*x₁*x₁₃^2*x₂*x₃^2 + 2*x₁*x₁₃*x₂^3*x₃ + 2*x₁*x₁₃*x₂^2*x₃^2 + 2*x₁*x₁₃*x₂*x₃^3
      + x₁₃^2*x₂^3*x₃ + 4*x₁₃^2*x₂^2*x₃^2 + x₁₃^2*x₂*x₃^3 + 3*x₁₃*x₂^3*x₃^2 + 3*x₁₃*x₂^2*x₃^3
      + x₂^3*x₃^3

/-- Numerator of `a1` from canonical start `2`, over `(x₂x₃(x₁−x₁₃))^1`. -/
noncomputable def canA2_1 (x₁ x₂ x₃ x₁₃ : ℝ) : ℝ :=
    x₁*x₃ + x₁₃*x₂ + x₂*x₃

/-- Numerator of `a2` from canonical start `2`, over `(x₂x₃(x₁−x₁₃))^2`. -/
noncomputable def canA2_2 (x₁ x₂ x₃ x₁₃ : ℝ) : ℝ :=
    x₁^2*x₃^2 + x₁*x₁₃*x₂^2 + 2*x₁*x₁₃*x₂*x₃ + x₁*x₂*x₃^2 + 2*x₁₃*x₂^2*x₃ + x₁₃*x₂*x₃^2
      + x₂^2*x₃^2

/-- Numerator of `a3` from canonical start `2`, over `(x₂x₃(x₁−x₁₃))^3`. -/
noncomputable def canA2_3 (x₁ x₂ x₃ x₁₃ : ℝ) : ℝ :=
    x₁^3*x₃^3 + x₁^2*x₁₃*x₂^3 + 2*x₁^2*x₁₃*x₂^2*x₃ + 3*x₁^2*x₁₃*x₂*x₃^2 + x₁^2*x₂*x₃^3
      + x₁*x₁₃^2*x₂^2*x₃ + 2*x₁*x₁₃*x₂^3*x₃ + 4*x₁*x₁₃*x₂^2*x₃^2 + 2*x₁*x₁₃*x₂*x₃^3
      + x₁*x₂^2*x₃^3 + x₁₃^2*x₂^3*x₃ + 2*x₁₃^2*x₂^2*x₃^2 + 3*x₁₃*x₂^3*x₃^2 + 2*x₁₃*x₂^2*x₃^3
      + x₂^3*x₃^3

/-- Numerator of `a1` from canonical start `3`, over `(x₂x₃(x₁−x₁₃))^1`. -/
noncomputable def canA3_1 (x₁ x₂ x₃ x₁₃ : ℝ) : ℝ :=
    x₁*x₂ + x₁*x₃ + x₂*x₃

/-- Numerator of `a2` from canonical start `3`, over `(x₂x₃(x₁−x₁₃))^2`. -/
noncomputable def canA3_2 (x₁ x₂ x₃ x₁₃ : ℝ) : ℝ :=
    x₁^2*x₂^2 + x₁^2*x₂*x₃ + x₁^2*x₃^2 + x₁*x₁₃*x₂*x₃ + x₁*x₂^2*x₃ + x₁*x₂*x₃^2 + x₁₃*x₂^2*x₃
      + x₁₃*x₂*x₃^2 + x₂^2*x₃^2

/-- Numerator of `a3` from canonical start `3`, over `(x₂x₃(x₁−x₁₃))^3`. -/
noncomputable def canA3_3 (x₁ x₂ x₃ x₁₃ : ℝ) : ℝ :=
    x₁^3*x₂^3 + x₁^3*x₂^2*x₃ + x₁^3*x₂*x₃^2 + x₁^3*x₃^3 + 2*x₁^2*x₁₃*x₂^2*x₃ + 2*x₁^2*x₁₃*x₂*x₃^2
      + x₁^2*x₂^3*x₃ + x₁^2*x₂^2*x₃^2 + x₁^2*x₂*x₃^3 + 2*x₁*x₁₃*x₂^3*x₃ + 4*x₁*x₁₃*x₂^2*x₃^2
      + 2*x₁*x₁₃*x₂*x₃^3 + x₁*x₂^3*x₃^2 + x₁*x₂^2*x₃^3 + x₁₃^2*x₂^2*x₃^2 + 2*x₁₃*x₂^3*x₃^2
      + 2*x₁₃*x₂^2*x₃^3 + x₂^3*x₃^3

/-! ### Identification with the actual moments

The definitions `canAi_j` were transcribed from `(−A)^{-j}𝟙`.  To make that a theorem rather
than a transcription, note that the moment vectors `vⱼ = (−A)^{-j}𝟙` are characterised without
any matrix inverse, by the linear recursion

  `(−A)·vⱼ = vⱼ₋₁`,   `v₀ = 𝟙`.

Scaling by the common denominator `den = x₂x₃(x₁−x₁₃)`, the numerator vectors
`wⱼ = den^j · vⱼ` satisfy

  `(−A)·wⱼ = den · wⱼ₋₁`,   `w₀ = 𝟙`,

which is a polynomial identity.  Proving it for `j = 1,2,3` pins the `canAi_j` down completely:
`−A` is invertible when `den ≠ 0`, so the recursion has a unique solution.  No inverse, no
`Matrix.adjugate`, just `ring` on each of the nine components. -/

/-- The canonical subgenerator's negation, `−A`, as a `Fin 3` matrix. -/
noncomputable def negA (x₁ x₂ x₃ x₁₃ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    match i, j with
    | 0, 0 => x₁   | 0, 1 => 0    | 0, 2 => -x₁₃
    | 1, 0 => -x₂  | 1, 1 => x₂   | 1, 2 => 0
    | 2, 0 => 0    | 2, 1 => -x₃  | 2, 2 => x₃

/-- The common denominator `den = x₂x₃(x₁−x₁₃)`, which is `det(−A)`. -/
noncomputable def canDen (x₁ x₂ x₃ x₁₃ : ℝ) : ℝ := x₂*x₃*(x₁ - x₁₃)

/-- `det(−A) = den`.  So `−A` is invertible exactly when `den ≠ 0`, i.e. when `x₁₃ ≠ x₁` and the
rates are nonzero. -/
theorem det_negA (x₁ x₂ x₃ x₁₃ : ℝ) :
    (negA x₁ x₂ x₃ x₁₃).det = canDen x₁ x₂ x₃ x₁₃ := by
  rw [Matrix.det_fin_three]
  unfold negA canDen
  simp [Matrix.of_apply]
  ring

/-- The numerator vector `w₁`. -/
noncomputable def canW1 (x₁ x₂ x₃ x₁₃ : ℝ) : Fin 3 → ℝ :=
  fun i => match i with
    | 0 => canA1_1 x₁ x₂ x₃ x₁₃
    | 1 => canA2_1 x₁ x₂ x₃ x₁₃
    | 2 => canA3_1 x₁ x₂ x₃ x₁₃

/-- The numerator vector `w₂`. -/
noncomputable def canW2 (x₁ x₂ x₃ x₁₃ : ℝ) : Fin 3 → ℝ :=
  fun i => match i with
    | 0 => canA1_2 x₁ x₂ x₃ x₁₃
    | 1 => canA2_2 x₁ x₂ x₃ x₁₃
    | 2 => canA3_2 x₁ x₂ x₃ x₁₃

/-- The numerator vector `w₃`. -/
noncomputable def canW3 (x₁ x₂ x₃ x₁₃ : ℝ) : Fin 3 → ℝ :=
  fun i => match i with
    | 0 => canA1_3 x₁ x₂ x₃ x₁₃
    | 1 => canA2_3 x₁ x₂ x₃ x₁₃
    | 2 => canA3_3 x₁ x₂ x₃ x₁₃

/-- **`(−A)·w₁ = den·𝟙`.**  This is the `j = 1` case of the recursion. -/
theorem negA_mulVec_W1 (x₁ x₂ x₃ x₁₃ : ℝ) (i : Fin 3) :
    (negA x₁ x₂ x₃ x₁₃).mulVec (canW1 x₁ x₂ x₃ x₁₃) i = canDen x₁ x₂ x₃ x₁₃ * 1 := by
  fin_cases i <;>
    · show (∑ j, negA x₁ x₂ x₃ x₁₃ _ j * _) = _
      rw [Fin.sum_univ_three]
      simp only [negA, canDen, canW1, canW2, canW3, Matrix.of_apply,
        canA1_1, canA2_1, canA3_1, canA1_2, canA2_2, canA3_2, canA1_3, canA2_3, canA3_3]
      ring

/-- **`(−A)·w₂ = den·w₁`.** -/
theorem negA_mulVec_W2 (x₁ x₂ x₃ x₁₃ : ℝ) (i : Fin 3) :
    (negA x₁ x₂ x₃ x₁₃).mulVec (canW2 x₁ x₂ x₃ x₁₃) i
      = canDen x₁ x₂ x₃ x₁₃ * canW1 x₁ x₂ x₃ x₁₃ i := by
  fin_cases i <;>
    · show (∑ j, negA x₁ x₂ x₃ x₁₃ _ j * _) = _
      rw [Fin.sum_univ_three]
      simp only [negA, canDen, canW1, canW2, canW3, Matrix.of_apply,
        canA1_1, canA2_1, canA3_1, canA1_2, canA2_2, canA3_2, canA1_3, canA2_3, canA3_3]
      ring

/-- **`(−A)·w₃ = den·w₂`.** -/
theorem negA_mulVec_W3 (x₁ x₂ x₃ x₁₃ : ℝ) (i : Fin 3) :
    (negA x₁ x₂ x₃ x₁₃).mulVec (canW3 x₁ x₂ x₃ x₁₃) i
      = canDen x₁ x₂ x₃ x₁₃ * canW2 x₁ x₂ x₃ x₁₃ i := by
  fin_cases i <;>
    · show (∑ j, negA x₁ x₂ x₃ x₁₃ _ j * _) = _
      rw [Fin.sum_univ_three]
      simp only [negA, canDen, canW1, canW2, canW3, Matrix.of_apply,
        canA1_1, canA2_1, canA3_1, canA1_2, canA2_2, canA3_2, canA1_3, canA2_3, canA3_3]
      ring


/-! #### Uniqueness: the recursion pins the `wⱼ` down

`det(−A) = den`, so when `den ≠ 0` the matrix `−A` is invertible and each equation
`(−A)·wⱼ = den·wⱼ₋₁` has a *unique* solution.  Hence the `canAi_j` are not merely *a* solution
of the recursion — they are `den^j·(−A)^{-j}𝟙`, i.e. `den^j` times the moment vector `aⱼ`.

That is the identification the earlier version of this file lacked. -/

/-- `−A` is invertible when `den ≠ 0`. -/
theorem negA_isUnit_det (x₁ x₂ x₃ x₁₃ : ℝ) (hden : canDen x₁ x₂ x₃ x₁₃ ≠ 0) :
    IsUnit (negA x₁ x₂ x₃ x₁₃).det := by
  rw [det_negA]
  exact isUnit_iff_ne_zero.mpr hden

/-- **The `wⱼ` are `den^j·(−A)^{-j}𝟙`.**  Stated as: `(−A)^{-1}` applied to `den·wⱼ₋₁` returns
`wⱼ`, so by induction `wⱼ = den^j·(−A)^{-j}𝟙`.

We record the three instances; each is `mulVec_injective`-style reasoning from the
corresponding recursion, using invertibility of `−A`. -/
theorem canW1_eq_inv (x₁ x₂ x₃ x₁₃ : ℝ) (hden : canDen x₁ x₂ x₃ x₁₃ ≠ 0) :
    canW1 x₁ x₂ x₃ x₁₃
      = (negA x₁ x₂ x₃ x₁₃)⁻¹.mulVec (fun _ => canDen x₁ x₂ x₃ x₁₃) := by
  have hu := negA_isUnit_det x₁ x₂ x₃ x₁₃ hden
  have h : (negA x₁ x₂ x₃ x₁₃).mulVec (canW1 x₁ x₂ x₃ x₁₃)
      = fun _ => canDen x₁ x₂ x₃ x₁₃ := by
    funext i
    have := negA_mulVec_W1 x₁ x₂ x₃ x₁₃ i
    simpa using this
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem canW2_eq_inv (x₁ x₂ x₃ x₁₃ : ℝ) (hden : canDen x₁ x₂ x₃ x₁₃ ≠ 0) :
    canW2 x₁ x₂ x₃ x₁₃
      = (negA x₁ x₂ x₃ x₁₃)⁻¹.mulVec
          (fun i => canDen x₁ x₂ x₃ x₁₃ * canW1 x₁ x₂ x₃ x₁₃ i) := by
  have hu := negA_isUnit_det x₁ x₂ x₃ x₁₃ hden
  have h : (negA x₁ x₂ x₃ x₁₃).mulVec (canW2 x₁ x₂ x₃ x₁₃)
      = fun i => canDen x₁ x₂ x₃ x₁₃ * canW1 x₁ x₂ x₃ x₁₃ i := by
    funext i; exact negA_mulVec_W2 x₁ x₂ x₃ x₁₃ i
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem canW3_eq_inv (x₁ x₂ x₃ x₁₃ : ℝ) (hden : canDen x₁ x₂ x₃ x₁₃ ≠ 0) :
    canW3 x₁ x₂ x₃ x₁₃
      = (negA x₁ x₂ x₃ x₁₃)⁻¹.mulVec
          (fun i => canDen x₁ x₂ x₃ x₁₃ * canW2 x₁ x₂ x₃ x₁₃ i) := by
  have hu := negA_isUnit_det x₁ x₂ x₃ x₁₃ hden
  have h : (negA x₁ x₂ x₃ x₁₃).mulVec (canW3 x₁ x₂ x₃ x₁₃)
      = fun i => canDen x₁ x₂ x₃ x₁₃ * canW2 x₁ x₂ x₃ x₁₃ i := by
    funext i; exact negA_mulVec_W3 x₁ x₂ x₃ x₁₃ i
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/-- **`den ≠ 0` on the admissible region.** -/
theorem canDen_pos (x₁ x₂ x₃ x₁₃ : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hlt : x₁₃ < x₁) : 0 < canDen x₁ x₂ x₃ x₁₃ := by
  unfold canDen
  have h : (0:ℝ) < x₁ - x₁₃ := by linarith
  positivity


/-- **The identification.**  Together with `canW1_eq_inv`, `canW2_eq_inv` and `canW3_eq_inv`,
this says the `canAi_j` are exactly `den^j` times the moment vectors `aⱼ = (−A)^{-j}𝟙`.

It is stated as the recursion rather than as an iterated inverse because that is what makes the
uniqueness visible: `det(−A) = den > 0`, so `−A` is invertible, and `w₀ = 𝟙` together with
`(−A)wⱼ = den·wⱼ₋₁` determines every `wⱼ` uniquely.  Hence `canAi_j / den^j` is the `i`-th
component of `aⱼ` — the `j`-th normalised moment from deterministic start `i` — and the
inequality proved in this file is genuinely about the moments. -/
theorem canW_recursion (x₁ x₂ x₃ x₁₃ : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hlt : x₁₃ < x₁) :
    (∀ i, (negA x₁ x₂ x₃ x₁₃).mulVec (canW1 x₁ x₂ x₃ x₁₃) i = canDen x₁ x₂ x₃ x₁₃ * 1) ∧
    (∀ i, (negA x₁ x₂ x₃ x₁₃).mulVec (canW2 x₁ x₂ x₃ x₁₃) i
            = canDen x₁ x₂ x₃ x₁₃ * canW1 x₁ x₂ x₃ x₁₃ i) ∧
    (∀ i, (negA x₁ x₂ x₃ x₁₃).mulVec (canW3 x₁ x₂ x₃ x₁₃) i
            = canDen x₁ x₂ x₃ x₁₃ * canW2 x₁ x₂ x₃ x₁₃ i) ∧
    IsUnit (negA x₁ x₂ x₃ x₁₃).det :=
  ⟨negA_mulVec_W1 x₁ x₂ x₃ x₁₃, negA_mulVec_W2 x₁ x₂ x₃ x₁₃, negA_mulVec_W3 x₁ x₂ x₃ x₁₃,
   negA_isUnit_det x₁ x₂ x₃ x₁₃ (ne_of_gt (canDen_pos x₁ x₂ x₃ x₁₃ hx₁ hx₂ hx₃ hlt))⟩

/-! ### The link to the three-cycle

For each start, `12·a₁a₃ − 10·a₂²` has denominator `(x₂x₃(x₁−x₁₃))⁴`, and its numerator is
*exactly* `cycFN` at the corresponding rotation — a polynomial identity, with the powers of `x₁`
from `u = x₁₃/x₁` cancelling on their own.  This is where the canonical form meets the work of
`SSPLean.CycleThree`. -/

/-- **Start 1.** -/
theorem canonical_link1 (x₁ x₂ x₃ x₁₃ : ℝ) (_hx₁ : x₁ ≠ 0) :
    12 * canA1_1 x₁ x₂ x₃ x₁₃ * canA1_3 x₁ x₂ x₃ x₁₃ - 10 * (canA1_2 x₁ x₂ x₃ x₁₃)^2
      = cycFN x₁ x₃ x₂ (x₁₃/x₁) 1 1 := by
  unfold canA1_1 canA1_2 canA1_3 cycFN
  field_simp
  ring

/-- **Start 2.** -/
theorem canonical_link2 (x₁ x₂ x₃ x₁₃ : ℝ) (hx₁ : x₁ ≠ 0) :
    12 * canA2_1 x₁ x₂ x₃ x₁₃ * canA2_3 x₁ x₂ x₃ x₁₃ - 10 * (canA2_2 x₁ x₂ x₃ x₁₃)^2
      = cycFN x₂ x₁ x₃ 1 (x₁₃/x₁) 1 := by
  unfold canA2_1 canA2_2 canA2_3 cycFN
  field_simp
  ring

/-- **Start 3.** -/
theorem canonical_link3 (x₁ x₂ x₃ x₁₃ : ℝ) (hx₁ : x₁ ≠ 0) :
    12 * canA3_1 x₁ x₂ x₃ x₁₃ * canA3_3 x₁ x₂ x₃ x₁₃ - 10 * (canA3_2 x₁ x₂ x₃ x₁₃)^2
      = cycFN x₃ x₂ x₁ 1 1 (x₁₃/x₁) := by
  unfold canA3_1 canA3_2 canA3_3 cycFN
  field_simp
  ring

/-! ### The inequality at each canonical deterministic start

Combining the link identities with the three-cycle results gives `12a₁a₃ ≥ 10a₂²` from every
deterministic start of the canonical representation.  The hypothesis `0 ≤ x₁₃ < x₁` is exactly
what makes `u = x₁₃/x₁` lie in `[0,1)`. -/

/-- `0 ≤ x₁₃ < x₁` gives `u = x₁₃/x₁ ∈ [0,1]`. -/
theorem loop_gain_mem (x₁ x₁₃ : ℝ) (hx₁ : 0 < x₁) (h0 : 0 ≤ x₁₃) (hlt : x₁₃ < x₁) :
    0 ≤ x₁₃/x₁ ∧ x₁₃/x₁ ≤ 1 := by
  refine ⟨div_nonneg h0 (le_of_lt hx₁), ?_⟩
  rw [div_le_one hx₁]; exact le_of_lt hlt

/-- **Canonical start 1: the inequality.** -/
theorem canonical_ineq1 (x₁ x₂ x₃ x₁₃ : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (h0 : 0 ≤ x₁₃) (hlt : x₁₃ < x₁) :
    10 * (canA1_2 x₁ x₂ x₃ x₁₃)^2 ≤ 12 * (canA1_1 x₁ x₂ x₃ x₁₃ * canA1_3 x₁ x₂ x₃ x₁₃) := by
  obtain ⟨hu0, hu1⟩ := loop_gain_mem x₁ x₁₃ hx₁ h0 hlt
  have h := canonical_start1 x₁ x₂ x₃ (x₁₃/x₁) hx₁ hx₂ hx₃ hu0 hu1
  have e := canonical_link1 x₁ x₂ x₃ x₁₃ (ne_of_gt hx₁)
  linarith [e ▸ h]

/-- **Canonical start 2: the inequality.** -/
theorem canonical_ineq2 (x₁ x₂ x₃ x₁₃ : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (h0 : 0 ≤ x₁₃) (hlt : x₁₃ < x₁) :
    10 * (canA2_2 x₁ x₂ x₃ x₁₃)^2 ≤ 12 * (canA2_1 x₁ x₂ x₃ x₁₃ * canA2_3 x₁ x₂ x₃ x₁₃) := by
  obtain ⟨hu0, hu1⟩ := loop_gain_mem x₁ x₁₃ hx₁ h0 hlt
  have h := canonical_start2 x₁ x₂ x₃ (x₁₃/x₁) hx₁ hx₂ hx₃ hu0 hu1
  have e := canonical_link2 x₁ x₂ x₃ x₁₃ (ne_of_gt hx₁)
  linarith [e ▸ h]

/-- **Canonical start 3: the inequality.** -/
theorem canonical_ineq3 (x₁ x₂ x₃ x₁₃ : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (h0 : 0 ≤ x₁₃) (hlt : x₁₃ < x₁) :
    10 * (canA3_2 x₁ x₂ x₃ x₁₃)^2 ≤ 12 * (canA3_1 x₁ x₂ x₃ x₁₃ * canA3_3 x₁ x₂ x₃ x₁₃) := by
  obtain ⟨hu0, hu1⟩ := loop_gain_mem x₁ x₁₃ hx₁ h0 hlt
  have h := canonical_start3 x₁ x₂ x₃ (x₁₃/x₁) hx₁ hx₂ hx₃ hu0 hu1
  have e := canonical_link3 x₁ x₂ x₃ x₁₃ (ne_of_gt hx₁)
  linarith [e ▸ h]

/-! ### Mixing over the initial distribution

`mixture_closure_sq` is stated for `κ·(Σwᵢyᵢ)² ≤ (Σwᵢxᵢ)(Σwᵢzᵢ)`.  With `κ = 5/6`,
`xᵢ = a₁` from start `i`, `yᵢ = a₂`, `zᵢ = a₃`, and `wᵢ = πᵢ`, this is exactly the statement
that `12a₁a₃ ≥ 10a₂²` passes from deterministic starts to the mixture. -/

/-- **The mixture step, in the form needed.**  If every deterministic start satisfies
`12a₁a₃ ≥ 10a₂²`, so does any convex — indeed any nonnegative — combination. -/
theorem mixture_step {ι : Type*} (t : Finset ι) (π a₁ a₂ a₃ : ι → ℝ)
    (hπ : ∀ i ∈ t, 0 ≤ π i) (h1 : ∀ i ∈ t, 0 ≤ a₁ i) (h2 : ∀ i ∈ t, 0 ≤ a₂ i)
    (h3 : ∀ i ∈ t, 0 ≤ a₃ i)
    (hstart : ∀ i ∈ t, 10 * (a₂ i)^2 ≤ 12 * (a₁ i * a₃ i)) :
    10 * (∑ i ∈ t, π i * a₂ i)^2
      ≤ 12 * ((∑ i ∈ t, π i * a₁ i) * (∑ i ∈ t, π i * a₃ i)) := by
  have hκ : (0:ℝ) ≤ 5/6 := by norm_num
  have hcomp : ∀ i ∈ t, (5/6) * (a₂ i)^2 ≤ a₁ i * a₃ i := by
    intro i hi
    have := hstart i hi
    linarith
  have h := SSP.Chain.mixture_closure_sq t π a₁ a₂ a₃ (5/6) hκ hπ h1 h3 h2 hcomp
  linarith

/-! ### The main theorem

Assembling: the three deterministic starts, then the mixture step.  The `aⱼ` of the canonical
representation with initial vector `π = (π₁,π₂,π₃)` are
`aⱼ = π₁·a⁽¹⁾ⱼ + π₂·a⁽²⁾ⱼ + π₃·a⁽³⁾ⱼ`, each `a⁽ⁱ⁾ⱼ = canAi_j / (x₂x₃(x₁−x₁₃))^j`.  Since the
common denominator is the same positive number for all three starts at a given `j`, it may be
cleared, and the statement is about the numerators. -/

/-- Positivity of each canonical numerator: needed as an input to the mixture step. -/
theorem canA_pos (x₁ x₂ x₃ x₁₃ : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (h0 : 0 ≤ x₁₃) :
    0 < canA1_1 x₁ x₂ x₃ x₁₃ ∧ 0 < canA1_2 x₁ x₂ x₃ x₁₃ ∧ 0 < canA1_3 x₁ x₂ x₃ x₁₃ ∧
    0 < canA2_1 x₁ x₂ x₃ x₁₃ ∧ 0 < canA2_2 x₁ x₂ x₃ x₁₃ ∧ 0 < canA2_3 x₁ x₂ x₃ x₁₃ ∧
    0 < canA3_1 x₁ x₂ x₃ x₁₃ ∧ 0 < canA3_2 x₁ x₂ x₃ x₁₃ ∧ 0 < canA3_3 x₁ x₂ x₃ x₁₃ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold canA1_1; positivity
  · unfold canA1_2; positivity
  · unfold canA1_3; positivity
  · unfold canA2_1; positivity
  · unfold canA2_2; positivity
  · unfold canA2_3; positivity
  · unfold canA3_1; positivity
  · unfold canA3_2; positivity
  · unfold canA3_3; positivity

/-- **Conjecture 1 at `k = 2`, `s = 3`, for the canonical representation with any initial
distribution.**

`π` is indexed by `Fin 3`; `A j i` is the numerator of `aⱼ` from deterministic start `i`.  The
conclusion is `12a₁a₃ ≥ 10a₂²` for the mixture — the numerator form of `\eqref{eq:goal}`.

Given the He–Zhang unicyclic representation (an external input, see the file header), this is the
`k = 2`, `s = 3` case of Conjecture 1 for *every* phase-type law of order at most three. -/
theorem canonical_hierarchy_s3 (x₁ x₂ x₃ x₁₃ : ℝ) (π : Fin 3 → ℝ)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃) (h0 : 0 ≤ x₁₃) (hlt : x₁₃ < x₁)
    (hπ : ∀ i, 0 ≤ π i)
    (A₁ A₂ A₃ : Fin 3 → ℝ)
    (hA₁ : A₁ = fun i => [canA1_1 x₁ x₂ x₃ x₁₃, canA2_1 x₁ x₂ x₃ x₁₃, canA3_1 x₁ x₂ x₃ x₁₃].get i)
    (hA₂ : A₂ = fun i => [canA1_2 x₁ x₂ x₃ x₁₃, canA2_2 x₁ x₂ x₃ x₁₃, canA3_2 x₁ x₂ x₃ x₁₃].get i)
    (hA₃ : A₃ = fun i => [canA1_3 x₁ x₂ x₃ x₁₃, canA2_3 x₁ x₂ x₃ x₁₃, canA3_3 x₁ x₂ x₃ x₁₃].get i) :
    10 * (∑ i, π i * A₂ i)^2 ≤ 12 * ((∑ i, π i * A₁ i) * (∑ i, π i * A₃ i)) := by
  obtain ⟨p11, p12, p13, p21, p22, p23, p31, p32, p33⟩ := canA_pos x₁ x₂ x₃ x₁₃ hx₁ hx₂ hx₃ h0
  refine mixture_step Finset.univ π A₁ A₂ A₃ (fun i _ => hπ i) ?_ ?_ ?_ ?_
  · intro i _; subst hA₁; fin_cases i <;> simp <;> linarith
  · intro i _; subst hA₂; fin_cases i <;> simp <;> linarith
  · intro i _; subst hA₃; fin_cases i <;> simp <;> linarith
  · intro i _; subst hA₁; subst hA₂; subst hA₃; fin_cases i <;> simp
    · exact canonical_ineq1 x₁ x₂ x₃ x₁₃ hx₁ hx₂ hx₃ h0 hlt
    · exact canonical_ineq2 x₁ x₂ x₃ x₁₃ hx₁ hx₂ hx₃ h0 hlt
    · exact canonical_ineq3 x₁ x₂ x₃ x₁₃ hx₁ hx₂ hx₃ h0 hlt

/-! ### The moment form of the main theorem

The numerator statement `canonical_hierarchy_s3` divided through by the positive constants
`den^j` gives the inequality for the actual normalised moments `aⱼ = π·(−A)^{-j}𝟙`.  Since
`a₁a₃` carries `den^4` and `a₂²` carries `den^4` as well, the constants cancel exactly. -/

/-- `aⱼ` from deterministic start `i`, as `canAi_j / den^j`. -/
noncomputable def canMoment (x₁ x₂ x₃ x₁₃ : ℝ) (j : Fin 3) (i : Fin 3) : ℝ :=
  match j with
  | 0 => (fun i => canW1 x₁ x₂ x₃ x₁₃ i / canDen x₁ x₂ x₃ x₁₃) i
  | 1 => (fun i => canW2 x₁ x₂ x₃ x₁₃ i / (canDen x₁ x₂ x₃ x₁₃)^2) i
  | 2 => (fun i => canW3 x₁ x₂ x₃ x₁₃ i / (canDen x₁ x₂ x₃ x₁₃)^3) i

/-- **Conjecture 1 at `k = 2`, `s = 3`, in moment form.**

`12·a₁a₃ ≥ 10·a₂²` for the canonical order-three representation with any nonnegative initial
vector `π`, where `aⱼ` is the genuine `j`-th normalised moment `π(−A)^{-j}𝟙` (identified by
`canW_recursion` together with `canW*_eq_inv`).

This is the statement of `k2_s3_complete.tex`, conditional only on the He–Zhang unicyclic
representation. -/
theorem canonical_hierarchy_s3_moments (x₁ x₂ x₃ x₁₃ : ℝ) (π : Fin 3 → ℝ)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃) (h0 : 0 ≤ x₁₃) (hlt : x₁₃ < x₁)
    (hπ : ∀ i, 0 ≤ π i) :
    10 * (∑ i, π i * canMoment x₁ x₂ x₃ x₁₃ 1 i)^2
      ≤ 12 * ((∑ i, π i * canMoment x₁ x₂ x₃ x₁₃ 0 i)
              * (∑ i, π i * canMoment x₁ x₂ x₃ x₁₃ 2 i)) := by
  have hc : 0 < canDen x₁ x₂ x₃ x₁₃ := canDen_pos x₁ x₂ x₃ x₁₃ hx₁ hx₂ hx₃ hlt
  set c := canDen x₁ x₂ x₃ x₁₃ with hcdef
  -- pull the constant out of each sum
  have e0 : (∑ i, π i * canMoment x₁ x₂ x₃ x₁₃ 0 i)
      = (∑ i, π i * canW1 x₁ x₂ x₃ x₁₃ i) / c := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [canMoment, hcdef]; ring
  have e1 : (∑ i, π i * canMoment x₁ x₂ x₃ x₁₃ 1 i)
      = (∑ i, π i * canW2 x₁ x₂ x₃ x₁₃ i) / c^2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [canMoment, hcdef]; ring
  have e2 : (∑ i, π i * canMoment x₁ x₂ x₃ x₁₃ 2 i)
      = (∑ i, π i * canW3 x₁ x₂ x₃ x₁₃ i) / c^3 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [canMoment, hcdef]; ring
  rw [e0, e1, e2]
  -- the numerator inequality
  have key := canonical_hierarchy_s3 x₁ x₂ x₃ x₁₃ π hx₁ hx₂ hx₃ h0 hlt hπ
    (canW1 x₁ x₂ x₃ x₁₃) (canW2 x₁ x₂ x₃ x₁₃) (canW3 x₁ x₂ x₃ x₁₃)
    (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl)
  set S₁ := ∑ i, π i * canW1 x₁ x₂ x₃ x₁₃ i
  set S₂ := ∑ i, π i * canW2 x₁ x₂ x₃ x₁₃ i
  set S₃ := ∑ i, π i * canW3 x₁ x₂ x₃ x₁₃ i
  -- both sides carry exactly `c⁴`, so the constant cancels
  have hc4 : (0:ℝ) < c^4 := by positivity
  have hrw : 10 * (S₂ / c^2)^2 = (10 * S₂^2) / c^4 := by field_simp
  have hrw2 : 12 * ((S₁ / c) * (S₃ / c^3)) = (12 * (S₁ * S₃)) / c^4 := by field_simp
  rw [hrw, hrw2]
  gcongr

end SSP.Canonical
