/-
Copyright (c) 2026. All rights reserved.
-/
import SSPLean.AldousSheppFinal

/-!
# The converse: Aldous–Shepp implies the componentwise bound

`AldousSheppFinal.lean` proves `ComponentBound ⟹ Aldous–Shepp`.  This file proves the
reverse implication, so the two statements are *equivalent*, not merely one-directional.

## Why a converse is available at all

The forward proof passes through the **moment dictionary**

* `E[X]   = ((1-Q)⁻¹𝟙)ᵢ        ` (`expectation_eq`)
* `E[X²]  = 2((1-Q)⁻¹(1-Q)⁻¹𝟙)ᵢ` (`second_moment_eq`)

Both are *equalities*, hence substitutable in either direction, and the remaining step

  `Var ≥ (E X)²/s   ⟺   (E X)² ≤ (s/(s+1))·E[X²]   ⟺   (N𝟙)ᵢ² ≤ (2s/(s+1))(N²𝟙)ᵢ`

is a chain of multiplications by the positive constants `s` and `s+1`.  So the equivalence
is an honest biconditional and not an artifact of a lossy estimate.

## What the hypotheses are doing

`hu`, `hnorm`, `hθ` are needed **only to evaluate the two integrals** (integrability and
the decay that makes the tail integrals converge); they carry no part of the inequality.
`hρ` is needed only for the `Nmat = invMat` bridge, i.e. to phrase the conclusion with the
Neumann series `Nmat` rather than the resolvent.  The mathematical content transferred in
each direction is exactly the scalar inequality.

## Main results

* `componentBound_at_of_aldous_shepp` — the converse at a fixed state `i`.
* `componentBound_of_aldous_shepp`    — the converse for all `i`, giving `ComponentBound`.
* `aldous_shepp_iff_componentBound_at` — the equivalence at a fixed `i`.
-/

open scoped Matrix.Norms.Operator
open NormedSpace Matrix SSP.Semigroup SSP.Survival SSP.Law SSP.Bridge Set MeasureTheory

set_option autoImplicit false

namespace SSP

/-- **Converse of Aldous–Shepp, at a fixed initial state.**

If the variance inequality `(E X)²/s ≤ Var X` holds for the absorption time started at `i`,
then the paper's componentwise bound holds at `i`.  This is the exact reverse of the final
algebraic step of `aldous_shepp`. -/
theorem componentBound_at_of_aldous_shepp {s : ℕ} (Q : ℕ → ℕ → ℝ) (θ : ℝ) (hs : 0 < s)
    (hρ : spectralRadius ℂ ((SSP.toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (hQm : ∀ i j : Fin s, 0 ≤ (SSP.toMat s Q) i j)
    (hrowm : ∀ i : Fin s, ∑ j, (SSP.toMat s Q) i j ≤ 1)
    (hu : IsUnit (1 - SSP.toMat s Q)) (hnorm : ‖SSP.toMat s Q‖ ≤ θ) (hθ : θ < 1)
    (i : Fin s)
    (hAS : (∫ x, id x ∂(survivalStieltjes (SSP.toMat s Q) hQm hrowm i).measure)^2 / s
      ≤ (∫ x, (id x)^2 ∂(survivalStieltjes (SSP.toMat s Q) hQm hrowm i).measure)
        - (∫ x, id x ∂(survivalStieltjes (SSP.toMat s Q) hQm hrowm i).measure)^2) :
    (rowSum s (Nmat s Q) i) ^ 2 ≤ (2 * s / (s + 1)) * rowSum2 s (Nmat s Q) i := by
  -- Replace the two integrals by their closed forms (the dictionary, used right-to-left).
  rw [expectation_eq (SSP.toMat s Q) θ hQm hrowm hu hnorm hθ i,
      second_moment_eq (SSP.toMat s Q) θ hQm hrowm hu hnorm hθ i] at hAS
  -- Move the goal onto the resolvent side, matching `hAS`.
  rw [rowSum_Nmat_eq_invMat Q hρ i i.isLt, rowSum2_Nmat_eq_invMat Q hρ i i.isLt,
      rowSum_invMat_eq Q (i:ℕ) i.isLt, rowSum2_invMat_eq Q (i:ℕ) i.isLt]
  -- Positivity of the two constants we divide by.
  have hsp : (0:ℝ) < s := by exact_mod_cast hs
  have hs1 : (0:ℝ) < (s:ℝ) + 1 := by linarith
  rw [div_le_iff₀ hsp] at hAS
  rw [div_mul_eq_mul_div, le_div_iff₀ hs1]
  nlinarith [hAS]

/-- **Converse of Aldous–Shepp.**  If the variance inequality holds from *every* initial
state, the paper's `ComponentBound` follows. -/
theorem componentBound_of_aldous_shepp {s : ℕ} (Q : ℕ → ℕ → ℝ) (θ : ℝ) (hs : 0 < s)
    (hρ : spectralRadius ℂ ((SSP.toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (hQm : ∀ i j : Fin s, 0 ≤ (SSP.toMat s Q) i j)
    (hrowm : ∀ i : Fin s, ∑ j, (SSP.toMat s Q) i j ≤ 1)
    (hu : IsUnit (1 - SSP.toMat s Q)) (hnorm : ‖SSP.toMat s Q‖ ≤ θ) (hθ : θ < 1)
    (hAS : ∀ i : Fin s,
      (∫ x, id x ∂(survivalStieltjes (SSP.toMat s Q) hQm hrowm i).measure)^2 / s
        ≤ (∫ x, (id x)^2 ∂(survivalStieltjes (SSP.toMat s Q) hQm hrowm i).measure)
          - (∫ x, id x ∂(survivalStieltjes (SSP.toMat s Q) hQm hrowm i).measure)^2) :
    ComponentBound s (Nmat s Q) := by
  intro i hi
  exact componentBound_at_of_aldous_shepp Q θ hs hρ hQm hrowm hu hnorm hθ ⟨i, hi⟩ (hAS ⟨i, hi⟩)

/-- **The two statements are equivalent.**

At a fixed initial state, the Aldous–Shepp variance inequality and the paper's componentwise
bound are the *same* assertion, transported across the moment dictionary.  Forward is
`aldous_shepp` (via `componentBound_unconditional`); backward is
`componentBound_at_of_aldous_shepp`. -/
theorem aldous_shepp_iff_componentBound_at {s : ℕ} (Q : ℕ → ℕ → ℝ) (θ : ℝ) (hs : 0 < s)
    (hQ : ∀ i j, 0 ≤ Q i j) (hsub : ∀ i < s, ∑ j ∈ Finset.range s, Q i j ≤ 1)
    (hρ : spectralRadius ℂ ((SSP.toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (hQm : ∀ i j : Fin s, 0 ≤ (SSP.toMat s Q) i j)
    (hrowm : ∀ i : Fin s, ∑ j, (SSP.toMat s Q) i j ≤ 1)
    (hu : IsUnit (1 - SSP.toMat s Q)) (hnorm : ‖SSP.toMat s Q‖ ≤ θ) (hθ : θ < 1)
    (i : Fin s) :
    ((∫ x, id x ∂(survivalStieltjes (SSP.toMat s Q) hQm hrowm i).measure)^2 / s
        ≤ (∫ x, (id x)^2 ∂(survivalStieltjes (SSP.toMat s Q) hQm hrowm i).measure)
          - (∫ x, id x ∂(survivalStieltjes (SSP.toMat s Q) hQm hrowm i).measure)^2)
      ↔ (rowSum s (Nmat s Q) i) ^ 2 ≤ (2 * s / (s + 1)) * rowSum2 s (Nmat s Q) i := by
  refine ⟨componentBound_at_of_aldous_shepp Q θ hs hρ hQm hrowm hu hnorm hθ i, fun _ => ?_⟩
  exact aldous_shepp Q θ hs hQ hsub hρ hQm hrowm hu hnorm hθ i

end SSP
