import SSPLean.AbsorptionLaw
import SSPLean.MomentBridge
import SSPLean.QSequenceCrossing

/-!
# The Aldous–Shepp least-variability theorem, unconditionally

Aldous and Shepp (1987) proved that the absorption time `X` of a continuous-time Markov chain with
at most `s` transient states satisfies `Var(X) ≥ (E[X])²/s`, by a continuous-time martingale
argument.

`SSPLean.AldousShepp` derives the same inequality from the matrix `ComponentBound`, but takes the
phase-type moment dictionary as a hypothesis.  This file removes that hypothesis: the law of `X` is
*constructed* (`SSPLean.SurvivalMonotone`), `X = id` is *identified* as the absorption time
(`SSP.Law.measure_Ioi_eq_survival`), and both moments are *computed*
(`SSP.Law.expectation_eq`, `SSP.Law.second_moment_eq`).

So the only input is `SSP.componentBound_unconditional` — the paper's Lemma 5, proved in
`SSPLean.QSequenceCrossing` by an elementary weighted-paths/crossing argument.  No martingale
theory, and no continuous-time Markov chain theory, appears anywhere.

## The chain

```
componentBound_unconditional          (Lemma 5, elementary)
  ↓  rowSum_Nmat_eq_invMat, rowSum_invMat_eq            (MomentBridge)
((I−Q)⁻¹𝟙)ᵢ² ≤ (2s/(s+1))·((I−Q)⁻¹((I−Q)⁻¹𝟙))ᵢ
  ↑  expectation_eq, second_moment_eq                   (AbsorptionLaw)
E[X]² ≤ (2s/(s+1))·(E[X²]/2)
  ↓  algebra
Var(X) ≥ (E[X])²/s
```
-/

open scoped Matrix.Norms.Operator
open NormedSpace Matrix SSP.Semigroup SSP.Survival SSP.Law SSP.Bridge Set MeasureTheory

set_option autoImplicit false

namespace SSP

/-- **The Aldous–Shepp least-variability theorem.**

For a nonnegative substochastic `Q` with `ρ(Q) < 1` and `‖Q‖ ≤ θ < 1`, let `μ` be the law of the
absorption time started at transient state `i`, constructed in `SSPLean.SurvivalMonotone`, and let
`X = id` be the absorption time itself.  Then

```
  (E[X])² / s ≤ E[X²] − (E[X])² = Var(X) .
```

Every ingredient is proved: the law, the identification of `X`, both moments, and the component
bound.  Nothing is assumed. -/
theorem aldous_shepp {s : ℕ} (Q : ℕ → ℕ → ℝ) (θ : ℝ) (hs : 0 < s)
    (hQ : ∀ i j, 0 ≤ Q i j) (hsub : ∀ i < s, ∑ j ∈ Finset.range s, Q i j ≤ 1)
    (hρ : spectralRadius ℂ ((SSP.toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (hQm : ∀ i j : Fin s, 0 ≤ (SSP.toMat s Q) i j)
    (hrowm : ∀ i : Fin s, ∑ j, (SSP.toMat s Q) i j ≤ 1)
    (hu : IsUnit (1 - SSP.toMat s Q)) (hnorm : ‖SSP.toMat s Q‖ ≤ θ) (hθ : θ < 1)
    (i : Fin s) :
    (∫ x, id x ∂(survivalStieltjes (SSP.toMat s Q) hQm hrowm i).measure)^2 / s
      ≤ (∫ x, (id x)^2 ∂(survivalStieltjes (SSP.toMat s Q) hQm hrowm i).measure)
        - (∫ x, id x ∂(survivalStieltjes (SSP.toMat s Q) hQm hrowm i).measure)^2 := by
  rw [expectation_eq (SSP.toMat s Q) θ hQm hrowm hu hnorm hθ i,
      second_moment_eq (SSP.toMat s Q) θ hQm hrowm hu hnorm hθ i]
  have hCB := SSP.componentBound_unconditional s Q hQ hsub hρ hs (i : ℕ) i.isLt
  rw [rowSum_Nmat_eq_invMat Q hρ i i.isLt, rowSum2_Nmat_eq_invMat Q hρ i i.isLt,
      rowSum_invMat_eq Q (i:ℕ) i.isLt, rowSum2_invMat_eq Q (i:ℕ) i.isLt] at hCB
  have hsp : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs
  have hs1 : (0:ℝ) < (s:ℝ) + 1 := by linarith
  rw [div_le_iff₀ hsp]
  rw [div_mul_eq_mul_div, le_div_iff₀ hs1] at hCB
  nlinarith [hCB]

end SSP
