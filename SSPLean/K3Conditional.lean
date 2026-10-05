import SSPLean.K3S3Canonical
import SSPLean.K3AllStagesComplete
import SSPLean.FourthMomentBridge

/-!
# The abstract `k = 3` hierarchy interface

The `k = 3` development in this repository supplies the *algebraic* induction step for every
order `n ≥ 4` (`SSPLean.K3AllStages*`, culminating in
`SSP.K3AllStages.excursionReducedGap_mixture_coordinates_nonneg`), together with concrete
unconditional base cases at `s = 2` (`transientStageBoundK3_two`) and a concrete `s = 3` case
that is conditional on a He--Zhang similarity representation
(`transientStageBoundK3_three_of_similarity`).

The induction is factored through the following two inputs:

1. `K3Inputs.base3` — the order-three base case.
2. `K3Inputs.step` — the state-return induction step in concrete moment coordinates.

This module proves the strong induction and mixture closure from that interface.  Both fields
are discharged in `SSPLean.K3Complete`.
-/

open Finset

namespace SSP.K2Concrete

/-- The two inputs used by the factored concrete `k = 3` induction. -/
structure K3Inputs : Prop where
  /-- The order-three base case. -/
  base3 : ∀ X : TransientStart 3,
    K3StageBound 3 (transientMoment2 3 X) (transientMoment3 3 X) (transientMoment4 3 X)
  /-- The state-return induction step in concrete moment coordinates: if both excursion laws,
  of order `< n`, satisfy the bound at their own order, then so does the parent at order `n`.
  The excursions are presented at the parent order `n - 1`, which is how the state-return
  decomposition produces them. -/
  step : ∀ n, 4 ≤ n → ∀ X : TransientStart n,
    (∀ Y : TransientInitial (n - 1),
      K3StageBound (n - 1) (transientInitialMoment2 (n - 1) Y)
        (transientInitialMoment3 (n - 1) Y) (transientInitialMoment4 (n - 1) Y)) →
    K3StageBound n (transientMoment2 n X) (transientMoment3 n X) (transientMoment4 n X)

/-- The one-state base case for `k = 3`.  A single transient state gives an exponential law,
for which the `s = 1` bound `4 m₃² ≤ 3 m₂ m₄` is an identity-driven inequality. -/
theorem transientStageBoundK3_one (X : TransientStart 1) :
    K3StageBound 1 (transientMoment2 1 X) (transientMoment3 1 X)
      (transientMoment4 1 X) := by
  unfold K3StageBound transientMoment2 transientMoment3 transientMoment4
  have hi : X.i = (0 : Fin 1) := Subsingleton.elim _ _
  rw [hi]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, mul_one]
  ring_nf
  nlinarith [sq_nonneg ((1 - X.Q)⁻¹ 0 0)]

/-- Monotonicity of the `k = 3` bound in the stage count: a bound proved with a smaller stage
count remains true with any larger one. -/
theorem k3StageBound_mono {s N : ℕ} {m₂ m₃ m₄ : ℝ}
    (hsN : s ≤ N) (hm₂ : 0 ≤ m₂) (hm₄ : 0 ≤ m₄)
    (h : K3StageBound s m₂ m₃ m₄) : K3StageBound N m₂ m₃ m₄ := by
  unfold K3StageBound at h ⊢
  have hcast : (s : ℝ) ≤ (N : ℝ) := by exact_mod_cast hsN
  have hm24 : 0 ≤ m₂ * m₄ := mul_nonneg hm₂ hm₄
  nlinarith [h, hm24, hcast]

/-- Mixture closure for the `k = 3` bound over a subprobability initial vector. -/
theorem transientInitialStageBoundK3_of_components {s : ℕ} (X : TransientInitial s)
    (hdet : ∀ i, K3StageBound s (transientMoment2 s (X.component i))
      (transientMoment3 s (X.component i)) (transientMoment4 s (X.component i))) :
    K3StageBound s (transientInitialMoment2 s X) (transientInitialMoment3 s X)
      (transientInitialMoment4 s X) := by
  have hmix := SSP.Chain.mixture_closure_sq (Finset.univ : Finset (Fin s)) X.weight
    (fun i => transientMoment2 s (X.component i))
    (fun i => transientMoment3 s (X.component i))
    (fun i => transientMoment4 s (X.component i))
    (((s : ℝ) + 3) / ((s : ℝ) + 2))
    (by positivity)
    (fun i _ => X.weight_nonneg i)
    (fun i _ => transientMoment2_nonneg (X.component i))
    (fun i _ => transientMoment4_nonneg (X.component i))
    (fun i _ => transientMoment3_nonneg (X.component i))
    (fun i _ => by
      have h := hdet i
      unfold K3StageBound at h
      have hs2 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hs2]
      nlinarith [h])
  unfold K3StageBound transientInitialMoment2 transientInitialMoment3
    transientInitialMoment4
  have hs2 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hs2] at hmix
  nlinarith [hmix]

/-- **The `k = 3` hierarchy for every order, from the two isolated inputs.**  The strong
induction, the low-order cases `s = 1, 2`, and the mixture closure are all proved; the only
hypotheses are the two fields of `K3Inputs`. -/
theorem all_transient_starts_k3_of_inputs (h : K3Inputs) :
    ∀ n, 1 ≤ n → ∀ X : TransientStart n,
      K3StageBound n (transientMoment2 n X) (transientMoment3 n X)
        (transientMoment4 n X) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hnpos X
      by_cases hn3 : n ≤ 3
      · have hs : n = 1 ∨ n = 2 ∨ n = 3 := by omega
        rcases hs with rfl | rfl | rfl
        · -- order one: the single-state law is exponential, handled by the s = 2 bound
          exact k3StageBound_mono (by omega) (transientMoment2_nonneg X)
            (transientMoment4_nonneg X) (transientStageBoundK3_one X)
        · exact transientStageBoundK3_two X
        · exact h.base3 X
      · have hn4 : 4 ≤ n := by omega
        refine h.step n hn4 X ?_
        intro Y
        apply transientInitialStageBoundK3_of_components
        intro i
        exact ih (n - 1) (by omega) (by omega) (Y.component i)

/-- Initial-distribution form of the previous theorem. -/
theorem all_transient_initial_k3_of_inputs (h : K3Inputs) {s : ℕ} (hs : 1 ≤ s)
    (X : TransientInitial s) :
    K3StageBound s (transientInitialMoment2 s X) (transientInitialMoment3 s X)
      (transientInitialMoment4 s X) := by
  apply transientInitialStageBoundK3_of_components
  intro i
  exact all_transient_starts_k3_of_inputs h s hs (X.component i)

end SSP.K2Concrete
