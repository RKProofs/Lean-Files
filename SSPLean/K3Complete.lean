import SSPLean.K3Conditional
import SSPLean.K3StepGlue
import SSPLean.K3S3Complete

/-!
# Unconditional `k = 3` moment hierarchy

The three-state base case is `transientStageBoundK3_three_unconditional`.  The general
state-return step is `k3StageBound_step`; its two degenerate branches are obtained as limits
of the already-proved positive-return scalar theorem.  Together they discharge both fields
of `K3Inputs`.
-/

namespace SSP.K2Concrete

/-- Both inputs to the abstract `k = 3` induction are unconditional. -/
theorem k3Inputs_unconditional : K3Inputs where
  base3 := transientStageBoundK3_three_unconditional
  step := fun _ hn X hind => k3StageBound_step hn X hind

/-- Every deterministic finite transient law satisfies the `k = 3` hierarchy inequality. -/
theorem all_transient_starts_k3 :
    ∀ n, 1 ≤ n → ∀ X : TransientStart n,
      K3StageBound n (transientMoment2 n X) (transientMoment3 n X)
        (transientMoment4 n X) :=
  all_transient_starts_k3_of_inputs k3Inputs_unconditional

/-- Initial-distribution form of the unconditional `k = 3` hierarchy. -/
theorem all_transient_initial_k3 {s : ℕ} (hs : 1 ≤ s) (X : TransientInitial s) :
    K3StageBound s (transientInitialMoment2 s X) (transientInitialMoment3 s X)
      (transientInitialMoment4 s X) :=
  all_transient_initial_k3_of_inputs k3Inputs_unconditional hs X

end SSP.K2Concrete

open Finset

namespace SSP.MainRevised

/-- **Conjecture `hierarchy` at `k = 3`, unconditionally.**  The `k = 3` instance of the
log-convexity hierarchy for the phase-type law of an arbitrary nonnegative substochastic
matrix `Q` with invertible `I - Q` and an arbitrary subprobability initial weight vector
`w`. -/
theorem hierarchy_k3 (s : ℕ) (hs : 1 ≤ s) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ (SSP.toMat s Q) i j)
    (hrow : ∀ i : Fin s, ∑ j, (SSP.toMat s Q) i j ≤ 1)
    (hu : IsUnit (1 - SSP.toMat s Q))
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i : Fin s, w (i : ℕ) ≤ 1) :
    SSP.LogConvexBound3 s (SSP.invMat s Q) w := by
  have hspos : 0 < s := hs
  let X : SSP.K2Concrete.TransientInitial s :=
    { model :=
        { Q := SSP.toMat s Q, hQ := hQ, hrow := hrow, hu := hu, i := ⟨0, hspos⟩ }
      weight := fun i => w (i : ℕ)
      weight_nonneg := fun i => hw _
      weight_sum_le_one := hw1 }
  have h := SSP.K2Concrete.all_transient_initial_k3 hs X
  unfold SSP.LogConvexBound3
  have e2 : ∀ i : Fin s, SSP.rowSum2 s (SSP.invMat s Q) (i : ℕ)
      = ((1 - SSP.toMat s Q)⁻¹.mulVec
          ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i := by
    intro i
    simpa using SSP.Bridge.rowSum2_invMat_eq Q (i : ℕ) i.isLt
  have e3 : ∀ i : Fin s, SSP.rowSum3 s (SSP.invMat s Q) (i : ℕ)
      = ((1 - SSP.toMat s Q)⁻¹.mulVec ((1 - SSP.toMat s Q)⁻¹.mulVec
          ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i := by
    intro i
    simpa using SSP.Bridge.rowSum3_invMat_eq Q (i : ℕ) i.isLt
  have e4 : ∀ i : Fin s, SSP.rowSum4 s (SSP.invMat s Q) (i : ℕ)
      = ((1 - SSP.toMat s Q)⁻¹.mulVec ((1 - SSP.toMat s Q)⁻¹.mulVec
          ((1 - SSP.toMat s Q)⁻¹.mulVec
            ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ)))))) i := by
    intro i
    simpa using SSP.Bridge.rowSum4_invMat_eq Q (i : ℕ) i.isLt
  rw [← Fin.sum_univ_eq_sum_range
        (fun i => w i * SSP.rowSum3 s (SSP.invMat s Q) i) s,
      ← Fin.sum_univ_eq_sum_range
        (fun i => w i * SSP.rowSum2 s (SSP.invMat s Q) i) s,
      ← Fin.sum_univ_eq_sum_range
        (fun i => w i * SSP.rowSum4 s (SSP.invMat s Q) i) s]
  simp_rw [e2, e3, e4]
  have c2 : ∑ i : Fin s, X.weight i *
        (2 * ((1 - (X.component i).Q)⁻¹.mulVec
          ((1 - (X.component i).Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) (X.component i).i)
      = 2 * ∑ i : Fin s, w (i : ℕ) *
        ((1 - SSP.toMat s Q)⁻¹.mulVec
          ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp [X, SSP.K2Concrete.TransientInitial.component]
      ring
  have c6 : ∑ i : Fin s, X.weight i *
        (6 * ((1 - (X.component i).Q)⁻¹.mulVec ((1 - (X.component i).Q)⁻¹.mulVec
          ((1 - (X.component i).Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) (X.component i).i)
      = 6 * ∑ i : Fin s, w (i : ℕ) *
        ((1 - SSP.toMat s Q)⁻¹.mulVec ((1 - SSP.toMat s Q)⁻¹.mulVec
          ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp [X, SSP.K2Concrete.TransientInitial.component]
      ring
  have c24 : ∑ i : Fin s, X.weight i *
        (24 * ((1 - (X.component i).Q)⁻¹.mulVec ((1 - (X.component i).Q)⁻¹.mulVec
          ((1 - (X.component i).Q)⁻¹.mulVec
            ((1 - (X.component i).Q)⁻¹.mulVec (fun _ => (1 : ℝ))))))
          (X.component i).i)
      = 24 * ∑ i : Fin s, w (i : ℕ) *
        ((1 - SSP.toMat s Q)⁻¹.mulVec ((1 - SSP.toMat s Q)⁻¹.mulVec
          ((1 - SSP.toMat s Q)⁻¹.mulVec
            ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ)))))) i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp [X, SSP.K2Concrete.TransientInitial.component]
      ring
  unfold SSP.K2Concrete.K3StageBound SSP.K2Concrete.transientInitialMoment2
    SSP.K2Concrete.transientInitialMoment3 SSP.K2Concrete.transientInitialMoment4
    SSP.K2Concrete.transientMoment2 SSP.K2Concrete.transientMoment3
    SSP.K2Concrete.transientMoment4 at h
  rw [c2, c6, c24] at h
  have hs2 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hs2]
  nlinarith [h]

end SSP.MainRevised
