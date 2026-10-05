import SSPLean.K3S3Step
import SSPLean.K3S3Concrete

/-!
# Unconditional `k = 3`, three-state theorem

The two degenerate state-return branches are supplied by `K3S3Concrete`.
In the genuinely cyclic branch, both conditioned excursions have at most two
states, so the existing two-state `k = 2` and `k = 3` bounds feed the complete
three-stage scalar renewal step.
-/

open Finset

namespace SSP.K2Concrete

open SSP.K3S4Renewal SSP.K3AllStages

/-- The genuinely cyclic, nondegenerate branch of the three-state theorem. -/
theorem transientStageBoundK3_three_of_positive_return
    (X : TransientStart 3) (hp : 0 < transientReturnProbability X)
    (hv : 0 < transientInitialMoment1 2
      (transientTerminalConditionedInitial X (by omega)
        (transientTerminalProbability_pos X))) :
    K3StageBound 3 (transientMoment2 3 X) (transientMoment3 3 X)
      (transientMoment4 3 X) := by
  have hs : 2 ≤ (3 : ℕ) := by omega
  let U := transientReturnConditionedInitial X hs hp
  let V := transientTerminalConditionedInitial X hs
    (transientTerminalProbability_pos X)
  let u := transientInitialMoment1 2 U
  let A := transientInitialMoment2 2 U
  let C := transientInitialMoment3 2 U
  let E := transientInitialMoment4 2 U
  let v := transientInitialMoment1 2 V
  let B := transientInitialMoment2 2 V
  let D := transientInitialMoment3 2 V
  let F := transientInitialMoment4 2 V
  let x := transientHoldingMean X
  let p := transientReturnProbability X
  let q := transientTerminalProbability X
  let r := p/q
  have hq : 0 < q := by dsimp [q]; exact transientTerminalProbability_pos X
  have hu : 0 < u := by
    apply transientInitialMoment1_pos_of_weight_sum_pos
    dsimp [U]
    rw [transientReturnConditionedInitial_weight_sum X hs hp]
    norm_num
  have hv' : 0 < v := by simpa [V, v] using hv
  have hASU := transientInitialAldousSheppForParent (r := 2) (n := 3)
    (by omega) (by omega) U
  have hASV := transientInitialAldousSheppForParent (r := 2) (n := 3)
    (by omega) (by omega) V
  have hA : 3*u^2 ≤ 2*A := by
    dsimp [u, A]
    nlinarith [hASU]
  have hB : 3*v^2 ≤ 2*B := by
    dsimp [v, B]
    nlinarith [hASV]
  have hk2U := all_transient_initial_laws_direct (s := 2) (by omega) U
  have hk2V := all_transient_initial_laws_direct (s := 2) (by omega) V
  have hC : 4*A^2 ≤ 3*u*C := by
    unfold SSP.K2AllStages.StageBound at hk2U
    dsimp [u, A, C]
    norm_num at hk2U ⊢
    exact hk2U
  have hD : 4*B^2 ≤ 3*v*D := by
    unfold SSP.K2AllStages.StageBound at hk2V
    dsimp [v, B, D]
    norm_num at hk2V ⊢
    exact hk2V
  have hk3U := transientInitialStageBoundK3_two U
  have hk3V := transientInitialStageBoundK3_two V
  have hE : 5*C^2 ≤ 4*A*E := by
    unfold K3StageBound at hk3U
    dsimp [A, C, E]
    norm_num at hk3U ⊢
    exact hk3U
  have hF : 5*D^2 ≤ 4*B*F := by
    unfold K3StageBound at hk3V
    dsimp [B, D, F]
    norm_num at hk3V ⊢
    exact hk3V
  have hr : 0 < r := by dsimp [r, p]; positivity
  have hgap := k3_renewal_step_three r x u A C E v B D F hr
    (by dsimp [x]; exact (transientHoldingMean_pos X).le)
    hu hv' hA hB hC hD hE hF
  have hm2raw := transientMoment2_renewal_of_return_pos X hs hp
  have hm3raw := transientMoment3_renewal_of_return_pos X hs hp
  have hm2 : transientMoment2 3 X =
      geomM2 r (kernelM1 x u) (kernelM2 x u A)
        (kernelM1 x v) (kernelM2 x v B) := by
    rw [hm2raw, renewalM2_eq_geomM2 _ _ _ _ _ _ _ hq.ne'
      (transientReturnProbability_add_terminalProbability X)]
  have hm3 : transientMoment3 3 X =
      geomM3 r (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C)
        (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D) := by
    rw [hm3raw, renewalM3_eq_geomM3 _ _ _ _ _ _ _ _ _ hq.ne'
      (transientReturnProbability_add_terminalProbability X)]
  have hm4raw := transientMoment4_renewal_of_return_pos X hs hp
  have hm4 : transientMoment4 3 X =
      geomM4 r (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C)
        (kernelM4 x u A C E) (kernelM1 x v) (kernelM2 x v B)
        (kernelM3 x v B D) (kernelM4 x v B D F) := by
    simpa only [U, V, u, A, C, E, v, B, D, F, x, p, q, r] using hm4raw
  unfold K3StageBound
  rw [hm2, hm3, hm4]
  unfold stageGap at hgap
  norm_num at hgap ⊢
  linarith

/-- Every deterministic three-state transient law satisfies the `k = 3`
hierarchy inequality, with no representation assumption. -/
theorem transientStageBoundK3_three_unconditional (X : TransientStart 3) :
    K3StageBound 3 (transientMoment2 3 X) (transientMoment3 3 X)
      (transientMoment4 3 X) := by
  by_cases hp0 : transientReturnProbability X = 0
  · exact transientStageBoundK3_three_of_boundary X (Or.inl hp0)
  · have hp : 0 < transientReturnProbability X :=
      lt_of_le_of_ne (transientReturnProbability_nonneg X) (Ne.symm hp0)
    let V := transientTerminalConditionedInitial X (by omega)
      (transientTerminalProbability_pos X)
    by_cases hv0 : transientInitialMoment1 2 V = 0
    · apply transientStageBoundK3_three_of_boundary X (Or.inr ?_)
      simpa [V] using hv0
    · have hv : 0 < transientInitialMoment1 2 V :=
        lt_of_le_of_ne (transientInitialMoment1_nonneg V) (Ne.symm hv0)
      apply transientStageBoundK3_three_of_positive_return X hp
      simpa [V] using hv

/-- The unconditional theorem for an arbitrary three-state subprobability
initial vector. -/
theorem transientInitialStageBoundK3_three_unconditional
    (X : TransientInitial 3) :
    K3StageBound 3 (transientInitialMoment2 3 X)
      (transientInitialMoment3 3 X) (transientInitialMoment4 3 X) := by
  have hmix := SSP.Chain.mixture_closure_sq (Finset.univ : Finset (Fin 3)) X.weight
    (fun i => transientMoment2 3 (X.component i))
    (fun i => transientMoment3 3 (X.component i))
    (fun i => transientMoment4 3 (X.component i)) (6/5 : ℝ)
    (by norm_num) (fun i _ => X.weight_nonneg i)
    (fun i _ => transientMoment2_nonneg (X.component i))
    (fun i _ => transientMoment4_nonneg (X.component i))
    (fun i _ => transientMoment3_nonneg (X.component i))
    (fun i _ => by
      have h := transientStageBoundK3_three_unconditional (X.component i)
      unfold K3StageBound at h
      norm_num at h ⊢
      nlinarith)
  unfold K3StageBound transientInitialMoment2 transientInitialMoment3
    transientInitialMoment4
  norm_num at hmix ⊢
  nlinarith

end SSP.K2Concrete
