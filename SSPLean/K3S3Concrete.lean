import SSPLean.K3S3Renewal
import SSPLean.K3S3VZero

/-!
# Concrete boundary of the three-state `k = 3` theorem

This file connects the scalar no-return certificate in `K3S3Renewal` to the
state-return decomposition of an arbitrary three-state transient model.
-/

namespace SSP.K2Concrete

open SSP.K3S4Renewal SSP.K3S3

/-- Fourth unnormalised renewal moment, extending the `renewalX1`--`renewalX3`
coordinates used by the shorter `k = 2` proof.  If `M₄` is the fourth
moment of the renewal law, this is `q⁴ M₄`. -/
noncomputable def renewalX4
    (p q a1 a2 a3 a4 b1 b2 b3 b4 : ℝ) : ℝ :=
  q^4*b4 + p*q^3*a4
    + 4*p*q^2*a3*SSP.K2AllStages.renewalX1 0 a1 b1 p q
    + 6*p*q*a2*SSP.K2AllStages.renewalX2 0 a1 b1 p q a2 b2
    + 4*p*a1*SSP.K2AllStages.renewalX3 0 a1 b1 p q a2 b2 a3 b3

/-- The order-three target in denominator-free renewal coordinates. -/
noncomputable def renewalGap3Scaled
    (p q a1 a2 a3 a4 b1 b2 b3 b4 : ℝ) : ℝ :=
  5 * SSP.K2AllStages.renewalX2 0 a1 b1 p q a2 b2 *
      renewalX4 p q a1 a2 a3 a4 b1 b2 b3 b4
    - 6 * (SSP.K2AllStages.renewalX3 0 a1 b1 p q a2 b2 a3 b3)^2

set_option maxRecDepth 100000 in
/-- Clearing the geometric denominator turns the `k = 3`, `s = 3` gap into
the polynomial `renewalGap3Scaled`. -/
theorem renewalGap3Scaled_eq_geomGap
    (p q a1 a2 a3 a4 b1 b2 b3 b4 : ℝ) (hq : q ≠ 0) :
    renewalGap3Scaled p q a1 a2 a3 a4 b1 b2 b3 b4 =
      q^6 * (5 * geomM2 (p/q) a1 a2 b1 b2 *
        geomM4 (p/q) a1 a2 a3 a4 b1 b2 b3 b4
        - 6 * (geomM3 (p/q) a1 a2 a3 b1 b2 b3)^2) := by
  unfold renewalGap3Scaled
    renewalX4
    SSP.K2AllStages.renewalX1 SSP.K2AllStages.renewalX2
    SSP.K2AllStages.renewalX3 SSP.K2AllStages.kernelM1
    SSP.K2AllStages.kernelM2 SSP.K2AllStages.kernelM3
    geomM4 geomM3 geomM2 geomM1
  field_simp [hq]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- Scale-free form of the order-three direct-terminal certificate. -/
theorem stageGap_three_directTerminal_nonneg
    (r x u A C E : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x) (hu : 0 < u)
    (hA : 3 * u ^ 2 ≤ 2 * A) (hC : 4 * A ^ 2 ≤ 3 * u * C)
    (hE : 5 * C ^ 2 ≤ 4 * A * E) :
    0 ≤ 5 * geomM2 r (kernelM1 x u) (kernelM2 x u A)
        (kernelM1 x 0) (kernelM2 x 0 0) *
      geomM4 r (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C)
        (kernelM4 x u A C E) (kernelM1 x 0) (kernelM2 x 0 0)
        (kernelM3 x 0 0 0) (kernelM4 x 0 0 0 0)
      - 6 * (geomM3 r (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C)
        (kernelM1 x 0) (kernelM2 x 0 0) (kernelM3 x 0 0 0)) ^ 2 := by
  let y := x / u
  let b := 3 * u^2 / (2 * A)
  let d := 4 * A^2 / (3 * u * C)
  let f := 5 * C^2 / (4 * A * E)
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hCp : 0 < C := by nlinarith [sq_pos_of_pos hAp]
  have hEp : 0 < E := by nlinarith [sq_pos_of_pos hCp]
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have hd1 : d ≤ 1 := by
    dsimp [d]
    rw [div_le_one (by positivity)]
    exact hC
  have hf1 : f ≤ 1 := by
    dsimp [f]
    rw [div_le_one (by positivity)]
    exact hE
  have hpoly := vzero_branch_nonneg r y b d f hr hy hb hd hd1 hf hf1
  dsimp [y, b, d, f] at hpoly
  unfold geomM4 geomM3 geomM2 geomM1 kernelM1 kernelM2 kernelM3 kernelM4
  field_simp [hu.ne', hAp.ne', hCp.ne', hEp.ne'] at hpoly ⊢
  nlinarith [hpoly]

theorem renewalM2_eq_geomM2 (x u v p q A B : ℝ) (hq : q ≠ 0)
    (_hpq : p + q = 1) :
    SSP.K2AllStages.renewalM2 x u v p q A B =
      geomM2 (p / q) (kernelM1 x u) (kernelM2 x u A)
        (kernelM1 x v) (kernelM2 x v B) := by
  unfold SSP.K2AllStages.renewalM2 SSP.K2AllStages.renewalX2
    SSP.K2AllStages.kernelM1 SSP.K2AllStages.kernelM2
    geomM2 geomM1 kernelM1 kernelM2
  field_simp [hq]
  nlinarith

theorem renewalM3_eq_geomM3 (x u v p q A B C D : ℝ) (hq : q ≠ 0)
    (_hpq : p + q = 1) :
    SSP.K2AllStages.renewalM3 x u v p q A B C D =
      geomM3 (p / q) (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C)
        (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D) := by
  unfold SSP.K2AllStages.renewalM3 SSP.K2AllStages.renewalX3
    SSP.K2AllStages.kernelM1 SSP.K2AllStages.kernelM2 SSP.K2AllStages.kernelM3
    geomM3 geomM2 geomM1 kernelM1 kernelM2 kernelM3
  field_simp [hq]
  nlinarith

/-- The other concrete boundary: return is possible, but the terminal excursion is
the atom at zero. -/
theorem transientStageBoundK3_three_of_terminalMoment1_eq_zero
    (X : TransientStart 3) (hp : 0 < transientReturnProbability X)
    (hv0 : transientInitialMoment1 2
      (transientTerminalConditionedInitial X (by omega)
        (transientTerminalProbability_pos X)) = 0) :
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
  let x := transientHoldingMean X
  let p := transientReturnProbability X
  let q := transientTerminalProbability X
  let r := p / q
  have hx : 0 < x := transientHoldingMean_pos X
  have hq : 0 < q := transientTerminalProbability_pos X
  have hu : 0 < u := by
    apply transientInitialMoment1_pos_of_weight_sum_pos
    dsimp [U]
    rw [transientReturnConditionedInitial_weight_sum X hs hp]
    norm_num
  have hVzero : transientInitialMoment1 2 V = 0 := by simpa [V] using hv0
  have hv234 := transientInitial_higher_moments_eq_zero_of_moment1_eq_zero V hVzero
  have hv4 : transientInitialMoment4 2 V = 0 := by
    unfold transientInitialMoment4
    have hw := transientInitial_weights_eq_zero_of_moment1_eq_zero V hVzero
    apply Finset.sum_eq_zero
    intro i hi
    rw [hw i]
    simp
  have hAS0 := transientInitialAldousSheppForParent (r := 2) (n := 3)
    (by omega) (by omega) U
  have hAS : 3 * u^2 ≤ 2 * A := by dsimp [u, A]; nlinarith [hAS0]
  have hk2stage := all_transient_initial_laws_direct (s := 2) (by omega) U
  have hk2 : 4 * A^2 ≤ 3 * u * C := by
    unfold SSP.K2AllStages.StageBound at hk2stage
    dsimp [u, A, C]
    norm_num at hk2stage ⊢
    exact hk2stage
  have hk3stage := transientInitialStageBoundK3_two U
  have hk3 : 5 * C^2 ≤ 4 * A * E := by
    unfold K3StageBound at hk3stage
    dsimp [A, C, E]
    norm_num at hk3stage ⊢
    exact hk3stage
  have hr : 0 ≤ r := by dsimp [r, p, q]; positivity
  have hgap := stageGap_three_directTerminal_nonneg r x u A C E hr hx.le hu hAS hk2 hk3
  have hm2raw := transientMoment2_renewal_of_return_pos X hs hp
  have hm3raw := transientMoment3_renewal_of_return_pos X hs hp
  have hm2 : transientMoment2 3 X =
      geomM2 r (kernelM1 x u) (kernelM2 x u A) (kernelM1 x 0) (kernelM2 x 0 0) := by
    rw [hm2raw, renewalM2_eq_geomM2 _ _ _ _ _ _ _ hq.ne'
      (transientReturnProbability_add_terminalProbability X)]
    simp only [U, V, u, A, x, p, q, r, hVzero, hv234.1]
  have hm3 : transientMoment3 3 X =
      geomM3 r (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C)
        (kernelM1 x 0) (kernelM2 x 0 0) (kernelM3 x 0 0 0) := by
    rw [hm3raw, renewalM3_eq_geomM3 _ _ _ _ _ _ _ _ _ hq.ne'
      (transientReturnProbability_add_terminalProbability X)]
    simp only [U, V, u, A, C, x, p, q, r, hVzero, hv234.1, hv234.2]
  have hm4raw := transientMoment4_renewal_of_return_pos X hs hp
  have hm4 : transientMoment4 3 X =
      geomM4 r (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C)
        (kernelM4 x u A C E) (kernelM1 x 0) (kernelM2 x 0 0)
        (kernelM3 x 0 0 0) (kernelM4 x 0 0 0 0) := by
    simpa only [U, V, u, A, C, E, x, p, q, r, hVzero, hv234.1,
      hv234.2, hv4] using hm4raw
  unfold K3StageBound
  rw [hm2, hm3, hm4]
  norm_num at hgap ⊢
  linarith

/-- If the distinguished state cannot be revisited, the three-state `k = 3`
bound follows unconditionally from the two-state hierarchy for the terminal
excursion. -/
theorem transientStageBoundK3_three_of_returnProbability_eq_zero
    (X : TransientStart 3) (hp0 : transientReturnProbability X = 0) :
    K3StageBound 3 (transientMoment2 3 X) (transientMoment3 3 X)
      (transientMoment4 3 X) := by
  have hs : 2 ≤ (3 : ℕ) := by omega
  let V := transientTerminalConditionedInitial X hs
    (transientTerminalProbability_pos X)
  let v := transientInitialMoment1 2 V
  let B := transientInitialMoment2 2 V
  let D := transientInitialMoment3 2 V
  let F := transientInitialMoment4 2 V
  let x := transientHoldingMean X
  have hx : 0 < x := transientHoldingMean_pos X
  have hvnn : 0 ≤ v := transientInitialMoment1_nonneg V
  have hq1 : transientTerminalProbability X = 1 := by
    linarith [transientReturnProbability_add_terminalProbability X]
  have hm123 := transient_renewal_moments_of_return_zero X hs hp0
    (pureTransientInitial (transientReturnConditionedStart X ⟨0, by omega⟩))
  have hm2 : transientMoment2 3 X = kernelM2 x v B := by
    have h := hm123.2.1
    rw [hp0, hq1] at h
    simpa [v, B, V, x, SSP.K2AllStages.renewalM2,
      SSP.K2AllStages.renewalX1, SSP.K2AllStages.renewalX2,
      SSP.K2AllStages.kernelM1, SSP.K2AllStages.kernelM2,
      kernelM2] using h
  have hm3 : transientMoment3 3 X = kernelM3 x v B D := by
    have h := hm123.2.2
    rw [hp0, hq1] at h
    simpa [v, B, D, V, x, SSP.K2AllStages.renewalM3,
      SSP.K2AllStages.renewalX1, SSP.K2AllStages.renewalX2,
      SSP.K2AllStages.renewalX3, SSP.K2AllStages.kernelM1,
      SSP.K2AllStages.kernelM2, SSP.K2AllStages.kernelM3,
      kernelM3] using h
  have hm4 : transientMoment4 3 X = kernelM4 x v B D F := by
    simpa [V, v, B, D, F, x] using
      (transientMoment4_of_return_zero X hs hp0)
  rcases eq_or_lt_of_le hvnn with hv0 | hv
  · have hv0' : v = 0 := hv0.symm
    have hv234 := transientInitial_higher_moments_eq_zero_of_moment1_eq_zero V hv0'
    have hF0 : F = 0 := by
      unfold F transientInitialMoment4
      have hw := transientInitial_weights_eq_zero_of_moment1_eq_zero V hv0.symm
      apply Finset.sum_eq_zero
      intro i hi
      rw [hw i]
      simp
    unfold K3StageBound
    rw [hm2, hm3, hm4]
    simp only [v, B, D, F, hv0', hv234.1, hv234.2, hF0]
    unfold kernelM2 kernelM3 kernelM4
    norm_num
    nlinarith [sq_nonneg (x ^ 3)]
  · have hAS := transientInitialAldousSheppForParent (r := 2) (n := 3)
      (by omega) (by omega) V
    have hAS' : 3 * v ^ 2 ≤ 2 * B := by
      dsimp [v, B]
      nlinarith [hAS]
    have hk2stage := all_transient_initial_laws_direct (s := 2) (by omega) V
    have hk2 : 4 * B ^ 2 ≤ 3 * v * D := by
      unfold SSP.K2AllStages.StageBound at hk2stage
      dsimp [v, B, D]
      norm_num at hk2stage ⊢
      exact hk2stage
    have hk3stage := transientInitialStageBoundK3_two V
    have hk3 : 5 * D ^ 2 ≤ 4 * B * F := by
      unfold K3StageBound at hk3stage
      dsimp [B, D, F]
      norm_num at hk3stage ⊢
      exact hk3stage
    have hgap := gap3_noReturn_nonneg x v B D F hx hv hAS' hk2 hk3
    unfold K3StageBound
    rw [hm2, hm3, hm4]
    unfold gap3 at hgap
    norm_num at hgap ⊢
    linarith

/-- All nongenuinely-cyclic branches of the three-state base case. -/
theorem transientStageBoundK3_three_of_boundary
    (X : TransientStart 3)
    (hboundary : transientReturnProbability X = 0 ∨
      transientInitialMoment1 2
        (transientTerminalConditionedInitial X (by omega)
          (transientTerminalProbability_pos X)) = 0) :
    K3StageBound 3 (transientMoment2 3 X) (transientMoment3 3 X)
      (transientMoment4 3 X) := by
  rcases hboundary with hp0 | hv0
  · exact transientStageBoundK3_three_of_returnProbability_eq_zero X hp0
  · by_cases hp : 0 < transientReturnProbability X
    · exact transientStageBoundK3_three_of_terminalMoment1_eq_zero X hp hv0
    · have hp0 : transientReturnProbability X = 0 :=
        le_antisymm (not_lt.mp hp) (transientReturnProbability_nonneg X)
      exact transientStageBoundK3_three_of_returnProbability_eq_zero X hp0

end SSP.K2Concrete
