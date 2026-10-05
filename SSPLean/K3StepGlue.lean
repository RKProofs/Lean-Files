import SSPLean.K3Step
import SSPLean.K3S3Concrete

/-!
# From the scalar `k = 3` renewal step to concrete transient models

`SSP.K2Concrete.k3_renewal_step` is the scalar induction step: it bounds `stageGap n r`
given Aldous--Shepp, the `k = 2` bound, and the `k = 3` bound on both excursions.  This file
packages the probabilistic side — a `k = 3` state-return certificate carrying the *fourth*
moment decomposition (which `TransientStateReturnData` does not) — and discharges
`SSP.K2Concrete.K3Inputs.step`.

The moment identities come from `SSPLean.K3FourthRenewal`
(`transientMoment4_renewal_of_return_pos` and friends); the `k = 2` and Aldous--Shepp inputs
are unconditional (`k2_bound_for_parent`, `transientInitialAldousSheppForParent`).
-/

open Finset

namespace SSP.K2Concrete

open SSP.K3S4Renewal SSP.K3AllStages

private theorem k3StageBound_mono_local {s N : ℕ} {m₂ m₃ m₄ : ℝ}
    (hsN : s ≤ N) (hm₂ : 0 ≤ m₂) (hm₄ : 0 ≤ m₄)
    (h : K3StageBound s m₂ m₃ m₄) : K3StageBound N m₂ m₃ m₄ := by
  unfold K3StageBound at h ⊢
  have hcast : (s : ℝ) ≤ (N : ℝ) := by exact_mod_cast hsN
  have hm24 : 0 ≤ m₂ * m₄ := mul_nonneg hm₂ hm₄
  nlinarith [h, hm24, hcast]

private theorem transientInitialMoment4_eq_zero_of_moment1_eq_zero {s : ℕ}
    (X : TransientInitial s) (h : transientInitialMoment1 s X = 0) :
    transientInitialMoment4 s X = 0 := by
  unfold transientInitialMoment4
  have hw := transientInitial_weights_eq_zero_of_moment1_eq_zero X h
  apply Finset.sum_eq_zero
  intro i hi
  rw [hw i]
  simp

/-- A polynomial inequality valid for every positive perturbation remains valid when the
perturbation is set to zero.  This is the only topological input needed for the two degenerate
renewal branches below. -/
private theorem nonneg_at_zero_of_continuous (f : ℝ → ℝ) (hf : Continuous f)
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ f t) : 0 ≤ f 0 := by
  refine ge_of_tendsto (x := nhdsWithin 0 (Set.Ioi 0))
    (hf.continuousAt.mono_left inf_le_left) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hpos t ht

/-- The scalar renewal step when return has vanished.  We obtain it from the positive-return
step by inserting a fixed sharp moment tuple for the irrelevant return excursion and sending
the geometric-return mean to zero. -/
theorem k3_renewal_step_return_zero
    (n x v B D F : ℝ) (hn : 4 ≤ n) (hx : 0 ≤ x) (hv : 0 < v)
    (hB : n * v ^ 2 ≤ (n - 1) * B)
    (hD : (n + 1) * B ^ 2 ≤ n * v * D)
    (hF : (n + 2) * D ^ 2 ≤ (n + 1) * B * F) :
    0 ≤ stageGap n 0
      (kernelM1 x 1) (kernelM2 x 1 n) (kernelM3 x 1 n (n * (n + 1)))
        (kernelM4 x 1 n (n * (n + 1)) (n * (n + 1) * (n + 2)))
      (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D) (kernelM4 x v B D F) := by
  let f : ℝ → ℝ := fun t => stageGap n t
    (kernelM1 x 1) (kernelM2 x 1 n) (kernelM3 x 1 n (n * (n + 1)))
      (kernelM4 x 1 n (n * (n + 1)) (n * (n + 1) * (n + 2)))
    (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D) (kernelM4 x v B D F)
  have hf : Continuous f := by
    dsimp [f]
    unfold stageGap geomM4 geomM3 geomM2 geomM1 kernelM1 kernelM2 kernelM3 kernelM4
    fun_prop
  have hpos : ∀ t : ℝ, 0 < t → 0 ≤ f t := by
    intro t ht
    dsimp [f]
    apply k3_renewal_step n t x 1 n (n * (n + 1)) (n * (n + 1) * (n + 2))
      v B D F hn ht hx (by norm_num) hv
    · nlinarith
    · exact hB
    · nlinarith
    · exact hD
    · nlinarith
    · exact hF
  exact nonneg_at_zero_of_continuous f hf hpos

/-- The scalar renewal step when the terminal excursion is the atom at zero.  Here the
positive-step theorem is applied to the sharp tuple
`(t, n t², n(n+1)t³, n(n+1)(n+2)t⁴)` and then `t → 0`. -/
theorem k3_renewal_step_terminal_zero
    (n r x u A C E : ℝ) (hn : 4 ≤ n) (hr : 0 < r) (hx : 0 ≤ x) (hu : 0 < u)
    (hA : n * u ^ 2 ≤ (n - 1) * A)
    (hC : (n + 1) * A ^ 2 ≤ n * u * C)
    (hE : (n + 2) * C ^ 2 ≤ (n + 1) * A * E) :
    0 ≤ stageGap n r
      (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C) (kernelM4 x u A C E)
      (kernelM1 x 0) (kernelM2 x 0 0) (kernelM3 x 0 0 0) (kernelM4 x 0 0 0 0) := by
  let f : ℝ → ℝ := fun t => stageGap n r
    (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C) (kernelM4 x u A C E)
    (kernelM1 x t) (kernelM2 x t (n * t ^ 2))
      (kernelM3 x t (n * t ^ 2) (n * (n + 1) * t ^ 3))
      (kernelM4 x t (n * t ^ 2) (n * (n + 1) * t ^ 3)
        (n * (n + 1) * (n + 2) * t ^ 4))
  have hf : Continuous f := by
    dsimp [f]
    unfold stageGap geomM4 geomM3 geomM2 geomM1 kernelM1 kernelM2 kernelM3 kernelM4
    fun_prop
  have hpos : ∀ t : ℝ, 0 < t → 0 ≤ f t := by
    intro t ht
    dsimp [f]
    apply k3_renewal_step n r x u A C E t (n * t ^ 2)
      (n * (n + 1) * t ^ 3) (n * (n + 1) * (n + 2) * t ^ 4)
      hn hr hx hu ht hA
    · have hn0 : 0 ≤ n := by linarith
      have hn2 : 0 ≤ n - 2 := by linarith
      nlinarith [mul_nonneg (mul_nonneg hn0 hn2) (sq_nonneg t)]
    · exact hC
    · ring_nf
      nlinarith [sq_nonneg (t ^ 2)]
    · exact hE
    · ring_nf
      nlinarith [sq_nonneg (t ^ 3)]
  simpa [f] using nonneg_at_zero_of_continuous f hf hpos

/-- A `k = 3` state-return certificate: the data of `TransientStateReturnData` together with
the fourth-moment decomposition, in the `geomM` form the `k = 3` development uses. -/
structure K3ReturnData (n : ℕ) (X : TransientStart n) where
  su : ℕ
  sv : ℕ
  su_pos : 1 ≤ su
  sv_pos : 1 ≤ sv
  su_lt : su < n
  sv_lt : sv < n
  U : TransientInitial su
  V : TransientInitial sv
  x : ℝ
  r : ℝ
  x_nonneg : 0 ≤ x
  r_pos : 0 < r
  u_pos : 0 < transientInitialMoment1 su U
  v_pos : 0 < transientInitialMoment1 sv V
  moment2_decomp : transientMoment2 n X =
    geomM2 r (kernelM1 x (transientInitialMoment1 su U))
      (kernelM2 x (transientInitialMoment1 su U) (transientInitialMoment2 su U))
      (kernelM1 x (transientInitialMoment1 sv V))
      (kernelM2 x (transientInitialMoment1 sv V) (transientInitialMoment2 sv V))
  moment3_decomp : transientMoment3 n X =
    geomM3 r (kernelM1 x (transientInitialMoment1 su U))
      (kernelM2 x (transientInitialMoment1 su U) (transientInitialMoment2 su U))
      (kernelM3 x (transientInitialMoment1 su U) (transientInitialMoment2 su U)
        (transientInitialMoment3 su U))
      (kernelM1 x (transientInitialMoment1 sv V))
      (kernelM2 x (transientInitialMoment1 sv V) (transientInitialMoment2 sv V))
      (kernelM3 x (transientInitialMoment1 sv V) (transientInitialMoment2 sv V)
        (transientInitialMoment3 sv V))
  moment4_decomp : transientMoment4 n X =
    geomM4 r (kernelM1 x (transientInitialMoment1 su U))
      (kernelM2 x (transientInitialMoment1 su U) (transientInitialMoment2 su U))
      (kernelM3 x (transientInitialMoment1 su U) (transientInitialMoment2 su U)
        (transientInitialMoment3 su U))
      (kernelM4 x (transientInitialMoment1 su U) (transientInitialMoment2 su U)
        (transientInitialMoment3 su U) (transientInitialMoment4 su U))
      (kernelM1 x (transientInitialMoment1 sv V))
      (kernelM2 x (transientInitialMoment1 sv V) (transientInitialMoment2 sv V))
      (kernelM3 x (transientInitialMoment1 sv V) (transientInitialMoment2 sv V)
        (transientInitialMoment3 sv V))
      (kernelM4 x (transientInitialMoment1 sv V) (transientInitialMoment2 sv V)
        (transientInitialMoment3 sv V) (transientInitialMoment4 sv V))

/-- The concrete state-return certificate in the genuinely cyclic, nondegenerate branch.
The two conditioned excursions both live on the `n - 1` states other than the distinguished
state. -/
noncomputable def generalK3ReturnDataOfPos {n : ℕ} (hn : 2 ≤ n)
    (X : TransientStart n) (hp : 0 < transientReturnProbability X)
    (hv : 0 < transientInitialMoment1 (n - 1)
      (transientTerminalConditionedInitial X hn (transientTerminalProbability_pos X))) :
    K3ReturnData n X := by
  let U := transientReturnConditionedInitial X hn hp
  let V := transientTerminalConditionedInitial X hn (transientTerminalProbability_pos X)
  let p := transientReturnProbability X
  let q := transientTerminalProbability X
  have hq : 0 < q := transientTerminalProbability_pos X
  have hu : 0 < transientInitialMoment1 (n - 1) U := by
    apply transientInitialMoment1_pos_of_weight_sum_pos
    dsimp [U]
    rw [transientReturnConditionedInitial_weight_sum X hn hp]
    norm_num
  refine
    { su := n - 1
      sv := n - 1
      su_pos := by omega
      sv_pos := by omega
      su_lt := by omega
      sv_lt := by omega
      U := U
      V := V
      x := transientHoldingMean X
      r := p / q
      x_nonneg := (transientHoldingMean_pos X).le
      r_pos := div_pos hp hq
      u_pos := hu
      v_pos := by simpa [V] using hv
      moment2_decomp := ?_
      moment3_decomp := ?_
      moment4_decomp := ?_ }
  · rw [transientMoment2_renewal_of_return_pos X hn hp,
      renewalM2_eq_geomM2 _ _ _ _ _ _ _ hq.ne'
        (transientReturnProbability_add_terminalProbability X)]
  · rw [transientMoment3_renewal_of_return_pos X hn hp,
      renewalM3_eq_geomM3 _ _ _ _ _ _ _ _ _ hq.ne'
        (transientReturnProbability_add_terminalProbability X)]
  · simpa [U, V, p, q] using transientMoment4_renewal_of_return_pos X hn hp

/-- **The `k = 3` step from a return certificate.**  Given the certificate and the `k = 3`
bound on both excursions at the parent order, the parent satisfies the `k = 3` bound.

The Aldous--Shepp and `k = 2` inputs are supplied internally — both are unconditional in
this repository — so the only hypothesis is the inductive one. -/
theorem k3StageBound_of_returnData {n : ℕ} (hn : 4 ≤ n) {X : TransientStart n}
    (c : K3ReturnData n X)
    (hU : K3StageBound (n - 1) (transientInitialMoment2 c.su c.U)
      (transientInitialMoment3 c.su c.U) (transientInitialMoment4 c.su c.U))
    (hV : K3StageBound (n - 1) (transientInitialMoment2 c.sv c.V)
      (transientInitialMoment3 c.sv c.V) (transientInitialMoment4 c.sv c.V)) :
    K3StageBound n (transientMoment2 n X) (transientMoment3 n X) (transientMoment4 n X) := by
  have hnR : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hncast : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  -- Aldous--Shepp at the parent order
  have hAS_U := transientInitialAldousSheppForParent c.su_pos c.su_lt c.U
  have hAS_V := transientInitialAldousSheppForParent c.sv_pos c.sv_lt c.V
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hA : (n:ℝ) * (transientInitialMoment1 c.su c.U)^2
      ≤ ((n:ℝ) - 1) * transientInitialMoment2 c.su c.U := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn1] at hAS_U; linarith
  have hB : (n:ℝ) * (transientInitialMoment1 c.sv c.V)^2
      ≤ ((n:ℝ) - 1) * transientInitialMoment2 c.sv c.V := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn1] at hAS_V; linarith
  -- the k = 2 bound at the parent order
  have hC := k2_bound_for_parent c.su_pos c.su_lt c.U
  have hD := k2_bound_for_parent c.sv_pos c.sv_lt c.V
  -- the inductive k = 3 bounds, recast at the parent order
  have hE : ((n:ℝ) + 2) * (transientInitialMoment3 c.su c.U)^2
      ≤ ((n:ℝ) + 1) * transientInitialMoment2 c.su c.U * transientInitialMoment4 c.su c.U := by
    unfold K3StageBound at hU; rw [hncast] at hU
    have h4 := transientInitialMoment4_nonneg c.U
    have h2 := transientInitialMoment2_nonneg c.U
    nlinarith [hU, mul_nonneg h2 h4]
  have hF : ((n:ℝ) + 2) * (transientInitialMoment3 c.sv c.V)^2
      ≤ ((n:ℝ) + 1) * transientInitialMoment2 c.sv c.V * transientInitialMoment4 c.sv c.V := by
    unfold K3StageBound at hV; rw [hncast] at hV
    have h4 := transientInitialMoment4_nonneg c.V
    have h2 := transientInitialMoment2_nonneg c.V
    nlinarith [hV, mul_nonneg h2 h4]
  -- apply the scalar step
  have hstep := k3_renewal_step (n:ℝ) c.r c.x
    (transientInitialMoment1 c.su c.U) (transientInitialMoment2 c.su c.U)
    (transientInitialMoment3 c.su c.U) (transientInitialMoment4 c.su c.U)
    (transientInitialMoment1 c.sv c.V) (transientInitialMoment2 c.sv c.V)
    (transientInitialMoment3 c.sv c.V) (transientInitialMoment4 c.sv c.V)
    hnR c.r_pos c.x_nonneg c.u_pos c.v_pos hA hB hC hD hE hF
  unfold K3StageBound
  rw [c.moment2_decomp, c.moment3_decomp, c.moment4_decomp]
  unfold stageGap at hstep
  linarith [hstep]

/-- The `k = 3` step from a return certificate, with the inductive hypothesis supplied at
each excursion's own order (the form a strong induction provides).  This is the shape that
`all_transient_starts_k3_of_inputs` consumes once the certificates are constructed. -/
theorem k3StageBound_step_of_returnData {n : ℕ} (hn : 4 ≤ n) {X : TransientStart n}
    (c : K3ReturnData n X)
    (hind : ∀ m : ℕ, m < n → 1 ≤ m → ∀ Y : TransientInitial m,
      K3StageBound m (transientInitialMoment2 m Y)
        (transientInitialMoment3 m Y) (transientInitialMoment4 m Y)) :
    K3StageBound n (transientMoment2 n X) (transientMoment3 n X)
      (transientMoment4 n X) := by
  refine k3StageBound_of_returnData hn c ?_ ?_
  · exact k3StageBound_mono_local (Nat.le_sub_one_of_lt c.su_lt)
      (transientInitialMoment2_nonneg c.U) (transientInitialMoment4_nonneg c.U)
      (hind c.su c.su_lt c.su_pos c.U)
  · exact k3StageBound_mono_local (Nat.le_sub_one_of_lt c.sv_lt)
      (transientInitialMoment2_nonneg c.V) (transientInitialMoment4_nonneg c.V)
      (hind c.sv c.sv_lt c.sv_pos c.V)

/-- The concrete induction step in the genuinely cyclic, nondegenerate branch. -/
theorem k3StageBound_step_of_positive_return {n : ℕ} (hn : 4 ≤ n)
    (X : TransientStart n) (hp : 0 < transientReturnProbability X)
    (hv : 0 < transientInitialMoment1 (n - 1)
      (transientTerminalConditionedInitial X (by omega)
        (transientTerminalProbability_pos X)))
    (hind : ∀ m : ℕ, m < n → 1 ≤ m → ∀ Y : TransientInitial m,
      K3StageBound m (transientInitialMoment2 m Y)
        (transientInitialMoment3 m Y) (transientInitialMoment4 m Y)) :
    K3StageBound n (transientMoment2 n X) (transientMoment3 n X)
      (transientMoment4 n X) := by
  let c := generalK3ReturnDataOfPos (n := n) (by omega) X hp hv
  exact k3StageBound_step_of_returnData hn c hind

/-- The concrete no-return boundary of the general induction step. -/
theorem k3StageBound_step_of_returnProbability_eq_zero {n : ℕ} (hn : 4 ≤ n)
    (X : TransientStart n) (hp0 : transientReturnProbability X = 0)
    (hV : K3StageBound (n - 1)
      (transientInitialMoment2 (n - 1)
        (transientTerminalConditionedInitial X (by omega) (transientTerminalProbability_pos X)))
      (transientInitialMoment3 (n - 1)
        (transientTerminalConditionedInitial X (by omega) (transientTerminalProbability_pos X)))
      (transientInitialMoment4 (n - 1)
        (transientTerminalConditionedInitial X (by omega) (transientTerminalProbability_pos X)))) :
    K3StageBound n (transientMoment2 n X) (transientMoment3 n X)
      (transientMoment4 n X) := by
  have hs : 2 ≤ n := by omega
  let V := transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X)
  let v := transientInitialMoment1 (n - 1) V
  let B := transientInitialMoment2 (n - 1) V
  let D := transientInitialMoment3 (n - 1) V
  let F := transientInitialMoment4 (n - 1) V
  let x := transientHoldingMean X
  have hx : 0 ≤ x := by dsimp [x]; exact (transientHoldingMean_pos X).le
  have hq1 : transientTerminalProbability X = 1 := by
    linarith [transientReturnProbability_add_terminalProbability X]
  have hm123 := transient_renewal_moments_of_return_zero X hs hp0
    (pureTransientInitial (transientReturnConditionedStart X ⟨0, by omega⟩))
  have hm2 : transientMoment2 n X = kernelM2 x v B := by
    have h := hm123.2.1
    rw [hp0, hq1] at h
    simpa [v, B, V, x, SSP.K2AllStages.renewalM2,
      SSP.K2AllStages.renewalX1, SSP.K2AllStages.renewalX2,
      SSP.K2AllStages.kernelM1, SSP.K2AllStages.kernelM2, kernelM2] using h
  have hm3 : transientMoment3 n X = kernelM3 x v B D := by
    have h := hm123.2.2
    rw [hp0, hq1] at h
    simpa [v, B, D, V, x, SSP.K2AllStages.renewalM3,
      SSP.K2AllStages.renewalX1, SSP.K2AllStages.renewalX2,
      SSP.K2AllStages.renewalX3, SSP.K2AllStages.kernelM1,
      SSP.K2AllStages.kernelM2, SSP.K2AllStages.kernelM3, kernelM3] using h
  have hm4 : transientMoment4 n X = kernelM4 x v B D F := by
    simpa [V, v, B, D, F, x] using transientMoment4_of_return_zero X hs hp0
  rcases eq_or_lt_of_le (transientInitialMoment1_nonneg V) with hv0 | hv
  · have hv0' : v = 0 := by simpa [v] using hv0.symm
    have hv23 := transientInitial_higher_moments_eq_zero_of_moment1_eq_zero V hv0.symm
    have hF0 : F = 0 := by
      dsimp [F]
      exact transientInitialMoment4_eq_zero_of_moment1_eq_zero V hv0.symm
    unfold K3StageBound
    rw [hm2, hm3, hm4]
    simp only [v, B, D, F, hv0', hv23.1, hv23.2, hF0]
    unfold kernelM2 kernelM3 kernelM4
    norm_num
    have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [sq_nonneg (x ^ 3)]
  · have hv' : 0 < v := by simpa [v] using hv
    have hB0 := transientInitialAldousSheppForParent (r := n - 1) (n := n)
      (by omega) (by omega) V
    have hB : (n : ℝ) * v ^ 2 ≤ ((n : ℝ) - 1) * B := by
      dsimp [v, B]
      have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ hn1] at hB0
      nlinarith
    have hD : ((n : ℝ) + 1) * B ^ 2 ≤ (n : ℝ) * v * D := by
      simpa [v, B, D] using k2_bound_for_parent (n := n) (r := n - 1)
        (by omega) (by omega) V
    have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    have hF : ((n : ℝ) + 2) * D ^ 2 ≤ ((n : ℝ) + 1) * B * F := by
      unfold K3StageBound at hV
      rw [hncast] at hV
      dsimp [V, B, D, F] at hV ⊢
      ring_nf at hV ⊢
      exact hV
    have hgap := k3_renewal_step_return_zero (n : ℝ) x v B D F
      (by exact_mod_cast hn) hx hv' hB hD hF
    unfold K3StageBound
    rw [hm2, hm3, hm4]
    unfold stageGap geomM4 geomM3 geomM2 geomM1 at hgap
    norm_num at hgap ⊢
    exact hgap

/-- The concrete positive-return boundary in which the conditioned terminal excursion has
zero first moment. -/
theorem k3StageBound_step_of_terminalMoment1_eq_zero {n : ℕ} (hn : 4 ≤ n)
    (X : TransientStart n) (hp : 0 < transientReturnProbability X)
    (hv0 : transientInitialMoment1 (n - 1)
      (transientTerminalConditionedInitial X (by omega)
        (transientTerminalProbability_pos X)) = 0)
    (hU : K3StageBound (n - 1)
      (transientInitialMoment2 (n - 1)
        (transientReturnConditionedInitial X (by omega) hp))
      (transientInitialMoment3 (n - 1)
        (transientReturnConditionedInitial X (by omega) hp))
      (transientInitialMoment4 (n - 1)
        (transientReturnConditionedInitial X (by omega) hp))) :
    K3StageBound n (transientMoment2 n X) (transientMoment3 n X)
      (transientMoment4 n X) := by
  have hs : 2 ≤ n := by omega
  let U := transientReturnConditionedInitial X hs hp
  let V := transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X)
  let u := transientInitialMoment1 (n - 1) U
  let A := transientInitialMoment2 (n - 1) U
  let C := transientInitialMoment3 (n - 1) U
  let E := transientInitialMoment4 (n - 1) U
  let x := transientHoldingMean X
  let p := transientReturnProbability X
  let q := transientTerminalProbability X
  let r := p / q
  have hq : 0 < q := by dsimp [q]; exact transientTerminalProbability_pos X
  have hu : 0 < u := by
    apply transientInitialMoment1_pos_of_weight_sum_pos
    dsimp [U]
    rw [transientReturnConditionedInitial_weight_sum X hs hp]
    norm_num
  have hVzero : transientInitialMoment1 (n - 1) V = 0 := by simpa [V] using hv0
  have hv23 := transientInitial_higher_moments_eq_zero_of_moment1_eq_zero V hVzero
  have hv4 := transientInitialMoment4_eq_zero_of_moment1_eq_zero V hVzero
  have hA0 := transientInitialAldousSheppForParent (r := n - 1) (n := n)
    (by omega) (by omega) U
  have hA : (n : ℝ) * u ^ 2 ≤ ((n : ℝ) - 1) * A := by
    dsimp [u, A]
    have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hn1] at hA0
    nlinarith
  have hC : ((n : ℝ) + 1) * A ^ 2 ≤ (n : ℝ) * u * C := by
    simpa [u, A, C] using k2_bound_for_parent (n := n) (r := n - 1)
      (by omega) (by omega) U
  have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hE : ((n : ℝ) + 2) * C ^ 2 ≤ ((n : ℝ) + 1) * A * E := by
    unfold K3StageBound at hU
    rw [hncast] at hU
    dsimp [U, A, C, E] at hU ⊢
    ring_nf at hU ⊢
    exact hU
  have hr : 0 < r := by dsimp [r, p]; positivity
  have hgap := k3_renewal_step_terminal_zero (n : ℝ) r x u A C E
    (by exact_mod_cast hn) hr (transientHoldingMean_pos X).le hu hA hC hE
  have hm2raw := transientMoment2_renewal_of_return_pos X hs hp
  have hm3raw := transientMoment3_renewal_of_return_pos X hs hp
  have hm2 : transientMoment2 n X =
      geomM2 r (kernelM1 x u) (kernelM2 x u A)
        (kernelM1 x 0) (kernelM2 x 0 0) := by
    rw [hm2raw, renewalM2_eq_geomM2 _ _ _ _ _ _ _ hq.ne'
      (transientReturnProbability_add_terminalProbability X)]
    simp only [U, V, u, A, x, p, q, r, hVzero, hv23.1]
  have hm3 : transientMoment3 n X =
      geomM3 r (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C)
        (kernelM1 x 0) (kernelM2 x 0 0) (kernelM3 x 0 0 0) := by
    rw [hm3raw, renewalM3_eq_geomM3 _ _ _ _ _ _ _ _ _ hq.ne'
      (transientReturnProbability_add_terminalProbability X)]
    simp only [U, V, u, A, C, x, p, q, r, hVzero, hv23.1, hv23.2]
  have hm4raw := transientMoment4_renewal_of_return_pos X hs hp
  have hm4 : transientMoment4 n X =
      geomM4 r (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C)
        (kernelM4 x u A C E) (kernelM1 x 0) (kernelM2 x 0 0)
        (kernelM3 x 0 0 0) (kernelM4 x 0 0 0 0) := by
    simpa only [U, V, u, A, C, E, x, p, q, r, hVzero, hv23.1, hv23.2, hv4]
      using hm4raw
  unfold K3StageBound
  rw [hm2, hm3, hm4]
  unfold stageGap at hgap
  linarith

/-- The complete concrete induction step, including both degenerate boundaries. -/
theorem k3StageBound_step {n : ℕ} (hn : 4 ≤ n) (X : TransientStart n)
    (hind : ∀ Y : TransientInitial (n - 1),
      K3StageBound (n - 1) (transientInitialMoment2 (n - 1) Y)
        (transientInitialMoment3 (n - 1) Y) (transientInitialMoment4 (n - 1) Y)) :
    K3StageBound n (transientMoment2 n X) (transientMoment3 n X)
      (transientMoment4 n X) := by
  by_cases hp0 : transientReturnProbability X = 0
  · exact k3StageBound_step_of_returnProbability_eq_zero hn X hp0
      (hind (transientTerminalConditionedInitial X (by omega)
        (transientTerminalProbability_pos X)))
  · have hp : 0 < transientReturnProbability X :=
      lt_of_le_of_ne (transientReturnProbability_nonneg X) (Ne.symm hp0)
    let U := transientReturnConditionedInitial X (by omega) hp
    let V := transientTerminalConditionedInitial X (by omega)
      (transientTerminalProbability_pos X)
    by_cases hv0 : transientInitialMoment1 (n - 1) V = 0
    · apply k3StageBound_step_of_terminalMoment1_eq_zero hn X hp
        (by simpa [V] using hv0)
      simpa [U] using hind U
    · have hv : 0 < transientInitialMoment1 (n - 1) V :=
        lt_of_le_of_ne (transientInitialMoment1_nonneg V) (Ne.symm hv0)
      let c := generalK3ReturnDataOfPos (n := n) (by omega) X hp
        (by simpa [V] using hv)
      exact k3StageBound_of_returnData hn c (hind c.U) (hind c.V)

end SSP.K2Concrete
