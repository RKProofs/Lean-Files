import SSPLean.K2ShortRenewal
import SSPLean.K2ConcreteInitial

/-!
# The shorter proof of Conjecture 1 at `k=2`

Formalization of `phase_type_moment_inequality.tex`. Strong induction starts at one
state, and each step uses only the terminal Aldous--Shepp bound and the two
lower-order third-moment inequalities. The finite transient substochastic model
allows cycles and subprobability initial vectors (an atom at zero).

No canonical representation or state-return certificate is assumed: the existing
Doob-transform and resolvent renewal construction supplies the excursions.
Moments in the general transient chart are the standard resolvent raw moments.
-/

set_option autoImplicit false
namespace SSP.K2Concrete

/-- The existing state-return construction applies already at `n=2`. -/
noncomputable def shortStateReturnData {n : ℕ} (hn : 2 ≤ n)
    (X : TransientStart n) : TransientStateReturnData n X := by
  have hn2 : 2 ≤ n := hn
  by_cases hp : 0 < transientReturnProbability X
  · refine
      { su := n - 1
        sv := n - 1
        su_pos := by omega
        sv_pos := by omega
        su_lt := by omega
        sv_lt := by omega
        U := transientReturnConditionedInitial X hn2 hp
        V := transientTerminalConditionedInitial X hn2 (transientTerminalProbability_pos X)
        x := transientHoldingMean X
        p := transientReturnProbability X
        q := transientTerminalProbability X
        x_pos := transientHoldingMean_pos X
        p_nonneg := transientReturnProbability_nonneg X
        q_pos := transientTerminalProbability_pos X
        prob_sum := transientReturnProbability_add_terminalProbability X
        return_weight_pos := by
          rw [transientReturnConditionedInitial_weight_sum X hn2 hp]
          norm_num
        moment1_decomp := transientMoment1_renewal_of_return_pos X hn2 hp
        moment2_decomp := transientMoment2_renewal_of_return_pos X hn2 hp
        moment3_decomp := transientMoment3_renewal_of_return_pos X hn2 hp }
  · have hp0 : transientReturnProbability X = 0 :=
      le_antisymm (not_lt.mp hp) (transientReturnProbability_nonneg X)
    let U := pureTransientInitial (transientReturnConditionedStart X ⟨0, by omega⟩)
    have hm := transient_renewal_moments_of_return_zero X hn2 hp0 U
    refine
      { su := n - 1
        sv := n - 1
        su_pos := by omega
        sv_pos := by omega
        su_lt := by omega
        sv_lt := by omega
        U := U
        V := transientTerminalConditionedInitial X hn2 (transientTerminalProbability_pos X)
        x := transientHoldingMean X
        p := transientReturnProbability X
        q := transientTerminalProbability X
        x_pos := transientHoldingMean_pos X
        p_nonneg := transientReturnProbability_nonneg X
        q_pos := transientTerminalProbability_pos X
        prob_sum := transientReturnProbability_add_terminalProbability X
        return_weight_pos := by
          dsimp [U]
          simp [pureTransientInitial]
        moment1_decomp := hm.1
        moment2_decomp := hm.2.1
        moment3_decomp := hm.2.2 }

/-- Improved induction step: the return second moment needs only nonnegativity. -/
theorem shortStageBound_of_state_return {n : ℕ} (hn : 2 ≤ n)
    {X : TransientStart n} (d : TransientStateReturnData n X)
    (hU0 : SSP.K2AllStages.StageBound d.su
      (transientInitialMoment1 d.su d.U) (transientInitialMoment2 d.su d.U)
      (transientInitialMoment3 d.su d.U))
    (hV0 : SSP.K2AllStages.StageBound d.sv
      (transientInitialMoment1 d.sv d.V) (transientInitialMoment2 d.sv d.V)
      (transientInitialMoment3 d.sv d.V)) :
    SSP.K2AllStages.StageBound n
      (transientMoment1 n X) (transientMoment2 n X) (transientMoment3 n X) := by
  have hU := SSP.K2AllStages.stageBound_mono d.su_pos
    (Nat.le_sub_one_of_lt d.su_lt)
    (transientInitialMoment1_nonneg d.U) (transientInitialMoment2_nonneg d.U)
    (transientInitialMoment3_nonneg d.U) hU0
  have hV := SSP.K2AllStages.stageBound_mono d.sv_pos
    (Nat.le_sub_one_of_lt d.sv_lt)
    (transientInitialMoment1_nonneg d.V) (transientInitialMoment2_nonneg d.V)
    (transientInitialMoment3_nonneg d.V) hV0
  have hncast : ((n-1 : ℕ) : ℝ)=(n : ℝ)-1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  unfold SSP.K2AllStages.StageBound at hU hV
  rw [hncast] at hU hV
  have hUc : (n+1)*(transientInitialMoment2 d.su d.U)^2 ≤
      (n : ℝ)*transientInitialMoment1 d.su d.U*transientInitialMoment3 d.su d.U := by
    nlinarith only [hU]
  have hVc : (n+1)*(transientInitialMoment2 d.sv d.V)^2 ≤
      (n : ℝ)*transientInitialMoment1 d.sv d.V*transientInitialMoment3 d.sv d.V := by
    nlinarith only [hV]
  rw [d.moment1_decomp, d.moment2_decomp, d.moment3_decomp]
  exact SSP.K2Short.renewal_bound n hn d.x
    (transientInitialMoment1 d.su d.U) (transientInitialMoment1 d.sv d.V) d.p d.q
    (transientInitialMoment2 d.su d.U) (transientInitialMoment2 d.sv d.V)
    (transientInitialMoment3 d.su d.U) (transientInitialMoment3 d.sv d.V)
    d.x_pos (transientInitialMoment1_nonneg d.U) (transientInitialMoment1_nonneg d.V)
    d.p_nonneg d.q_pos d.prob_sum (transientInitialMoment2_nonneg d.U)
    (transientInitialMoment3_nonneg d.U) (transientInitialMoment3_nonneg d.V)
    (transientInitialAldousSheppForParent d.sv_pos d.sv_lt d.V) hUc hVc

/-- Conjecture 1, `k=2`, for deterministic starts, by the shorter induction from `n=1`. -/
theorem all_transient_starts_short :
    ∀ n, 1 ≤ n → ∀ X : TransientStart n,
      SSP.K2AllStages.StageBound n
        (transientMoment1 n X) (transientMoment2 n X) (transientMoment3 n X) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn X
      by_cases hn1 : n=1
      · subst n
        exact transientStageBound_one X
      · have hn2 : 2 ≤ n := by omega
        let d := shortStateReturnData hn2 X
        apply shortStageBound_of_state_return hn2 d
        · apply transientInitialStageBound_of_components
          intro i
          exact ih d.su d.su_lt d.su_pos (d.U.component i)
        · apply transientInitialStageBound_of_components
          intro i
          exact ih d.sv d.sv_lt d.sv_pos (d.V.component i)

/-- Conjecture 1, `k=2`, including cycles and an atom at zero. -/
theorem all_transient_initial_laws_short {s : ℕ} (hs : 1 ≤ s) (X : TransientInitial s) :
    SSP.K2AllStages.StageBound s
      (transientInitialMoment1 s X) (transientInitialMoment2 s X)
      (transientInitialMoment3 s X) := by
  apply transientInitialStageBound_of_components
  intro i
  exact all_transient_starts_short s hs (X.component i)

/-- The statement with at most `s` transient states. -/
theorem at_most_stages_short {d s : ℕ} (hd : 1 ≤ d) (hds : d ≤ s)
    (X : TransientInitial d) :
    SSP.K2AllStages.StageBound s
      (transientInitialMoment1 d X) (transientInitialMoment2 d X)
      (transientInitialMoment3 d X) := by
  exact SSP.K2AllStages.stageBound_mono hd hds
    (transientInitialMoment1_nonneg X) (transientInitialMoment2_nonneg X)
    (transientInitialMoment3_nonneg X) (all_transient_initial_laws_short hd X)

/-- Ratio form of Conjecture 1 for a law with positive mean. -/
theorem conjecture_one_k2_short {s : ℕ} (hs : 1 ≤ s) (X : TransientInitial s)
    (hm : 0 < transientInitialMoment1 s X) :
    ((s : ℝ)+2)/((s : ℝ)+1) ≤
      transientInitialMoment1 s X*transientInitialMoment3 s X/
        (transientInitialMoment2 s X)^2 := by
  have has := transientInitialAldousSheppMoment hs X
  have hM2 : 0 < transientInitialMoment2 s X := by
    have hn : (0 : ℝ) < s := by exact_mod_cast hs
    have hpos : 0 < ((s : ℝ)+1)/s*(transientInitialMoment1 s X)^2 := by positivity
    linarith
  have h := all_transient_initial_laws_short hs X
  unfold SSP.K2AllStages.StageBound at h
  rw [div_le_div_iff₀ (by positivity) (sq_pos_of_pos hM2)]
  nlinarith only [h]

/-- The same theorem for the repository's concrete absorption-time measures. -/
theorem all_absorption_initial_laws_short {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionInitial s) :
    SSP.K2AllStages.StageBound s
      (initialMoment1 s X) (initialMoment2 s X) (initialMoment3 s X) := by
  apply initialStageBound_of_components
  intro i
  simpa only [toTransient_moment1, toTransient_moment2, toTransient_moment3] using
    all_transient_starts_short s hs (X.component i).toTransient

/-- Sharpness, including an arbitrary atom-at-zero weight, as in the paper. -/
theorem erlang_mixture_sharp_short (s : ℕ) (w θ : ℝ) :
    SSP.K2AllStages.gap s (SSP.K2AllStages.erlangMixMoment s w θ 1)
      (SSP.K2AllStages.erlangMixMoment s w θ 2)
      (SSP.K2AllStages.erlangMixMoment s w θ 3)=0 :=
  SSP.K2AllStages.erlang_mixture_sharp s w θ

end SSP.K2Concrete
