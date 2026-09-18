import SSPLean.K2ConcreteInitial

/-!
# A concrete Erlang equality witness for the all-stage `k = 2` inequality

The strict operator-norm chart used for the measure construction excludes a serial chain whose
intermediate rows have sum one.  The general `TransientStart` interface does not.  This module
constructs that boundary chain, computes its resolvent and first three moments, and proves that
the final all-stage inequality is attained exactly there.
-/

open scoped Matrix.Norms.Operator
open Matrix Finset

set_option autoImplicit false

namespace SSP.K2Concrete

noncomputable def erlangShiftQ (s : ℕ) : Matrix (Fin s) (Fin s) ℝ :=
  fun i j => if h : i.val + 1 < s then if j = ⟨i.val + 1, h⟩ then 1 else 0 else 0

noncomputable def erlangResolvent (s : ℕ) : Matrix (Fin s) (Fin s) ℝ :=
  fun i j => if i ≤ j then 1 else 0

theorem erlangShiftQ_mulVec (s : ℕ) (v : Fin s → ℝ) (i : Fin s) :
    (erlangShiftQ s).mulVec v i =
      if h : i.val + 1 < s then v ⟨i.val + 1, h⟩ else 0 := by
  classical
  unfold Matrix.mulVec dotProduct
  by_cases h : i.val + 1 < s
  · simp only [erlangShiftQ, dif_pos h]
    simp
  · simp only [erlangShiftQ, dif_neg h]
    simp

theorem one_sub_erlangShiftQ_mul_erlangResolvent (s : ℕ) :
    (1 - erlangShiftQ s) * erlangResolvent s = 1 := by
  rw [sub_mul, one_mul]
  ext i j
  change erlangResolvent s i j -
      (erlangShiftQ s).mulVec (fun x => erlangResolvent s x j) i =
    (1 : Matrix (Fin s) (Fin s) ℝ) i j
  rw [erlangShiftQ_mulVec]
  by_cases h : i.val + 1 < s
  · rw [dif_pos h]
    rcases lt_trichotomy i j with hij | hij | hij
    · have hsucc : (⟨i.val + 1, h⟩ : Fin s) ≤ j := by
        exact Fin.mk_le_mk.mpr hij
      simp [erlangResolvent, hij.ne, hij.le, hsucc]
    · subst j
      have hsucc : ¬(⟨i.val + 1, h⟩ : Fin s) ≤ i := by
        exact not_le.mpr (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _))
      simp [erlangResolvent, hsucc]
    · have hile : ¬i ≤ j := not_le.mpr hij
      have hsucc : ¬(⟨i.val + 1, h⟩ : Fin s) ≤ j := by
        intro hj
        apply hile
        exact le_trans (Fin.mk_le_mk.mpr (by omega)) hj
      simp [erlangResolvent, hij.ne', hile, hsucc]
  · rw [dif_neg h]
    by_cases hij : i = j
    · subst j
      simp [erlangResolvent]
    · have hji : j < i := by
        apply lt_of_not_ge
        intro hijle
        have hijlt : i < j := lt_of_le_of_ne hijle hij
        change i.val < j.val at hijlt
        omega
      simp [erlangResolvent, hij, not_le.mpr hji]

theorem one_sub_erlangShiftQ_isUnit (s : ℕ) : IsUnit (1 - erlangShiftQ s) := by
  exact IsUnit.of_mul_eq_one _ (one_sub_erlangShiftQ_mul_erlangResolvent s)

theorem erlangShiftQ_inverse (s : ℕ) :
    (1 - erlangShiftQ s)⁻¹ = erlangResolvent s := by
  exact Matrix.inv_eq_right_inv (one_sub_erlangShiftQ_mul_erlangResolvent s)

noncomputable def erlangTransientStart (s : ℕ) (hs : 1 ≤ s) : TransientStart s where
  Q := erlangShiftQ s
  hQ := by
    intro i j
    unfold erlangShiftQ
    split_ifs <;> positivity
  hrow := by
    intro i
    by_cases h : i.val + 1 < s
    · simp [erlangShiftQ, h]
    · simp [erlangShiftQ, h]
  hu := one_sub_erlangShiftQ_isUnit s
  i := ⟨0, hs⟩

theorem erlangResolvent_mulVec (s : ℕ) (v : Fin s → ℝ) (i : Fin s) :
    (erlangResolvent s).mulVec v i = ∑ j ∈ Finset.Ici i, v j := by
  unfold Matrix.mulVec dotProduct erlangResolvent
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 2
  ext j
  simp

theorem erlangResolvent_one (s : ℕ) (i : Fin s) :
    (erlangResolvent s).mulVec (fun _ => (1 : ℝ)) i = s - i.val := by
  rw [erlangResolvent_mulVec]
  simp

noncomputable def erlangV1 (s : ℕ) (i : Fin s) : ℝ := s - i.val

noncomputable def erlangV2 (s : ℕ) (i : Fin s) : ℝ :=
  erlangV1 s i * (erlangV1 s i + 1) / 2

noncomputable def erlangV3 (s : ℕ) (i : Fin s) : ℝ :=
  erlangV1 s i * (erlangV1 s i + 1) * (erlangV1 s i + 2) / 6

theorem one_sub_erlangShiftQ_mulVec_v2 (s : ℕ) :
    (1 - erlangShiftQ s).mulVec (erlangV2 s) = erlangV1 s := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  funext i
  simp only [Pi.sub_apply]
  rw [erlangShiftQ_mulVec]
  by_cases h : i.val + 1 < s
  · rw [dif_pos h]
    have hr : erlangV1 s (⟨i.val + 1, h⟩ : Fin s) = erlangV1 s i - 1 := by
      unfold erlangV1
      push_cast
      ring
    simp only [erlangV2, hr]
    ring
  · rw [dif_neg h]
    have hi : i.val + 1 = s := by omega
    have hr : erlangV1 s i = 1 := by
      simp [erlangV1, ← hi]
    norm_num [erlangV2, hr]

theorem one_sub_erlangShiftQ_mulVec_v3 (s : ℕ) :
    (1 - erlangShiftQ s).mulVec (erlangV3 s) = erlangV2 s := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  funext i
  simp only [Pi.sub_apply]
  rw [erlangShiftQ_mulVec]
  by_cases h : i.val + 1 < s
  · rw [dif_pos h]
    have hr : erlangV1 s (⟨i.val + 1, h⟩ : Fin s) = erlangV1 s i - 1 := by
      unfold erlangV1
      push_cast
      ring
    simp only [erlangV2, erlangV3, hr]
    ring
  · rw [dif_neg h]
    have hi : i.val + 1 = s := by omega
    have hr : erlangV1 s i = 1 := by
      simp [erlangV1, ← hi]
    norm_num [erlangV2, erlangV3, hr]

theorem erlangResolvent_mulVec_v1 (s : ℕ) :
    (erlangResolvent s).mulVec (erlangV1 s) = erlangV2 s := by
  rw [← erlangShiftQ_inverse]
  rw [← one_sub_erlangShiftQ_mulVec_v2 s, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul (1 - erlangShiftQ s)
      (Matrix.isUnit_iff_isUnit_det _ |>.mp (one_sub_erlangShiftQ_isUnit s)),
    Matrix.one_mulVec]

theorem erlangResolvent_mulVec_v2 (s : ℕ) :
    (erlangResolvent s).mulVec (erlangV2 s) = erlangV3 s := by
  rw [← erlangShiftQ_inverse]
  rw [← one_sub_erlangShiftQ_mulVec_v3 s, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul (1 - erlangShiftQ s)
      (Matrix.isUnit_iff_isUnit_det _ |>.mp (one_sub_erlangShiftQ_isUnit s)),
    Matrix.one_mulVec]

theorem erlangTransientStart_moments (s : ℕ) (hs : 1 ≤ s) :
    transientMoment1 s (erlangTransientStart s hs) = s ∧
      transientMoment2 s (erlangTransientStart s hs) = (s : ℝ) * (s + 1) ∧
      transientMoment3 s (erlangTransientStart s hs) =
        (s : ℝ) * (s + 1) * (s + 2) := by
  let z : Fin s := ⟨0, by omega⟩
  have h1 : (erlangResolvent s).mulVec (fun _ => (1 : ℝ)) = erlangV1 s := by
    funext i
    rw [erlangResolvent_one]
    rfl
  have h2 : (erlangResolvent s).mulVec (erlangV1 s) = erlangV2 s :=
    erlangResolvent_mulVec_v1 s
  have h3 : (erlangResolvent s).mulVec (erlangV2 s) = erlangV3 s :=
    erlangResolvent_mulVec_v2 s
  constructor
  · unfold transientMoment1
    change ((1 - erlangShiftQ s)⁻¹.mulVec (fun _ => (1 : ℝ))) z = s
    rw [erlangShiftQ_inverse, h1]
    simp [erlangV1, z]
  constructor
  · unfold transientMoment2
    change 2 * ((1 - erlangShiftQ s)⁻¹.mulVec
      ((1 - erlangShiftQ s)⁻¹.mulVec (fun _ => (1 : ℝ)))) z =
        (s : ℝ) * (s + 1)
    rw [erlangShiftQ_inverse, h1, h2]
    simp [erlangV2, erlangV1, z]
    ring
  · unfold transientMoment3
    change 6 * ((1 - erlangShiftQ s)⁻¹.mulVec ((1 - erlangShiftQ s)⁻¹.mulVec
      ((1 - erlangShiftQ s)⁻¹.mulVec (fun _ => (1 : ℝ))))) z =
        (s : ℝ) * (s + 1) * (s + 2)
    rw [erlangShiftQ_inverse, h1, h2, h3]
    simp [erlangV3, erlangV1, z]
    ring

theorem erlangTransientStart_is_sharp (s : ℕ) (hs : 1 ≤ s) :
    SSP.K2AllStages.gap s
      (transientMoment1 s (erlangTransientStart s hs))
      (transientMoment2 s (erlangTransientStart s hs))
      (transientMoment3 s (erlangTransientStart s hs)) = 0 := by
  obtain ⟨h1, h2, h3⟩ := erlangTransientStart_moments s hs
  rw [h1, h2, h3]
  unfold SSP.K2AllStages.gap
  ring

/-- The concrete subprobability initial law representing mass `1 - w` at zero and mass `w` on
the serial `s`-stage Erlang chain. -/
noncomputable def erlangMixtureInitial (s : ℕ) (hs : 1 ≤ s) (w : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : TransientInitial s where
  model := erlangTransientStart s hs
  weight := fun j => if j = (erlangTransientStart s hs).i then w else 0
  weight_nonneg := by
    intro j
    split_ifs <;> positivity
  weight_sum_le_one := by
    simpa using hw1

theorem erlangMixtureInitial_moments (s : ℕ) (hs : 1 ≤ s) (w : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    transientInitialMoment1 s (erlangMixtureInitial s hs w hw0 hw1) =
        SSP.K2AllStages.erlangMixMoment s w 1 1 ∧
      transientInitialMoment2 s (erlangMixtureInitial s hs w hw0 hw1) =
        SSP.K2AllStages.erlangMixMoment s w 1 2 ∧
      transientInitialMoment3 s (erlangMixtureInitial s hs w hw0 hw1) =
        SSP.K2AllStages.erlangMixMoment s w 1 3 := by
  obtain ⟨h1, h2, h3⟩ := erlangTransientStart_moments s hs
  constructor
  · simp [transientInitialMoment1, erlangMixtureInitial, TransientInitial.component,
      h1, SSP.K2AllStages.erlangMixMoment]
  constructor
  · simp [transientInitialMoment2, erlangMixtureInitial, TransientInitial.component,
      h2, SSP.K2AllStages.erlangMixMoment, mul_assoc]
  · simp [transientInitialMoment3, erlangMixtureInitial, TransientInitial.component,
      h3, SSP.K2AllStages.erlangMixMoment, mul_assoc]

/-- The atom-at-zero/Erlang family is realized inside `TransientInitial` and attains equality. -/
theorem erlangMixtureInitial_is_sharp (s : ℕ) (hs : 1 ≤ s) (w : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    SSP.K2AllStages.gap s
      (transientInitialMoment1 s (erlangMixtureInitial s hs w hw0 hw1))
      (transientInitialMoment2 s (erlangMixtureInitial s hs w hw0 hw1))
      (transientInitialMoment3 s (erlangMixtureInitial s hs w hw0 hw1)) = 0 := by
  obtain ⟨h1, h2, h3⟩ := erlangMixtureInitial_moments s hs w hw0 hw1
  rw [h1, h2, h3]
  exact SSP.K2AllStages.erlang_mixture_sharp s w 1

end SSP.K2Concrete
