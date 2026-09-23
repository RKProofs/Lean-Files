import SSPLean.K3AllStagesReturnFace

/-!
# Positive-current-slope coordinates for the uniform `k = 3` induction

This module isolates the root parametrization used when the current return
slope is positive although its `q = 0` value is negative.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

theorem uniformFaceANonposP_pos (m : ℝ) (hm : 0 ≤ m) :
    0 < uniformFaceANonposP m := by
  unfold uniformFaceANonposP
  positivity

noncomputable def uniformFaceAPositiveLowZ (m u : ℝ) : ℝ :=
  uniformFaceANonposP m / (m + 6) * u

theorem exists_uniformFaceAPositiveLowZ_eq
    (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z)
    (hzP : (m + 6) * z ≤ uniformFaceANonposP m) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ uniformFaceAPositiveLowZ m u = z := by
  let u := (m + 6) * z / uniformFaceANonposP m
  have hP := uniformFaceANonposP_pos m hm
  have hm6 : 0 < m + 6 := by linarith
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one hP]
    exact hzP
  refine ⟨u, hu, hu1, ?_⟩
  unfold uniformFaceAPositiveLowZ
  dsimp [u]
  field_simp [hP.ne', hm6.ne']

noncomputable def uniformFaceAPositiveD (m s : ℝ) : ℝ :=
  (m + 3) * (m + 7) * (m + 8) * uniformFaceANonposT m s

noncomputable def uniformFaceAPositiveQ0 (m s : ℝ) : ℝ :=
  (m + 6) * s / uniformFaceAPositiveD m s

noncomputable def uniformFaceAPositiveQ (m s v : ℝ) : ℝ :=
  uniformFaceAPositiveQ0 m s
    + v * (1 - uniformFaceAPositiveQ0 m s)

theorem uniformFaceANonposT_pos
    (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 < uniformFaceANonposT m s := by
  unfold uniformFaceANonposT uniformFaceANonposZ
  have hP := uniformFaceANonposP_pos m hm
  have hm6 : 0 < m + 6 := by linarith
  positivity

theorem uniformFaceAPositiveD_pos
    (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 < uniformFaceAPositiveD m s := by
  unfold uniformFaceAPositiveD
  have hT := uniformFaceANonposT_pos m s hm hs
  positivity

theorem uniformFaceAPositiveQ0_nonneg
    (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ uniformFaceAPositiveQ0 m s := by
  unfold uniformFaceAPositiveQ0
  have hD := uniformFaceAPositiveD_pos m s hm hs
  positivity

theorem uniformFaceAPositiveQ0_lt_one
    (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceAPositiveQ0 m s < 1 := by
  have hP := uniformFaceANonposP_pos m hm
  have hm6 : 0 < m + 6 := by linarith
  have hTgt : s < uniformFaceANonposT m s := by
    unfold uniformFaceANonposT uniformFaceANonposZ
    have : 0 < uniformFaceANonposP m / (m + 6) := by positivity
    linarith
  have hA : 0 < (m + 3) * (m + 7) * (m + 8) := by positivity
  have hA6 : m + 6 ≤ (m + 3) * (m + 7) * (m + 8) := by
    have hdiff : 0 ≤ m^3 + 18 * m^2 + 100 * m + 162 := by
      positivity
    nlinarith
  have hleft : (m + 6) * s ≤
      ((m + 3) * (m + 7) * (m + 8)) * s := by
    exact mul_le_mul_of_nonneg_right hA6 hs
  have hright : ((m + 3) * (m + 7) * (m + 8)) * s <
      uniformFaceAPositiveD m s := by
    unfold uniformFaceAPositiveD
    exact mul_lt_mul_of_pos_left hTgt hA
  unfold uniformFaceAPositiveQ0
  exact (div_lt_one (uniformFaceAPositiveD_pos m s hm hs)).2
    (lt_of_le_of_lt hleft hright)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem uniformFaceACurrentM_at_positiveQ0
    (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceACurrentM (m + 4) (uniformFaceANonposT m s)
      (uniformFaceAPositiveQ0 m s) = 0 := by
  have hD := uniformFaceAPositiveD_pos m s hm hs
  unfold uniformFaceAPositiveQ0 uniformFaceAPositiveD
  unfold uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP
  unfold uniformFaceACurrentM uniformReturnM
  field_simp [hD.ne']
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem uniformFaceACurrentM_positiveQ
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceACurrentM (m + 4) (uniformFaceANonposT m s)
        (uniformFaceAPositiveQ m s v) =
      v * uniformFaceACurrentM (m + 4) (uniformFaceANonposT m s) 1 := by
  have hinterp :
      uniformFaceACurrentM (m + 4) (uniformFaceANonposT m s)
          (uniformFaceAPositiveQ m s v) =
        (1 - v) * uniformFaceACurrentM (m + 4)
            (uniformFaceANonposT m s) (uniformFaceAPositiveQ0 m s)
          + v * uniformFaceACurrentM (m + 4)
            (uniformFaceANonposT m s) 1 := by
    unfold uniformFaceAPositiveQ uniformFaceACurrentM uniformReturnM
    ring
  rw [hinterp, uniformFaceACurrentM_at_positiveQ0 m s hm hs]
  ring

theorem uniformFaceAPositiveQ_mem_unit
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceAPositiveQ m s v ∧
      uniformFaceAPositiveQ m s v ≤ 1 := by
  have hq0 := uniformFaceAPositiveQ0_nonneg m s hm hs
  have hq01 := (uniformFaceAPositiveQ0_lt_one m s hm hs).le
  unfold uniformFaceAPositiveQ
  constructor <;> nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem uniformFaceACurrentM_sub_at_positiveQ0
    (m s q : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceACurrentM (m + 4) (uniformFaceANonposT m s) q
        - uniformFaceACurrentM (m + 4) (uniformFaceANonposT m s)
          (uniformFaceAPositiveQ0 m s) =
      (q - uniformFaceAPositiveQ0 m s) * uniformFaceAPositiveD m s := by
  have hD := uniformFaceAPositiveD_pos m s hm hs
  unfold uniformFaceAPositiveQ0 uniformFaceAPositiveD
  unfold uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP
  unfold uniformFaceACurrentM uniformReturnM
  field_simp [hD.ne']
  ring

/-- Every positive current slope above the `q = 0` root is represented by a
unique interpolation parameter in `(0,1]`. -/
theorem exists_uniformFaceAPositiveQ_eq
    (m s q : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hq1 : q ≤ 1)
    (hM : 0 < uniformFaceACurrentM (m + 4)
      (uniformFaceANonposT m s) q) :
    ∃ v : ℝ, 0 < v ∧ v ≤ 1 ∧ uniformFaceAPositiveQ m s v = q := by
  let q0 := uniformFaceAPositiveQ0 m s
  let v := (q - q0) / (1 - q0)
  have hD := uniformFaceAPositiveD_pos m s hm hs
  have hq01 : q0 < 1 := by
    dsimp [q0]
    exact uniformFaceAPositiveQ0_lt_one m s hm hs
  have hroot := uniformFaceACurrentM_at_positiveQ0 m s hm hs
  have hdiff := uniformFaceACurrentM_sub_at_positiveQ0 m s q hm hs
  have hprod : 0 < (q - q0) * uniformFaceAPositiveD m s := by
    dsimp [q0] at hroot hdiff ⊢
    rw [← hdiff]
    linarith
  have hqq0 : 0 < q - q0 :=
    (mul_pos_iff_of_pos_right hD).mp hprod
  have hv : 0 < v := by
    dsimp [v]
    positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by linarith : 0 < 1 - q0)]
    linarith
  refine ⟨v, hv, hv1, ?_⟩
  unfold uniformFaceAPositiveQ
  dsimp [v, q0]
  field_simp [ne_of_gt (show 0 < 1 - uniformFaceAPositiveQ0 m s by
    exact sub_pos.mpr (uniformFaceAPositiveQ0_lt_one m s hm hs))]
  ring

theorem exists_uniformFaceANonposT_eq_of_P_le
    (m z : ℝ) (hm : 0 ≤ m)
    (hzP : uniformFaceANonposP m ≤ (m + 6) * z) :
    ∃ s : ℝ, 0 ≤ s ∧ uniformFaceANonposT m s = m + 3 + z := by
  let s := z - uniformFaceANonposP m / (m + 6)
  have hm6 : 0 < m + 6 := by linarith
  have hs : 0 ≤ s := by
    dsimp [s]
    rw [sub_nonneg, div_le_iff₀ hm6]
    simpa [mul_comm] using hzP
  refine ⟨s, hs, ?_⟩
  unfold uniformFaceANonposT uniformFaceANonposZ
  dsimp [s]
  ring

/-- The two substitutions in this module cover every point of the unbounded
positive-current-slope region. -/
theorem uniformFaceAPositive_parameter_dichotomy
    (m z q : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) (hq1 : q ≤ 1)
    (hM : 0 < uniformFaceACurrentM (m + 4) (m + 3 + z) q) :
    (∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ uniformFaceAPositiveLowZ m u = z) ∨
      (∃ s v : ℝ, 0 ≤ s ∧ 0 < v ∧ v ≤ 1 ∧
        uniformFaceANonposT m s = m + 3 + z ∧
        uniformFaceAPositiveQ m s v = q) := by
  by_cases hzP : (m + 6) * z ≤ uniformFaceANonposP m
  · left
    exact exists_uniformFaceAPositiveLowZ_eq m z hm hz hzP
  · right
    have hPz : uniformFaceANonposP m ≤ (m + 6) * z :=
      le_of_not_ge hzP
    obtain ⟨s, hs, hT⟩ :=
      exists_uniformFaceANonposT_eq_of_P_le m z hm hPz
    have hM' : 0 < uniformFaceACurrentM (m + 4)
        (uniformFaceANonposT m s) q := by
      rw [hT]
      exact hM
    obtain ⟨v, hv, hv1, hq⟩ :=
      exists_uniformFaceAPositiveQ_eq m s q hm hs hq1 hM'
    exact ⟨s, v, hs, hv, hv1, hT, hq⟩

/-! ### Projective subdivision of the high-`z` chart -/

theorem exists_right_ratio_of_le
    (v w : ℝ) (hv : 0 < v) (hw : 0 ≤ w) (hwv : w ≤ v) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ v * t = w := by
  let t := w / v
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    rw [div_le_one hv]
    exact hwv
  refine ⟨t, ht, ht1, ?_⟩
  dsimp [t]
  field_simp [hv.ne']

theorem exists_left_ratio_of_le
    (v w : ℝ) (hv : 0 < v) (hvw : v ≤ w) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ w * t = v := by
  have hw : 0 < w := lt_of_lt_of_le hv hvw
  let t := v / w
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    rw [div_le_one hw]
    exact hvw
  refine ⟨t, ht, ht1, ?_⟩
  dsimp [t]
  field_simp [hw.ne']

/-- Every face coordinate in the high-`z` parameterization lies either in
the Bernstein-positive chart `w = v*t`, or in its complementary chart
`v = w*t`.  The latter is split at `t = 1/2`, isolating precisely the small
region where the active-gradient hypothesis is still needed. -/
theorem uniformFaceAPositive_high_chart_trichotomy
    (v w : ℝ) (hv : 0 < v) (hw : 0 ≤ w) :
    (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ w = v * t) ∨
      (∃ t : ℝ, 0 < t ∧ t < 1 / 2 ∧ v = w * t) ∨
      (∃ t : ℝ, 1 / 2 ≤ t ∧ t ≤ 1 ∧ v = w * t) := by
  by_cases hwv : w ≤ v
  · left
    obtain ⟨t, ht, ht1, htw⟩ := exists_right_ratio_of_le v w hv hw hwv
    exact ⟨t, ht, ht1, htw.symm⟩
  · right
    have hvw : v ≤ w := le_of_not_ge hwv
    obtain ⟨t, ht, ht1, htv⟩ := exists_left_ratio_of_le v w hv hvw
    by_cases htHalf : t < 1 / 2
    · left
      exact ⟨t, ht, htHalf, htv.symm⟩
    · right
      exact ⟨t, le_of_not_gt htHalf, ht1, htv.symm⟩

/-! ### The Bernstein-positive high chart `w = v*t` -/

/-- The four cubic Bernstein coefficients after using
`uniformFaceACurrentM = v * uniformFaceACurrentM(·,1)` and extracting the
common factor `v^3`. -/
noncomputable def uniformFaceAPositiveHighWVC0 (m s v : ℝ) : ℝ :=
  (m+4)^3 *
    (uniformFaceACurrentM (m+4) (uniformFaceANonposT m s) 1)^3 *
    uniformFaceACoreXC0 (m+4) (uniformFaceANonposT m s)
      (uniformFaceAPositiveQ m s v)

noncomputable def uniformFaceAPositiveHighWVC1 (m s v : ℝ) : ℝ :=
  uniformFaceAPositiveHighWVC0 m s v + (1/3) * (m+4)^2 *
    (uniformFaceACurrentM (m+4) (uniformFaceANonposT m s) 1)^2 *
    uniformFaceACurrentK (m+4) (uniformFaceANonposT m s)
      (uniformFaceAPositiveQ m s v) *
    uniformFaceACoreXC1 (m+4) (uniformFaceANonposT m s)
      (uniformFaceAPositiveQ m s v)

noncomputable def uniformFaceAPositiveHighWVC2 (m s v : ℝ) : ℝ :=
  uniformFaceAPositiveHighWVC0 m s v + (2/3) * (m+4)^2 *
    (uniformFaceACurrentM (m+4) (uniformFaceANonposT m s) 1)^2 *
    uniformFaceACurrentK (m+4) (uniformFaceANonposT m s)
      (uniformFaceAPositiveQ m s v) *
    uniformFaceACoreXC1 (m+4) (uniformFaceANonposT m s)
      (uniformFaceAPositiveQ m s v)
    + (1/3) * (m+4) *
      uniformFaceACurrentM (m+4) (uniformFaceANonposT m s) 1 *
      (uniformFaceACurrentK (m+4) (uniformFaceANonposT m s)
        (uniformFaceAPositiveQ m s v))^2 *
      uniformFaceACoreXC2 (m+4) (uniformFaceANonposT m s)
        (uniformFaceAPositiveQ m s v)

noncomputable def uniformFaceAPositiveHighWVC3 (m s v : ℝ) : ℝ :=
  uniformFaceAPositiveHighWVC0 m s v + (m+4)^2 *
    (uniformFaceACurrentM (m+4) (uniformFaceANonposT m s) 1)^2 *
    uniformFaceACurrentK (m+4) (uniformFaceANonposT m s)
      (uniformFaceAPositiveQ m s v) *
    uniformFaceACoreXC1 (m+4) (uniformFaceANonposT m s)
      (uniformFaceAPositiveQ m s v)
    + (m+4) *
      uniformFaceACurrentM (m+4) (uniformFaceANonposT m s) 1 *
      (uniformFaceACurrentK (m+4) (uniformFaceANonposT m s)
        (uniformFaceAPositiveQ m s v))^2 *
      uniformFaceACoreXC2 (m+4) (uniformFaceANonposT m s)
        (uniformFaceAPositiveQ m s v)
    + (uniformFaceACurrentK (m+4) (uniformFaceANonposT m s)
        (uniformFaceAPositiveQ m s v))^3 *
      uniformFaceACoreXC3 (m+4) (uniformFaceANonposT m s)
        (uniformFaceAPositiveQ m s v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Exact cubic Bernstein decomposition in the projective ratio `t`.  The
factor `v^3` is what reduces the remaining coefficient problem from degree
nine to degree six in `v`. -/
theorem uniformFaceAPositiveHighWV_bernstein_t
    (m s v t : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceACurrentPoly (m+4) (uniformFaceANonposT m s)
        (uniformFaceAPositiveQ m s v) (v*t) =
      v^3 * cornerBern3 (uniformFaceAPositiveHighWVC0 m s v)
        (uniformFaceAPositiveHighWVC1 m s v)
        (uniformFaceAPositiveHighWVC2 m s v)
        (uniformFaceAPositiveHighWVC3 m s v) t := by
  unfold uniformFaceACurrentPoly
  rw [uniformFaceACurrentM_positiveQ m s v hm hs]
  unfold uniformFaceAPositiveHighWVC1 uniformFaceAPositiveHighWVC2
  unfold uniformFaceAPositiveHighWVC3 uniformFaceAPositiveHighWVC0
  unfold cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
/-- At `X = 0`, all four `q`-Bernstein coefficients of the return core are
nonnegative on the high-`z` chart. -/
theorem uniformFaceACoreXC0_nonneg_of_positive_high
    (m s q : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ uniformFaceACoreXC0 (m+4) (uniformFaceANonposT m s) q := by
  unfold uniformFaceACoreXC0
  apply uniformFaceACore_nonneg_of_q_bernstein
      (m+4) 0 (uniformFaceANonposT m s) q (by linarith) (by norm_num)
      hq hq1
  · exact uniformFaceAQB1_nonneg (m+4) 0 (uniformFaceANonposT m s)
      (by linarith) (by norm_num) (uniformFaceANonposT_pos m s hm hs).le
  · exact uniformFaceAQB2_nonneg (m+4) 0 (uniformFaceANonposT m s)
      (by linarith) (by norm_num) (uniformFaceANonposT_pos m s hm hs).le
  · unfold uniformFaceAQB3 uniformFaceANonposT uniformFaceANonposZ
    unfold uniformFaceANonposP uniformFaceACore
    field_simp
    ring_nf
    positivity

/-- The left coefficient of the high-chart cubic is unconditional. -/
theorem uniformFaceAPositiveHighWVC0_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceAPositiveHighWVC0 m s v := by
  have hq := uniformFaceAPositiveQ_mem_unit m s v hm hs hv hv1
  unfold uniformFaceAPositiveHighWVC0
  have hcore := uniformFaceACoreXC0_nonneg_of_positive_high
    m s (uniformFaceAPositiveQ m s v) hm hs hq.1 hq.2
  have hz : 0 ≤ uniformFaceANonposZ m s := by
    unfold uniformFaceANonposZ uniformFaceANonposP
    positivity
  have hM : 0 < uniformFaceACurrentM (m+4)
      (uniformFaceANonposT m s) 1 := by
    simpa [uniformFaceALargeM, uniformFaceACurrentM,
      uniformFaceANonposT] using
      uniformFaceALargeM_pos m (uniformFaceANonposZ m s) hm hz
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- On the high chart, the return-side intercept at an admissible `q` does
not exceed its value at `q = 1`. -/
theorem uniformFaceACurrentK_le_one_of_positive_high
    (m s q : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) (hq1 : q ≤ 1) :
    uniformFaceACurrentK (m+4) (uniformFaceANonposT m s) q ≤
      uniformFaceACurrentK (m+4) (uniformFaceANonposT m s) 1 := by
  have hid : uniformFaceACurrentK (m+4) (uniformFaceANonposT m s) 1 -
      uniformFaceACurrentK (m+4) (uniformFaceANonposT m s) q =
      (1-q)*(m+6)*(uniformFaceANonposT m s) *
        (m^4 + m^3*uniformFaceANonposZ m s + 16*m^3
          + 16*m^2*uniformFaceANonposZ m s + 91*m^2
          + m*(uniformFaceANonposZ m s)^2
          + 83*m*uniformFaceANonposZ m s + 222*m
          + 4*(uniformFaceANonposZ m s)^2
          + 132*uniformFaceANonposZ m s + 198) := by
    unfold uniformFaceACurrentK uniformFaceANonposT uniformReturnK
    ring
  rw [← sub_nonneg, hid]
  have hz : 0 ≤ uniformFaceANonposZ m s := by
    unfold uniformFaceANonposZ uniformFaceANonposP
    positivity
  have hT : 0 < uniformFaceANonposT m s :=
    uniformFaceANonposT_pos m s hm hs
  have hpoly : 0 ≤
        m^4 + m^3*uniformFaceANonposZ m s + 16*m^3
          + 16*m^2*uniformFaceANonposZ m s + 91*m^2
          + m*(uniformFaceANonposZ m s)^2
          + 83*m*uniformFaceANonposZ m s + 222*m
          + 4*(uniformFaceANonposZ m s)^2
          + 132*uniformFaceANonposZ m s + 198 := by positivity
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The right cubic coefficient is the original core evaluated at the
projective endpoint `K(q)/(n*M(1))`. -/
theorem uniformFaceAPositiveHighWVC3_eq_core
    (m s v : ℝ) (hn : m+4 ≠ 0)
    (hM : uniformFaceACurrentM (m+4) (uniformFaceANonposT m s) 1 ≠ 0) :
    uniformFaceAPositiveHighWVC3 m s v = (m+4)^3 *
      (uniformFaceACurrentM (m+4) (uniformFaceANonposT m s) 1)^3 *
      uniformFaceACore (m+4)
        (uniformFaceACurrentK (m+4) (uniformFaceANonposT m s)
          (uniformFaceAPositiveQ m s v) /
          ((m+4) * uniformFaceACurrentM (m+4)
            (uniformFaceANonposT m s) 1))
        (uniformFaceANonposT m s) (uniformFaceAPositiveQ m s v) := by
  unfold uniformFaceAPositiveHighWVC3 uniformFaceAPositiveHighWVC0
  unfold uniformFaceACoreXC0 uniformFaceACoreXC1
  unfold uniformFaceACoreXC2 uniformFaceACoreXC3 uniformFaceACore
  field_simp [hn, hM]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
/-- The projective endpoint coefficient is nonnegative. -/
theorem uniformFaceAPositiveHighWVC3_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceAPositiveHighWVC3 m s v := by
  have hz : 0 ≤ uniformFaceANonposZ m s := by
    unfold uniformFaceANonposZ uniformFaceANonposP
    positivity
  have hM : 0 < uniformFaceACurrentM (m+4)
      (uniformFaceANonposT m s) 1 := by
    simpa [uniformFaceALargeM, uniformFaceACurrentM,
      uniformFaceANonposT] using
      uniformFaceALargeM_pos m (uniformFaceANonposZ m s) hm hz
  have hq := uniformFaceAPositiveQ_mem_unit m s v hm hs hv hv1
  let q := uniformFaceAPositiveQ m s v
  let K := uniformFaceACurrentK (m+4) (uniformFaceANonposT m s) q
  let X := K / ((m+4) * uniformFaceACurrentM (m+4)
    (uniformFaceANonposT m s) 1)
  have hK : 0 < K := by
    dsimp [K]
    exact uniformFaceACurrentK_pos (m+4) (uniformFaceANonposT m s) q
      (by linarith) (by unfold uniformFaceANonposT; linarith)
      hq.1 hq.2
  have hX : 0 < X := by dsimp [X]; positivity
  have hKle : K ≤ uniformFaceACurrentK (m+4)
      (uniformFaceANonposT m s) 1 := by
    dsimp [K, q]
    exact uniformFaceACurrentK_le_one_of_positive_high m s
      (uniformFaceAPositiveQ m s v) hm hs hq.2
  have hreturn1 : uniformReturnSide (m+4) 1
      (uniformFaceANonposT m s) X 1 ≤ 0 := by
    rw [uniformReturnSide_eq_current]
    dsimp [X]
    field_simp [hM.ne']
    nlinarith
  have h3 := uniformFaceAQB3_nonneg_of_T_ge_of_returnSide_nonpos
    (m+4) 1 (uniformFaceANonposT m s) X (by linarith) (by norm_num)
    (by unfold uniformFaceANonposT; linarith) hX hreturn1
  have hcore := uniformFaceACore_nonneg_of_q_bernstein
    (m+4) X (uniformFaceANonposT m s) q (by linarith) hX.le
    hq.1 hq.2
    (uniformFaceAQB1_nonneg (m+4) X (uniformFaceANonposT m s)
      (by linarith) hX.le (uniformFaceANonposT_pos m s hm hs).le)
    (uniformFaceAQB2_nonneg (m+4) X (uniformFaceANonposT m s)
      (by linarith) hX.le (uniformFaceANonposT_pos m s hm hs).le)
    (by simpa using h3)
  rw [uniformFaceAPositiveHighWVC3_eq_core m s v (by linarith) hM.ne']
  change 0 ≤ (m+4)^3 *
    (uniformFaceACurrentM (m+4) (uniformFaceANonposT m s) 1)^3 *
      uniformFaceACore (m+4) X (uniformFaceANonposT m s) q
  positivity

/-- Only the two middle cubic coefficients remain in the `w = v*t` chart. -/
theorem uniformFaceAPositiveHighWV_nonneg_of_middle_coefficients
    (m s v t : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (h1 : 0 ≤ uniformFaceAPositiveHighWVC1 m s v)
    (h2 : 0 ≤ uniformFaceAPositiveHighWVC2 m s v) :
    0 ≤ uniformFaceACurrentPoly (m+4) (uniformFaceANonposT m s)
      (uniformFaceAPositiveQ m s v) (v*t) := by
  rw [uniformFaceAPositiveHighWV_bernstein_t m s v t hm hs]
  have h0 := uniformFaceAPositiveHighWVC0_nonneg m s v hm hs hv hv1
  have h3 := uniformFaceAPositiveHighWVC3_nonneg m s v hm hs hv hv1
  have hbern := cornerBern3_nonneg _ _ _ _ t h0 h1 h2 h3 ht ht1
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
/-- The `w = v*t` high chart is nonnegative without a gradient hypothesis.
Instead of expanding its two middle Bernstein coefficients, evaluate the
original core at `X = t*K(q)/(n*M(1))`; monotonicity of `K` makes the
`q = 1` return-side condition automatic. -/
theorem uniformFaceAPositiveHighWV_nonneg
    (m s v t : ℝ)
    (hm : 0 ≤ m) (hs : 0 ≤ s) (hv : 0 < v) (hv1 : v ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ uniformFaceACurrentPoly (m+4) (uniformFaceANonposT m s)
      (uniformFaceAPositiveQ m s v) (v*t) := by
  by_cases ht0 : t = 0
  · subst t
    rw [uniformFaceAPositiveHighWV_bernstein_t m s v 0 hm hs]
    norm_num [cornerBern3]
    exact mul_nonneg (by positivity)
      (uniformFaceAPositiveHighWVC0_nonneg m s v hm hs hv.le hv1)
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hz : 0 ≤ uniformFaceANonposZ m s := by
    unfold uniformFaceANonposZ uniformFaceANonposP
    positivity
  have hM : 0 < uniformFaceACurrentM (m+4)
      (uniformFaceANonposT m s) 1 := by
    simpa [uniformFaceALargeM, uniformFaceACurrentM,
      uniformFaceANonposT] using
      uniformFaceALargeM_pos m (uniformFaceANonposZ m s) hm hz
  have hq := uniformFaceAPositiveQ_mem_unit m s v hm hs hv.le hv1
  let q := uniformFaceAPositiveQ m s v
  let K := uniformFaceACurrentK (m+4) (uniformFaceANonposT m s) q
  let X := t*K / ((m+4) * uniformFaceACurrentM (m+4)
    (uniformFaceANonposT m s) 1)
  have hK : 0 < K := by
    dsimp [K]
    exact uniformFaceACurrentK_pos (m+4) (uniformFaceANonposT m s) q
      (by linarith) (by unfold uniformFaceANonposT; linarith)
      hq.1 hq.2
  have hX : 0 < X := by dsimp [X]; positivity
  have hKle : K ≤ uniformFaceACurrentK (m+4)
      (uniformFaceANonposT m s) 1 := by
    dsimp [K, q]
    exact uniformFaceACurrentK_le_one_of_positive_high m s
      (uniformFaceAPositiveQ m s v) hm hs hq.2
  have hreturn1 : uniformReturnSide (m+4) 1
      (uniformFaceANonposT m s) X 1 ≤ 0 := by
    rw [uniformReturnSide_eq_current]
    dsimp [X]
    field_simp [hM.ne']
    nlinarith
  have h3 := uniformFaceAQB3_nonneg_of_T_ge_of_returnSide_nonpos
    (m+4) 1 (uniformFaceANonposT m s) X (by linarith) (by norm_num)
    (by unfold uniformFaceANonposT; linarith) hX hreturn1
  have hcore := uniformFaceACore_nonneg_of_q_bernstein
    (m+4) X (uniformFaceANonposT m s) q (by linarith) hX.le
    hq.1 hq.2
    (uniformFaceAQB1_nonneg (m+4) X (uniformFaceANonposT m s)
      (by linarith) hX.le (uniformFaceANonposT_pos m s hm hs).le)
    (uniformFaceAQB2_nonneg (m+4) X (uniformFaceANonposT m s)
      (by linarith) hX.le (uniformFaceANonposT_pos m s hm hs).le)
    (by simpa using h3)
  have hMq : 0 < uniformFaceACurrentM (m+4)
      (uniformFaceANonposT m s) q := by
    dsimp [q]
    rw [uniformFaceACurrentM_positiveQ m s v hm hs]
    positivity
  rw [← uniformFaceACurrentScaled_eq_poly (m+4)
    (uniformFaceANonposT m s) q (v*t) (by linarith) hMq.ne']
  unfold uniformFaceACurrentScaled
  have hXid : v*t*K / ((m+4) *
      uniformFaceACurrentM (m+4) (uniformFaceANonposT m s) q) = X := by
    dsimp [X, K, q]
    rw [uniformFaceACurrentM_positiveQ m s v hm hs]
    field_simp [hv.ne', hM.ne']
  change 0 ≤ (m+4)^3 *
    (uniformFaceACurrentM (m+4) (uniformFaceANonposT m s) q)^3 *
      uniformFaceACore (m+4)
        (v*t*K / ((m+4) * uniformFaceACurrentM (m+4)
          (uniformFaceANonposT m s) q))
        (uniformFaceANonposT m s) q
  rw [hXid]
  positivity

/-- Assembly theorem for the remaining positive-current-slope polynomial.
It separates the low-`z` chart and the three high-`z` projective charts.  The
two charts already detected as coefficientwise nonnegative do not retain the
gradient hypothesis; only the genuinely difficult charts do. -/
theorem uniformFaceAPositive_poly_nonneg_of_chart_certificates
    (m z q w : ℝ)
    (hm : 0 ≤ m) (hz : 0 ≤ z) (hq : 0 < q) (hq1 : q ≤ 1)
    (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hM : 0 < uniformFaceACurrentM (m + 4) (m + 3 + z) q)
    (hgrad : uniformFaceACurrentGradPoly (m + 4) (m + 3 + z) q w < 0)
    (hLow : ∀ m u q w : ℝ,
      0 ≤ m → 0 ≤ u → u ≤ 1 → 0 < q → q ≤ 1 →
      0 ≤ w → w ≤ 1 →
      uniformFaceACurrentGradPoly (m + 4)
          (m + 3 + uniformFaceAPositiveLowZ m u) q w < 0 →
      0 ≤ uniformFaceACurrentPoly (m + 4)
          (m + 3 + uniformFaceAPositiveLowZ m u) q w)
    (hHighVWSmall : ∀ m s v t w : ℝ,
      0 ≤ m → 0 ≤ s → 0 < v → v ≤ 1 →
      0 < t → t < 1 / 2 → 0 ≤ w → w ≤ 1 → v = w * t →
      uniformFaceACurrentGradPoly (m + 4) (uniformFaceANonposT m s)
          (uniformFaceAPositiveQ m s v) w < 0 →
      0 ≤ uniformFaceACurrentPoly (m + 4) (uniformFaceANonposT m s)
          (uniformFaceAPositiveQ m s v) w)
    (hHighVWLarge : ∀ m s v t w : ℝ,
      0 ≤ m → 0 ≤ s → 0 < v → v ≤ 1 →
      1 / 2 ≤ t → t ≤ 1 → 0 ≤ w → w ≤ 1 → v = w * t →
      0 ≤ uniformFaceACurrentPoly (m + 4) (uniformFaceANonposT m s)
          (uniformFaceAPositiveQ m s v) w) :
    0 ≤ uniformFaceACurrentPoly (m + 4) (m + 3 + z) q w := by
  rcases uniformFaceAPositive_parameter_dichotomy
      m z q hm hz hq1 hM with hlow | hhigh
  · obtain ⟨u, hu, hu1, huz⟩ := hlow
    rw [← huz] at hgrad ⊢
    exact hLow m u q w hm hu hu1 hq hq1 hw hw1 hgrad
  · obtain ⟨s, v, hs, hv, hv1, hT, hqv⟩ := hhigh
    rw [← hT, ← hqv] at hgrad ⊢
    rcases uniformFaceAPositive_high_chart_trichotomy v w hv hw with
      hwv | hvwSmall | hvwLarge
    · obtain ⟨t, ht, ht1, hwt⟩ := hwv
      rw [hwt]
      exact uniformFaceAPositiveHighWV_nonneg m s v t hm hs hv hv1 ht ht1
    · obtain ⟨t, ht, htHalf, hvt⟩ := hvwSmall
      exact hHighVWSmall m s v t w hm hs hv hv1 ht htHalf hw hw1 hvt hgrad
    · obtain ⟨t, htHalf, ht1, hvt⟩ := hvwLarge
      exact hHighVWLarge m s v t w hm hs hv hv1 htHalf ht1 hw hw1 hvt

end SSP.K3AllStages
