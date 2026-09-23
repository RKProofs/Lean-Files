import SSPLean.K3AllStagesMiddleLow

/-!
# The upper-middle return-face certificate for `k = 3`

This covers `m² + 39 ≤ X ≤ P(m)/8` in the nonpositive-current-slope
parameterization.  The transformed polynomial is bicubic in the interval
coordinate and the terminal mixture coordinate.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

noncomputable def uniformFaceANonposMiddleHigh
    (m s v w : ℝ) : ℝ :=
  uniformFaceANonposScaled m s v
    ((m^2 + 39) + w * (uniformFaceANonposP m / 8 - (m^2 + 39)))

noncomputable def uniformFaceANonposMiddleHighB0
    (m s v : ℝ) : ℝ :=
  uniformCubicSampleB0 (fun w => uniformFaceANonposMiddleHigh m s v w)

noncomputable def uniformFaceANonposMiddleHighB1
    (m s v : ℝ) : ℝ :=
  uniformCubicSampleB1 (fun w => uniformFaceANonposMiddleHigh m s v w)

noncomputable def uniformFaceANonposMiddleHighB2
    (m s v : ℝ) : ℝ :=
  uniformCubicSampleB2 (fun w => uniformFaceANonposMiddleHigh m s v w)

noncomputable def uniformFaceANonposMiddleHighB3
    (m s v : ℝ) : ℝ :=
  uniformCubicSampleB3 (fun w => uniformFaceANonposMiddleHigh m s v w)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem uniformFaceANonposMiddleHigh_bernstein_w (m s v w : ℝ) :
    uniformFaceANonposMiddleHigh m s v w =
      cornerBern3 (uniformFaceANonposMiddleHighB0 m s v)
        (uniformFaceANonposMiddleHighB1 m s v)
        (uniformFaceANonposMiddleHighB2 m s v)
        (uniformFaceANonposMiddleHighB3 m s v) w := by
  unfold uniformFaceANonposMiddleHighB0 uniformFaceANonposMiddleHighB1
  unfold uniformFaceANonposMiddleHighB2 uniformFaceANonposMiddleHighB3
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposMiddleHigh cornerBern3
  simp_rw [uniformFaceANonposScaled_power]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformFaceANonposMiddleHighB0_bernstein_v
    (m s v : ℝ) :
    uniformFaceANonposMiddleHighB0 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleHighB0 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleHighB0 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleHighB0 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleHighB0 m s u)) v := by
  unfold uniformFaceANonposMiddleHighB0 uniformFaceANonposMiddleHigh
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposScaled uniformFaceANonposQ
  unfold uniformFaceACore cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposMiddleHighB0_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposMiddleHighB0 m s v := by
  rw [uniformFaceANonposMiddleHighB0_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    first
    | simp only [uniformCubicSampleB0]
    | simp only [uniformCubicSampleB1]
    | simp only [uniformCubicSampleB2]
    | simp only [uniformCubicSampleB3]
    unfold uniformFaceANonposMiddleHighB0 uniformFaceANonposMiddleHigh
    simp only [uniformCubicSampleB0]
    unfold uniformFaceANonposScaled uniformFaceANonposScale
    unfold uniformFaceANonposQ uniformFaceANonposT
    unfold uniformFaceANonposZ uniformFaceANonposP
    unfold uniformFaceACore
    field_simp
    ring_nf
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformFaceANonposMiddleHighB1_bernstein_v
    (m s v : ℝ) :
    uniformFaceANonposMiddleHighB1 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleHighB1 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleHighB1 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleHighB1 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleHighB1 m s u)) v := by
  unfold uniformFaceANonposMiddleHighB1 uniformFaceANonposMiddleHigh
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposScaled uniformFaceANonposQ
  unfold uniformFaceACore cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposMiddleHighB1_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposMiddleHighB1 m s v := by
  rw [uniformFaceANonposMiddleHighB1_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    first
    | simp only [uniformCubicSampleB0]
    | simp only [uniformCubicSampleB1]
    | simp only [uniformCubicSampleB2]
    | simp only [uniformCubicSampleB3]
    unfold uniformFaceANonposMiddleHighB1 uniformFaceANonposMiddleHigh
    simp only [uniformCubicSampleB1]
    unfold uniformFaceANonposScaled uniformFaceANonposScale
    unfold uniformFaceANonposQ uniformFaceANonposT
    unfold uniformFaceANonposZ uniformFaceANonposP
    unfold uniformFaceACore
    field_simp
    ring_nf
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformFaceANonposMiddleHighB2_bernstein_v
    (m s v : ℝ) :
    uniformFaceANonposMiddleHighB2 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleHighB2 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleHighB2 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleHighB2 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleHighB2 m s u)) v := by
  unfold uniformFaceANonposMiddleHighB2 uniformFaceANonposMiddleHigh
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposScaled uniformFaceANonposQ
  unfold uniformFaceACore cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposMiddleHighB2_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposMiddleHighB2 m s v := by
  rw [uniformFaceANonposMiddleHighB2_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    first
    | simp only [uniformCubicSampleB0]
    | simp only [uniformCubicSampleB1]
    | simp only [uniformCubicSampleB2]
    | simp only [uniformCubicSampleB3]
    unfold uniformFaceANonposMiddleHighB2 uniformFaceANonposMiddleHigh
    simp only [uniformCubicSampleB2]
    unfold uniformFaceANonposScaled uniformFaceANonposScale
    unfold uniformFaceANonposQ uniformFaceANonposT
    unfold uniformFaceANonposZ uniformFaceANonposP
    unfold uniformFaceACore
    field_simp
    ring_nf
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformFaceANonposMiddleHighB3_bernstein_v
    (m s v : ℝ) :
    uniformFaceANonposMiddleHighB3 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleHighB3 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleHighB3 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleHighB3 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleHighB3 m s u)) v := by
  unfold uniformFaceANonposMiddleHighB3 uniformFaceANonposMiddleHigh
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposScaled uniformFaceANonposQ
  unfold uniformFaceACore cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposMiddleHighB3_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposMiddleHighB3 m s v := by
  rw [uniformFaceANonposMiddleHighB3_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    first
    | simp only [uniformCubicSampleB0]
    | simp only [uniformCubicSampleB1]
    | simp only [uniformCubicSampleB2]
    | simp only [uniformCubicSampleB3]
    unfold uniformFaceANonposMiddleHighB3 uniformFaceANonposMiddleHigh
    simp only [uniformCubicSampleB3]
    unfold uniformFaceANonposScaled uniformFaceANonposScale
    unfold uniformFaceANonposQ uniformFaceANonposT
    unfold uniformFaceANonposZ uniformFaceANonposP
    unfold uniformFaceACore
    field_simp
    ring_nf
    positivity

theorem uniformFaceANonposMiddleHigh_nonneg
    (m s v w : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    0 ≤ uniformFaceANonposMiddleHigh m s v w := by
  rw [uniformFaceANonposMiddleHigh_bernstein_w]
  exact cornerBern3_nonneg _ _ _ _ _
    (uniformFaceANonposMiddleHighB0_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposMiddleHighB1_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposMiddleHighB2_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposMiddleHighB3_nonneg m s v hm hs hv hv1)
    hw hw1

/-- Nonnegativity on the second middle interval
`m² + 39 ≤ X ≤ P(m)/8`. -/
theorem uniformFaceANonposScaled_nonneg_of_middle_high
    (m s v X : ℝ) (hm : 0 < m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hXlower : m^2 + 39 ≤ X)
    (hXupper : X ≤ uniformFaceANonposP m / 8) :
    0 ≤ uniformFaceANonposScaled m s v X := by
  let L := m^2 + 39
  let R := uniformFaceANonposP m / 8
  let w := (X - L) / (R - L)
  have hwidth : 0 < R - L := by
    dsimp [R, L]
    unfold uniformFaceANonposP
    have hm0 : 0 ≤ m := hm.le
    have hpoly : 0 < 2*m^2 + 27*m + 191 := by positivity
    nlinarith [mul_pos hm hpoly]
  have hw : 0 ≤ w := by
    dsimp [w]
    exact div_nonneg (sub_nonneg.mpr hXlower) hwidth.le
  have hw1 : w ≤ 1 := by
    dsimp [w]
    rw [div_le_one hwidth]
    dsimp [R, L] at hXupper ⊢
    linarith
  have hXid : L + w * (R - L) = X := by
    dsimp [w]
    field_simp [hwidth.ne']
    ring
  have hcert := uniformFaceANonposMiddleHigh_nonneg
    m s v w hm.le hs hv hv1 hw hw1
  unfold uniformFaceANonposMiddleHigh at hcert
  change 0 ≤ uniformFaceANonposScaled m s v
    (L + w * (R - L)) at hcert
  rwa [hXid] at hcert

/-- The compact, lower-middle, upper-middle, and far-tail certificates cover
the entire nonnegative `X` axis. -/
theorem uniformFaceANonposScaled_nonneg
    (m s v X : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) (hX : 0 ≤ X) :
    0 ≤ uniformFaceANonposScaled m s v X := by
  by_cases hX1 : X ≤ 1
  · exact uniformFaceANonposScaled_nonneg_of_X_le_one
      m s v X hm hs hv hv1 hX hX1
  by_cases hXmid : X ≤ m^2 + 39
  · exact uniformFaceANonposScaled_nonneg_of_middle_low
      m s v X hm hs hv hv1 (by linarith) hXmid
  by_cases hXtail : uniformFaceANonposP m / 8 ≤ X
  · exact uniformFaceANonposScaled_nonneg_of_large_X
      m s v X hm hs hv hv1 hXtail
  have hmpos : 0 < m := by
    by_contra hmnot
    have hmzero : m = 0 := le_antisymm (le_of_not_gt hmnot) hm
    subst m
    unfold uniformFaceANonposP at hXtail
    norm_num at hXmid hXtail
    linarith
  exact uniformFaceANonposScaled_nonneg_of_middle_high
    m s v X hmpos hs hv hv1 (by linarith) (le_of_not_ge hXtail)

/-- The nonpositive-current-slope return-face core is nonnegative without any
remaining range restriction on its face coordinate. -/
theorem uniformFaceACore_nonneg_of_currentM_nonpos_complete
    (n X T q : ℝ) (hn : 4 ≤ n) (hX : 0 ≤ X)
    (hT1 : n - 1 ≤ T) (hq : 0 < q)
    (hM : uniformFaceACurrentM n T q ≤ 0) :
    0 ≤ uniformFaceACore n X T q := by
  apply uniformFaceACore_nonneg_of_currentM_nonpos n X T q hn hX hT1 hq hM
  intro m s v R hm hs hv hv1 hR
  exact uniformFaceANonposScaled_nonneg m s v R hm hs hv hv1 hR

/-- Complete normalized return-face certificate in the branch where the
current return slope is nonpositive. -/
theorem uniformSharpFaceA_nonneg_of_currentM_nonpos_complete
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hT1 : n - 1 ≤ T) (hY : 0 < Y)
    (hq : 0 < q) (hM : uniformFaceACurrentM n T q ≤ 0) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  apply uniformSharpFaceA_nonneg_of_currentM_nonpos
    n a T Y q hn ha hT hT1 hY hq hM
  intro m s v X hm hs hv hv1 hX
  exact uniformFaceANonposScaled_nonneg m s v X hm hs hv hv1 hX

end SSP.K3AllStages
