import SSPLean.K3AllStagesTail

/-!
# The lower-middle return-face certificate for `k = 3`

This covers `1 ≤ X ≤ m² + 39` in the nonpositive-current-slope
parameterization.  The transformed polynomial is bicubic in the interval
coordinate and the terminal mixture coordinate.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

noncomputable def uniformFaceANonposMiddleLow
    (m s v w : ℝ) : ℝ :=
  uniformFaceANonposScaled m s v (1 + w * (m^2 + 38))

noncomputable def uniformFaceANonposMiddleLowB0
    (m s v : ℝ) : ℝ :=
  uniformCubicSampleB0 (fun w => uniformFaceANonposMiddleLow m s v w)

noncomputable def uniformFaceANonposMiddleLowB1
    (m s v : ℝ) : ℝ :=
  uniformCubicSampleB1 (fun w => uniformFaceANonposMiddleLow m s v w)

noncomputable def uniformFaceANonposMiddleLowB2
    (m s v : ℝ) : ℝ :=
  uniformCubicSampleB2 (fun w => uniformFaceANonposMiddleLow m s v w)

noncomputable def uniformFaceANonposMiddleLowB3
    (m s v : ℝ) : ℝ :=
  uniformCubicSampleB3 (fun w => uniformFaceANonposMiddleLow m s v w)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem uniformFaceANonposMiddleLow_bernstein_w (m s v w : ℝ) :
    uniformFaceANonposMiddleLow m s v w =
      cornerBern3 (uniformFaceANonposMiddleLowB0 m s v)
        (uniformFaceANonposMiddleLowB1 m s v)
        (uniformFaceANonposMiddleLowB2 m s v)
        (uniformFaceANonposMiddleLowB3 m s v) w := by
  unfold uniformFaceANonposMiddleLowB0 uniformFaceANonposMiddleLowB1
  unfold uniformFaceANonposMiddleLowB2 uniformFaceANonposMiddleLowB3
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposMiddleLow cornerBern3
  simp_rw [uniformFaceANonposScaled_power]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem uniformFaceANonposMiddleLowB0_bernstein_v
    (m s v : ℝ) :
    uniformFaceANonposMiddleLowB0 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleLowB0 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleLowB0 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleLowB0 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleLowB0 m s u)) v := by
  unfold uniformFaceANonposMiddleLowB0 uniformFaceANonposMiddleLow
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposScaled uniformFaceANonposQ
  unfold uniformFaceACore cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposMiddleLowB0_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposMiddleLowB0 m s v := by
  rw [uniformFaceANonposMiddleLowB0_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    first
    | simp only [uniformCubicSampleB0]
    | simp only [uniformCubicSampleB1]
    | simp only [uniformCubicSampleB2]
    | simp only [uniformCubicSampleB3]
    unfold uniformFaceANonposMiddleLowB0 uniformFaceANonposMiddleLow
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
private theorem uniformFaceANonposMiddleLowB1_bernstein_v
    (m s v : ℝ) :
    uniformFaceANonposMiddleLowB1 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleLowB1 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleLowB1 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleLowB1 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleLowB1 m s u)) v := by
  unfold uniformFaceANonposMiddleLowB1 uniformFaceANonposMiddleLow
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposScaled uniformFaceANonposQ
  unfold uniformFaceACore cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposMiddleLowB1_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposMiddleLowB1 m s v := by
  rw [uniformFaceANonposMiddleLowB1_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    first
    | simp only [uniformCubicSampleB0]
    | simp only [uniformCubicSampleB1]
    | simp only [uniformCubicSampleB2]
    | simp only [uniformCubicSampleB3]
    unfold uniformFaceANonposMiddleLowB1 uniformFaceANonposMiddleLow
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
private theorem uniformFaceANonposMiddleLowB2_bernstein_v
    (m s v : ℝ) :
    uniformFaceANonposMiddleLowB2 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleLowB2 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleLowB2 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleLowB2 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleLowB2 m s u)) v := by
  unfold uniformFaceANonposMiddleLowB2 uniformFaceANonposMiddleLow
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposScaled uniformFaceANonposQ
  unfold uniformFaceACore cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposMiddleLowB2_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposMiddleLowB2 m s v := by
  rw [uniformFaceANonposMiddleLowB2_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    first
    | simp only [uniformCubicSampleB0]
    | simp only [uniformCubicSampleB1]
    | simp only [uniformCubicSampleB2]
    | simp only [uniformCubicSampleB3]
    unfold uniformFaceANonposMiddleLowB2 uniformFaceANonposMiddleLow
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
private theorem uniformFaceANonposMiddleLowB3_bernstein_v
    (m s v : ℝ) :
    uniformFaceANonposMiddleLowB3 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleLowB3 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleLowB3 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleLowB3 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleLowB3 m s u)) v := by
  unfold uniformFaceANonposMiddleLowB3 uniformFaceANonposMiddleLow
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposScaled uniformFaceANonposQ
  unfold uniformFaceACore cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem uniformFaceANonposMiddleLowB3_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposMiddleLowB3 m s v := by
  rw [uniformFaceANonposMiddleLowB3_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    first
    | simp only [uniformCubicSampleB0]
    | simp only [uniformCubicSampleB1]
    | simp only [uniformCubicSampleB2]
    | simp only [uniformCubicSampleB3]
    unfold uniformFaceANonposMiddleLowB3 uniformFaceANonposMiddleLow
    simp only [uniformCubicSampleB3]
    unfold uniformFaceANonposScaled uniformFaceANonposScale
    unfold uniformFaceANonposQ uniformFaceANonposT
    unfold uniformFaceANonposZ uniformFaceANonposP
    unfold uniformFaceACore
    field_simp
    ring_nf
    positivity

theorem uniformFaceANonposMiddleLow_nonneg
    (m s v w : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    0 ≤ uniformFaceANonposMiddleLow m s v w := by
  rw [uniformFaceANonposMiddleLow_bernstein_w]
  exact cornerBern3_nonneg _ _ _ _ _
    (uniformFaceANonposMiddleLowB0_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposMiddleLowB1_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposMiddleLowB2_nonneg m s v hm hs hv hv1)
    (uniformFaceANonposMiddleLowB3_nonneg m s v hm hs hv hv1)
    hw hw1

/-- Nonnegativity on the first middle interval `1 ≤ X ≤ m² + 39`. -/
theorem uniformFaceANonposScaled_nonneg_of_middle_low
    (m s v X : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hX1 : 1 ≤ X) (hXupper : X ≤ m^2 + 39) :
    0 ≤ uniformFaceANonposScaled m s v X := by
  let w := (X - 1) / (m^2 + 38)
  have hden : 0 < m^2 + 38 := by positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : w ≤ 1 := by
    dsimp [w]
    rw [div_le_one hden]
    linarith
  have hXid : 1 + w * (m^2 + 38) = X := by
    dsimp [w]
    field_simp [hden.ne']
    ring
  have hcert := uniformFaceANonposMiddleLow_nonneg
    m s v w hm hs hv hv1 hw hw1
  unfold uniformFaceANonposMiddleLow at hcert
  rwa [hXid] at hcert

end SSP.K3AllStages
