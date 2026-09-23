import SSPLean.K3AllStagesPositiveSlopeSmall

/-!
# The low-`z` positive-slope chart

This file proves the remaining compact `z` chart.  The `q = 1` endpoint is
split once in its compact parameter: near zero its linear coefficient is
nonnegative, while on the complementary interval its quadratic part has
nonpositive discriminant.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

noncomputable def uniformFaceAPositiveLowQOneC1Small (m r : ℝ) : ℝ :=
  uniformFaceACoreXC1 (m + 4)
    (m + 3 + uniformFaceAPositiveLowZ m (r / 41)) 1

noncomputable def uniformFaceAPositiveLowQOneC1SmallB0 (m : ℝ) : ℝ :=
  (m + 3)^4 * (m + 4)^2 * (m + 5) * (m + 6) * (2*m + 9)

noncomputable def uniformFaceAPositiveLowQOneC1SmallB1 (m : ℝ) : ℝ :=
  (m + 3)^4 * (m + 4) * (m + 5) *
    (6*m^4 + 277*m^3 + 3055*m^2 + 12494*m + 17088) / 82

noncomputable def uniformFaceAPositiveLowQOneC1SmallB2 (m : ℝ) : ℝ :=
  2 * (m + 3)^4 * (m + 4) *
    (6*m^7 + 565*m^6 + 18411*m^5 + 268320*m^4 + 2022073*m^3
      + 8187162*m^2 + 16784856*m + 13479112) / (5043 * (m + 6))

noncomputable def uniformFaceAPositiveLowQOneC1SmallB3 (m : ℝ) : ℝ :=
  (m + 3)^4 * (m + 4) *
    (4*m^10 + 658*m^9 + 39276*m^8 + 1167848*m^7 + 19637742*m^6
      + 200826449*m^5 + 1291223443*m^4 + 5211699396*m^3
      + 12658526880*m^2 + 16523682168*m + 8487948416) /
    (68921 * (m + 6)^3)

noncomputable def uniformFaceAPositiveLowQOneC1SmallB4 (m : ℝ) : ℝ :=
  8 * (m + 3)^4 * (m + 4) *
    (64*m^11 + 7672*m^10 + 383614*m^9 + 10508754*m^8
      + 175318083*m^7 + 1880199378*m^6 + 13269258852*m^5
      + 61418879034*m^4 + 179813162764*m^3 + 302672139018*m^2
      + 224360249084*m + 2354378928) / (2825761 * (m + 6)^4)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem uniformFaceAPositiveLowQOneC1Small_bernstein
    (m r : ℝ) (hm : 0 ≤ m) :
    uniformFaceAPositiveLowQOneC1Small m r =
      cornerBern4 (uniformFaceAPositiveLowQOneC1SmallB0 m)
        (uniformFaceAPositiveLowQOneC1SmallB1 m)
        (uniformFaceAPositiveLowQOneC1SmallB2 m)
        (uniformFaceAPositiveLowQOneC1SmallB3 m)
        (uniformFaceAPositiveLowQOneC1SmallB4 m) r := by
  unfold uniformFaceAPositiveLowQOneC1SmallB0
  unfold uniformFaceAPositiveLowQOneC1SmallB1
  unfold uniformFaceAPositiveLowQOneC1SmallB2
  unfold uniformFaceAPositiveLowQOneC1SmallB3
  unfold uniformFaceAPositiveLowQOneC1SmallB4
  unfold uniformFaceAPositiveLowQOneC1Small
  unfold uniformFaceAPositiveLowZ uniformFaceACoreXC1
  unfold uniformFaceANonposP uniformFaceACore cornerBern4
  field_simp [show m + 6 ≠ 0 by positivity]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem uniformFaceAPositiveLowQOneC1Small_coefficients_nonneg
    (m : ℝ) (hm : 0 ≤ m) :
    0 ≤ uniformFaceAPositiveLowQOneC1SmallB0 m ∧
    0 ≤ uniformFaceAPositiveLowQOneC1SmallB1 m ∧
    0 ≤ uniformFaceAPositiveLowQOneC1SmallB2 m ∧
    0 ≤ uniformFaceAPositiveLowQOneC1SmallB3 m ∧
    0 ≤ uniformFaceAPositiveLowQOneC1SmallB4 m := by
  unfold uniformFaceAPositiveLowQOneC1SmallB0
  unfold uniformFaceAPositiveLowQOneC1SmallB1
  unfold uniformFaceAPositiveLowQOneC1SmallB2
  unfold uniformFaceAPositiveLowQOneC1SmallB3
  unfold uniformFaceAPositiveLowQOneC1SmallB4
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

theorem uniformFaceAPositiveLow_qOne_C1_nonneg_of_small
    (m u : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u) (huSmall : u ≤ 1 / 41) :
    0 ≤ uniformFaceACoreXC1 (m + 4)
      (m + 3 + uniformFaceAPositiveLowZ m u) 1 := by
  let r := 41*u
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; nlinarith
  have hid : u = r/41 := by dsimp [r]; ring
  rw [hid]
  change 0 ≤ uniformFaceAPositiveLowQOneC1Small m r
  rw [uniformFaceAPositiveLowQOneC1Small_bernstein m r hm]
  obtain ⟨h0, h1, h2, h3, h4⟩ :=
    uniformFaceAPositiveLowQOneC1Small_coefficients_nonneg m hm
  exact cornerBern4_nonneg _ _ _ _ _ r h0 h1 h2 h3 h4 hr hr1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceAPositiveLow_qOne_C0_nonneg
    (m u : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u) :
    0 ≤ uniformFaceACoreXC0 (m + 4)
      (m + 3 + uniformFaceAPositiveLowZ m u) 1 := by
  unfold uniformFaceACoreXC0 uniformFaceAPositiveLowZ
  unfold uniformFaceANonposP uniformFaceACore
  field_simp [show m + 6 ≠ 0 by positivity]
  ring_nf
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceAPositiveLow_qOne_C2_pos
    (m u : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u) :
    0 < uniformFaceACoreXC2 (m + 4)
      (m + 3 + uniformFaceAPositiveLowZ m u) 1 := by
  unfold uniformFaceACoreXC2 uniformFaceAPositiveLowZ
  unfold uniformFaceANonposP uniformFaceACore
  field_simp [show m + 6 ≠ 0 by positivity]
  ring_nf
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceAPositiveLow_qOne_C3_nonneg
    (m u : ℝ) (hm : 0 ≤ m) :
    0 ≤ uniformFaceACoreXC3 (m + 4)
      (m + 3 + uniformFaceAPositiveLowZ m u) 1 := by
  unfold uniformFaceACoreXC3 uniformFaceAPositiveLowZ
  unfold uniformFaceANonposP uniformFaceACore
  field_simp [show m + 6 ≠ 0 by positivity]
  ring_nf
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem uniformFaceAPositiveLow_qOne_discriminant_of_large
    (m u : ℝ) (hm : 0 ≤ m) (huLarge : 1 / 41 ≤ u) :
    (uniformFaceACoreXC1 (m + 4)
        (m + 3 + uniformFaceAPositiveLowZ m u) 1)^2 ≤
      4 * uniformFaceACoreXC2 (m + 4)
          (m + 3 + uniformFaceAPositiveLowZ m u) 1 *
        uniformFaceACoreXC0 (m + 4)
          (m + 3 + uniformFaceAPositiveLowZ m u) 1 := by
  let r := 41*u-1
  have hr : 0 ≤ r := by dsimp [r]; nlinarith
  have hid : u = (r+1)/41 := by dsimp [r]; ring
  rw [hid, ← sub_nonneg]
  unfold uniformFaceACoreXC0 uniformFaceACoreXC1
  unfold uniformFaceACoreXC2 uniformFaceAPositiveLowZ
  unfold uniformFaceANonposP uniformFaceACore
  field_simp [show m + 6 ≠ 0 by positivity]
  ring_nf
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceAPositiveLow_qOne_nonneg
    (m u X : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u) (_hu1 : u ≤ 1)
    (hX : 0 ≤ X) :
    0 ≤ uniformFaceACore (m + 4) X
      (m + 3 + uniformFaceAPositiveLowZ m u) 1 := by
  let C0 := uniformFaceACoreXC0 (m + 4)
    (m + 3 + uniformFaceAPositiveLowZ m u) 1
  let C1 := uniformFaceACoreXC1 (m + 4)
    (m + 3 + uniformFaceAPositiveLowZ m u) 1
  let C2 := uniformFaceACoreXC2 (m + 4)
    (m + 3 + uniformFaceAPositiveLowZ m u) 1
  let C3 := uniformFaceACoreXC3 (m + 4)
    (m + 3 + uniformFaceAPositiveLowZ m u) 1
  have h0 : 0 ≤ C0 := by
    dsimp [C0]
    exact uniformFaceAPositiveLow_qOne_C0_nonneg m u hm hu
  have h2 : 0 < C2 := by
    dsimp [C2]
    exact uniformFaceAPositiveLow_qOne_C2_pos m u hm hu
  have h3 : 0 ≤ C3 := by
    dsimp [C3]
    exact uniformFaceAPositiveLow_qOne_C3_nonneg m u hm
  have hcore :
      uniformFaceACore (m + 4) X
          (m + 3 + uniformFaceAPositiveLowZ m u) 1 =
        C2*X^2 + C1*X + C0 + C3*X^3 := by
    dsimp [C0, C1, C2, C3]
    unfold uniformFaceACoreXC0 uniformFaceACoreXC1
    unfold uniformFaceACoreXC2 uniformFaceACoreXC3 uniformFaceACore
    ring
  rw [hcore]
  by_cases huSmall : u ≤ 1/41
  · have h1 : 0 ≤ C1 := by
      dsimp [C1]
      exact uniformFaceAPositiveLow_qOne_C1_nonneg_of_small
        m u hm hu huSmall
    positivity
  · have hdisc : C1^2 ≤ 4*C2*C0 := by
      dsimp [C0, C1, C2]
      exact uniformFaceAPositiveLow_qOne_discriminant_of_large
        m u hm (le_of_not_ge huSmall)
    have hquad : 0 ≤ C2*X^2 + C1*X + C0 := by
      have hid :
          4*C2*(C2*X^2 + C1*X + C0) =
            (2*C2*X + C1)^2 + (4*C2*C0 - C1^2) := by ring
      apply (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*C2)).mp
      rw [hid]
      nlinarith [sq_nonneg (2*C2*X + C1)]
    positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
/-- The entire low-`z` chart is nonnegative.  The active-gradient premise
used by the final assembly is therefore unnecessary on this chart. -/
theorem uniformFaceAPositiveLow_nonneg
    (m u q w : ℝ)
    (hm : 0 ≤ m) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1) (hw : 0 ≤ w) (_hw1 : w ≤ 1) :
    0 ≤ uniformFaceACurrentPoly (m + 4)
      (m + 3 + uniformFaceAPositiveLowZ m u) q w := by
  let n := m + 4
  let T := m + 3 + uniformFaceAPositiveLowZ m u
  let M := uniformFaceACurrentM n T q
  let K := uniformFaceACurrentK n T q
  let X := w*K/(n*M)
  have hn : 4 ≤ n := by dsimp [n]; linarith
  have hnpos : 0 < n := by linarith
  have hz : 0 ≤ uniformFaceAPositiveLowZ m u := by
    unfold uniformFaceAPositiveLowZ
    have hP := uniformFaceANonposP_pos m hm
    positivity
  have hT : 0 < T := by dsimp [T]; linarith
  have hTge : n - 1 ≤ T := by dsimp [n, T]; linarith
  have hM0 : 0 ≤ uniformFaceACurrentM n T 0 := by
    dsimp [n, T]
    rw [uniformFaceACurrentM_zero_shift]
    unfold uniformFaceAPositiveLowZ
    have hm6 : 0 < m + 6 := by linarith
    have hid :
        2*m^3 + 35*m^2 + 191*m + 312 -
            (m+6) * (uniformFaceANonposP m / (m+6) * u) =
          uniformFaceANonposP m * (1-u) := by
      unfold uniformFaceANonposP
      field_simp [hm6.ne']
    rw [hid]
    have hP := uniformFaceANonposP_pos m hm
    positivity
  have hM1 : 0 < uniformFaceACurrentM n T 1 :=
    uniformFaceACurrentM_at_one_pos n T hn hTge
  have hM : 0 < M := by
    dsimp [M]
    rw [uniformFaceACurrentM_affine]
    have hq0 : 0 ≤ 1-q := by linarith
    have hleft : 0 ≤ (1-q)*uniformFaceACurrentM n T 0 :=
      mul_nonneg hq0 hM0
    have hright : 0 < q*uniformFaceACurrentM n T 1 :=
      mul_pos hq hM1
    linarith
  have hK : 0 < K := by
    dsimp [K]
    exact uniformFaceACurrentK_pos n T q hn hTge hq.le hq1
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have h3 : 0 ≤ uniformFaceAQB3 n X T := by
    unfold uniformFaceAQB3
    dsimp [n, T] at X ⊢
    exact uniformFaceAPositiveLow_qOne_nonneg m u X hm hu hu1 hX
  have hcore : 0 ≤ uniformFaceACore n X T q :=
    uniformFaceACore_nonneg_of_q_bernstein n X T q hn hX hq.le hq1
      (uniformFaceAQB1_nonneg n X T hn hX hT.le)
      (uniformFaceAQB2_nonneg n X T hn hX hT.le) h3
  rw [← uniformFaceACurrentScaled_eq_poly n T q w hnpos.ne' hM.ne']
  unfold uniformFaceACurrentScaled
  change 0 ≤ n^3 * M^3 * uniformFaceACore n X T q
  positivity

end SSP.K3AllStages
