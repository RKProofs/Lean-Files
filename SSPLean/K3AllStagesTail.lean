import SSPLean.K3AllStagesTailCertificate

/-!
# The far-tail certificate for the uniform `k = 3` return face

This file is kept separate from `K3AllStages` so that the large base module is
serialized before the remaining coefficient certificate is elaborated.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

/-- The weakened derivative certificate used at the start of the far tail. -/
noncomputable def uniformFaceANonposTailSlope (m s v : ℝ) : ℝ :=
  uniformFaceANonposXC1 m s v
    + (uniformFaceANonposP m / 8) * uniformFaceANonposXC2 m s v

noncomputable def uniformFaceANonposTailSlopeB0 (m s : ℝ) : ℝ :=
  uniformCubicSampleB0 (fun v => uniformFaceANonposTailSlope m s v)

noncomputable def uniformFaceANonposTailSlopeB1 (m s : ℝ) : ℝ :=
  uniformCubicSampleB1 (fun v => uniformFaceANonposTailSlope m s v)

noncomputable def uniformFaceANonposTailSlopeB2 (m s : ℝ) : ℝ :=
  uniformCubicSampleB2 (fun v => uniformFaceANonposTailSlope m s v)

noncomputable def uniformFaceANonposTailSlopeB3 (m s : ℝ) : ℝ :=
  uniformCubicSampleB3 (fun v => uniformFaceANonposTailSlope m s v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem uniformFaceANonposTailSlope_bernstein_v (m s v : ℝ) :
    uniformFaceANonposTailSlope m s v =
      cornerBern3 (uniformFaceANonposTailSlopeB0 m s)
        (uniformFaceANonposTailSlopeB1 m s)
        (uniformFaceANonposTailSlopeB2 m s)
        (uniformFaceANonposTailSlopeB3 m s) v := by
  unfold uniformFaceANonposTailSlopeB0 uniformFaceANonposTailSlopeB1
  unfold uniformFaceANonposTailSlopeB2 uniformFaceANonposTailSlopeB3
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposTailSlope
  unfold uniformFaceANonposXC1 uniformFaceANonposXC2
  unfold uniformFaceACoreXC1 uniformFaceACoreXC2
  simp_rw [uniformFaceACore_bernstein_q]
  unfold uniformFaceANonposQ cornerBern3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceANonposTailSlopeB0_nonneg
    (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ uniformFaceANonposTailSlopeB0 m s := by
  have heq : uniformFaceANonposTailSlopeB0 m s = TailCompactB0 m s := by
    unfold uniformFaceANonposTailSlopeB0 uniformCubicSampleB0
    unfold uniformFaceANonposTailSlope
    simp only [TailCompact_identity m s _ hm hs]
    unfold cornerBern3
    ring
  rw [heq]
  exact TailCompactB0_nonneg m s hm hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceANonposTailSlopeB1_nonneg
    (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ uniformFaceANonposTailSlopeB1 m s := by
  have heq : uniformFaceANonposTailSlopeB1 m s = TailCompactB1 m s := by
    unfold uniformFaceANonposTailSlopeB1 uniformCubicSampleB1
    unfold uniformFaceANonposTailSlope
    simp only [TailCompact_identity m s _ hm hs]
    unfold cornerBern3
    ring
  rw [heq]
  exact TailCompactB1_nonneg m s hm hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceANonposTailSlopeB2_nonneg
    (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ uniformFaceANonposTailSlopeB2 m s := by
  have heq : uniformFaceANonposTailSlopeB2 m s = TailCompactB2 m s := by
    unfold uniformFaceANonposTailSlopeB2 uniformCubicSampleB2
    unfold uniformFaceANonposTailSlope
    simp only [TailCompact_identity m s _ hm hs]
    unfold cornerBern3
    ring
  rw [heq]
  exact TailCompactB2_nonneg m s hm hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceANonposTailSlopeB3_nonneg
    (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ uniformFaceANonposTailSlopeB3 m s := by
  have heq : uniformFaceANonposTailSlopeB3 m s = TailCompactB3 m s := by
    unfold uniformFaceANonposTailSlopeB3 uniformCubicSampleB3
    unfold uniformFaceANonposTailSlope
    simp only [TailCompact_identity m s _ hm hs]
    unfold cornerBern3
    ring
  rw [heq]
  exact TailCompactB3_nonneg m s hm hs

/-- The far-tail slope condition follows from a cubic Bernstein certificate in
the normalized terminal weight. -/
theorem uniformFaceANonposTailSlope_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposTailSlope m s v := by
  rw [uniformFaceANonposTailSlope_bernstein_v]
  exact cornerBern3_nonneg _ _ _ _ _
    (uniformFaceANonposTailSlopeB0_nonneg m s hm hs)
    (uniformFaceANonposTailSlopeB1_nonneg m s hm hs)
    (uniformFaceANonposTailSlopeB2_nonneg m s hm hs)
    (uniformFaceANonposTailSlopeB3_nonneg m s hm hs)
    hv hv1

/-- Unconditional nonnegativity of the return-face cubic on the far tail
`X ≥ P(m)/8`. -/
theorem uniformFaceANonposScaled_nonneg_of_large_X
    (m s v X : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hPX : uniformFaceANonposP m / 8 ≤ X) :
    0 ≤ uniformFaceANonposScaled m s v X := by
  apply uniformFaceANonposScaled_nonneg_of_tailSlope
    m s v X hm hs hv hv1 hPX
  exact uniformFaceANonposTailSlope_nonneg m s v hm hs hv hv1

/-- Restore the original return-face core in the nonpositive-current-slope
branch when its face coordinate is in the certified far tail. -/
theorem uniformFaceACore_nonneg_of_currentM_nonpos_of_X_ge_tail
    (n X T q : ℝ) (hn : 4 ≤ n)
    (hT1 : n - 1 ≤ T) (hq : 0 < q)
    (hM : uniformFaceACurrentM n T q ≤ 0)
    (hXtail : uniformFaceANonposP (n - 4) / 8 ≤ X) :
    0 ≤ uniformFaceACore n X T q := by
  let m := n - 4
  let z := T - (n - 1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hnid : m + 4 = n := by dsimp [m]; ring
  have hTid : m + 3 + z = T := by dsimp [m, z]; ring
  have hM' : uniformFaceACurrentM (m + 4) (m + 3 + z) q ≤ 0 := by
    simpa only [hnid, hTid] using hM
  obtain ⟨s, v, hs, hv, hv1, hzid, hqid⟩ :=
    uniformFaceACurrentM_nonpos_parameterization m z q hm hz hq hM'
  have hTs : uniformFaceANonposT m s = T := by
    rw [← hTid, hzid]
    rfl
  have htail : uniformFaceANonposP m / 8 ≤ X := by
    simpa only [m] using hXtail
  have hscaled := uniformFaceANonposScaled_nonneg_of_large_X
    m s v X hm hs hv hv1 htail
  unfold uniformFaceANonposScaled at hscaled
  rw [hnid, hTs, ← hqid] at hscaled
  have hscale := uniformFaceANonposScale_pos m hm
  exact (mul_nonneg_iff_of_pos_left hscale).mp hscaled

/-- The normalized return-face discriminant is therefore unconditional in
the far-tail part of the nonpositive-current-slope branch. -/
theorem uniformSharpFaceA_nonneg_of_currentM_nonpos_of_mul_ge_tail
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 0 < T) (hT1 : n - 1 ≤ T) (hY : 0 < Y)
    (hq : 0 < q) (hM : uniformFaceACurrentM n T q ≤ 0)
    (haYtail : uniformFaceANonposP (n - 4) / 8 ≤ a * Y) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  have hcore := uniformFaceACore_nonneg_of_currentM_nonpos_of_X_ge_tail
    n (a * Y) T q hn hT1 hq hM haYtail
  have hnum := uniformFaceANum_nonneg_of_core
    n a T Y q hn ha.le hT.le hY.le hq.le hcore
  exact uniformSharpFaceA_nonneg_of_num n a T Y q hn ha hT hY hq hnum

end SSP.K3AllStages
