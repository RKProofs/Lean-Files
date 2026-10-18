import SSPLean.K3AllStagesPositiveSlopeLargeB1T1
import SSPLean.K3AllStagesPositiveSlopeLargeB1C2
set_option autoImplicit false
namespace SSP.K3AllStages

private theorem LargeB1CurrentK_affine (n T q t : ℝ) :
    uniformFaceACurrentK n T (q + t*(1-q)) =
      uniformFaceACurrentK n T q + t*(uniformFaceACurrentK n T 1 - uniformFaceACurrentK n T q) := by
  unfold uniformFaceACurrentK uniformReturnK
  ring

private noncomputable def uniformFaceAPositiveHighVWLargeB1T2Compact (m s : ℝ) : ℝ :=
  let n := m + 4
  let T := uniformFaceANonposT m s
  let L := uniformFaceACurrentM n T 1
  let K₀ := uniformFaceACurrentK n T (uniformFaceAPositiveQ0 m s)
  let H := uniformFaceACurrentK n T 1 - K₀
  let A := n^3 * L^3 * uniformFaceACoreXC0 n T 1
  let B := n^2 * L^2 * uniformFaceACoreXC1 n T 1
  let C := n * L * uniformFaceACoreXC2 n T 1
  let D := uniformFaceACoreXC3 n T 1
  K₀^3 * D + (5/6) * K₀^2 * (C + H*D)
    + (2/3) * K₀ * (B + (2/3)*H*C) + (1/2) * (A + (1/3)*H*B)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem uniformFaceAPositiveHighVWLargeB1T2_eq_compact (m s : ℝ) :
    uniformFaceAPositiveHighVWLargeB1T2 m s = uniformFaceAPositiveHighVWLargeB1T2Compact m s := by
  unfold uniformFaceAPositiveHighVWLargeB1T2 uniformCubicSampleB2
  unfold uniformFaceAPositiveHighVWLargeB1R
  unfold uniformFaceAPositiveHighVWLargeB1 uniformCubicSampleB1
  unfold uniformFaceAPositiveHighVWLargeEndpoint
  unfold uniformFaceAPositiveHighVWLargeB1T2Compact uniformFaceAPositiveQ
  simp only [LargeB1CurrentK_affine]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformFaceAPositiveHighVWLargeB1T2_reduced (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceAPositiveHighVWLargeB1T2 m s =
      (m+4)^3 * LargeB1Positive2 m s /
        (18*(m+6)^8*((m+3)*(m+7)*(m+8))^3) := by
  rw [uniformFaceAPositiveHighVWLargeB1T2_eq_compact]
  unfold uniformFaceAPositiveHighVWLargeB1T2Compact
  dsimp only
  rw [uniformFaceACoreXC0_at_one, uniformFaceACoreXC1_at_one,
    uniformFaceACoreXC2_at_one, uniformFaceACoreXC3_at_one]
  rw [LargeL_eq m s hm hs, LargeK0_eq m s hm hs, LargeK1_eq m s hm hs]
  rw [LargeX0_eq m s hm, LargeX1_eq m s hm, LargeX2_eq m s hm, LargeX3_eq m s hm]
  rw [LargeX0_factor, LargeX1_factor, LargeX2_factor, LargeX3_factor,
    LargeH_factor m s hm, ← LargeB1Positive2_identity]
  have ha : m+6 ≠ 0 := by linarith
  have hb : m+3 ≠ 0 := by linarith
  have hc : m+7 ≠ 0 := by linarith
  have hd : m+8 ≠ 0 := by linarith
  field_simp [ha,hb,hc,hd]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformFaceAPositiveHighVWLargeB1T2_nonneg (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ uniformFaceAPositiveHighVWLargeB1T2 m s := by
  rw [uniformFaceAPositiveHighVWLargeB1T2_reduced m s hm hs]
  have h := LargeB1Positive2_nonneg m s hm hs
  positivity
end SSP.K3AllStages
