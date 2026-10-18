import SSPLean.K3AllStagesPositiveSlopeLargeB2T0
import SSPLean.K3AllStagesPositiveSlopeLargeB2C1
set_option autoImplicit false
namespace SSP.K3AllStages

private theorem LargeB2CurrentK_affine (n T q t : ℝ) :
    uniformFaceACurrentK n T (q + t*(1-q)) =
      uniformFaceACurrentK n T q + t*(uniformFaceACurrentK n T 1 - uniformFaceACurrentK n T q) := by
  unfold uniformFaceACurrentK uniformReturnK
  ring

private noncomputable def uniformFaceAPositiveHighVWLargeB2T1Compact (m s : ℝ) : ℝ :=
  let n := m + 4
  let T := uniformFaceANonposT m s
  let L := uniformFaceACurrentM n T 1
  let K₀ := uniformFaceACurrentK n T (uniformFaceAPositiveQ0 m s)
  let H := uniformFaceACurrentK n T 1 - K₀
  let A := n^3 * L^3 * uniformFaceACoreXC0 n T 1
  let B := n^2 * L^2 * uniformFaceACoreXC1 n T 1
  let C := n * L * uniformFaceACoreXC2 n T 1
  let D := uniformFaceACoreXC3 n T 1
  K₀^3 * D + (2/3) * K₀^2 * (C + 2*H*D)
    + (5/12) * K₀ * (B + (4/3)*H*C + H^2*D) + (1/4) * (A + (2/3)*H*B + (1/3)*H^2*C)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem uniformFaceAPositiveHighVWLargeB2T1_eq_compact (m s : ℝ) :
    uniformFaceAPositiveHighVWLargeB2T1 m s = uniformFaceAPositiveHighVWLargeB2T1Compact m s := by
  unfold uniformFaceAPositiveHighVWLargeB2T1 uniformCubicSampleB1
  unfold uniformFaceAPositiveHighVWLargeB2R
  unfold uniformFaceAPositiveHighVWLargeB2 uniformCubicSampleB2
  unfold uniformFaceAPositiveHighVWLargeEndpoint
  unfold uniformFaceAPositiveHighVWLargeB2T1Compact uniformFaceAPositiveQ
  simp only [LargeB2CurrentK_affine]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformFaceAPositiveHighVWLargeB2T1_reduced (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceAPositiveHighVWLargeB2T1 m s =
      (m+4)^3 * LargeB2Positive1 m s /
        (72*(m+6)^8*((m+3)*(m+7)*(m+8))^3) := by
  rw [uniformFaceAPositiveHighVWLargeB2T1_eq_compact]
  unfold uniformFaceAPositiveHighVWLargeB2T1Compact
  dsimp only
  rw [uniformFaceACoreXC0_at_one, uniformFaceACoreXC1_at_one,
    uniformFaceACoreXC2_at_one, uniformFaceACoreXC3_at_one]
  rw [LargeL_eq m s hm hs, LargeK0_eq m s hm hs, LargeK1_eq m s hm hs]
  rw [LargeX0_eq m s hm, LargeX1_eq m s hm, LargeX2_eq m s hm, LargeX3_eq m s hm]
  rw [LargeX0_factor, LargeX1_factor, LargeX2_factor, LargeX3_factor,
    LargeH_factor m s hm, ← LargeB2Positive1_identity]
  have ha : m+6 ≠ 0 := by linarith
  have hb : m+3 ≠ 0 := by linarith
  have hc : m+7 ≠ 0 := by linarith
  have hd : m+8 ≠ 0 := by linarith
  field_simp [ha,hb,hc,hd]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformFaceAPositiveHighVWLargeB2T1_nonneg (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ uniformFaceAPositiveHighVWLargeB2T1 m s := by
  rw [uniformFaceAPositiveHighVWLargeB2T1_reduced m s hm hs]
  have h := LargeB2Positive1_nonneg m s hm hs
  positivity
end SSP.K3AllStages
