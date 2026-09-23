import SSPLean.K3AllStagesPositiveSlopeLargeB2T1

set_option autoImplicit false
namespace SSP.K3AllStages

private noncomputable def uniformFaceAPositiveHighVWLargeB2T2Compact
    (m s : ℝ) : ℝ :=
  let n := m + 4
  let T := uniformFaceANonposT m s
  let L := uniformFaceACurrentM n T 1
  let K₀ := uniformFaceACurrentK n T (uniformFaceAPositiveQ0 m s)
  let H := uniformFaceACurrentK n T 1 - K₀
  let A := n^3 * L^3 * uniformFaceACoreXC0 n T 1
  let B := n^2 * L^2 * uniformFaceACoreXC1 n T 1
  let C := n * L * uniformFaceACoreXC2 n T 1
  let D := uniformFaceACoreXC3 n T 1
  K₀^3 * D + (5/6) * K₀^2 * (C + 2*H*D)
    + (2/3) * K₀ * (B + (4/3)*H*C + H^2*D)
    + (1/2) * (A + (2/3)*H*B + (1/3)*H^2*C)

private theorem uniformFaceAPositiveHighVWLargeB2T2_eq_compact
    (m s : ℝ) :
    uniformFaceAPositiveHighVWLargeB2T2 m s =
      uniformFaceAPositiveHighVWLargeB2T2Compact m s := by
  unfold uniformFaceAPositiveHighVWLargeB2T2 uniformCubicSampleB2
  unfold uniformFaceAPositiveHighVWLargeB2R
  unfold uniformFaceAPositiveHighVWLargeB2 uniformCubicSampleB2
  unfold uniformFaceAPositiveHighVWLargeEndpoint
  unfold uniformFaceAPositiveHighVWLargeB2T2Compact
  unfold uniformFaceAPositiveQ
  unfold uniformFaceACurrentK uniformReturnK
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem uniformFaceAPositiveHighVWLargeB2T2_nonneg
    (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ uniformFaceAPositiveHighVWLargeB2T2 m s := by
  rw [uniformFaceAPositiveHighVWLargeB2T2_eq_compact]
  unfold uniformFaceAPositiveHighVWLargeB2T2Compact
  unfold uniformFaceAPositiveQ0
  unfold uniformFaceAPositiveD uniformFaceANonposT
  unfold uniformFaceANonposZ uniformFaceANonposP
  unfold uniformFaceACurrentM uniformFaceACurrentK
  unfold uniformFaceACoreXC0 uniformFaceACoreXC1
  unfold uniformFaceACoreXC2 uniformFaceACoreXC3
  unfold uniformReturnM uniformReturnK uniformFaceACore
  field_simp
  ring_nf
  positivity

end SSP.K3AllStages
