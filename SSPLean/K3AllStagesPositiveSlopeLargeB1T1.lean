import SSPLean.K3AllStagesPositiveSlopeLargeB1T0

set_option autoImplicit false
namespace SSP.K3AllStages

private noncomputable def uniformFaceAPositiveHighVWLargeB1T1Compact
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
  K₀^3 * D + (2/3) * K₀^2 * (C + H*D)
    + (5/12) * K₀ * (B + (2/3)*H*C) + (1/4) * (A + (1/3)*H*B)

private theorem uniformFaceAPositiveHighVWLargeB1T1_eq_compact
    (m s : ℝ) :
    uniformFaceAPositiveHighVWLargeB1T1 m s =
      uniformFaceAPositiveHighVWLargeB1T1Compact m s := by
  unfold uniformFaceAPositiveHighVWLargeB1T1 uniformCubicSampleB1
  unfold uniformFaceAPositiveHighVWLargeB1R
  unfold uniformFaceAPositiveHighVWLargeB1 uniformCubicSampleB1
  unfold uniformFaceAPositiveHighVWLargeEndpoint
  unfold uniformFaceAPositiveHighVWLargeB1T1Compact
  unfold uniformFaceAPositiveQ
  unfold uniformFaceACurrentK uniformReturnK
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem uniformFaceAPositiveHighVWLargeB1T1_nonneg
    (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ uniformFaceAPositiveHighVWLargeB1T1 m s := by
  rw [uniformFaceAPositiveHighVWLargeB1T1_eq_compact]
  unfold uniformFaceAPositiveHighVWLargeB1T1Compact
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
