import SSPLean.K3AllStagesPositiveSlopeLargeB0C0
import SSPLean.K3AllStagesPositiveSlopeLargeB0C1
import SSPLean.K3AllStagesPositiveSlopeLargeB0C2
import SSPLean.K3AllStagesPositiveSlopeLargeB0C3
set_option autoImplicit false
namespace SSP.K3AllStages
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem LargeB0_shift_eq (m s r : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceAPositiveHighVWLargeB0 m s ((1+r)/2) =
      (m+4)^3*(LargeB0Positive0 m s + LargeLNumerator m s*LargeB0Positive1 m s*r
        +(LargeLNumerator m s)^2*LargeB0Positive2 m s*r^2
        +(LargeLNumerator m s)^3*LargeB0Positive3 m s*r^3) /
        (8*(m+6)^8*((m+3)*(m+7)*(m+8))^3) := by
  simp only [uniformFaceAPositiveHighVWLargeB0, uniformCubicSampleB0]
  unfold uniformFaceAPositiveHighVWLargeEndpoint
  simp only [zero_mul, uniformFaceAPositiveQ, add_zero]
  rw [uniformFaceACoreXC0_at_one, uniformFaceACoreXC1_at_one,
    uniformFaceACoreXC2_at_one, uniformFaceACoreXC3_at_one]
  rw [LargeL_eq m s hm hs, LargeK0_eq m s hm hs]
  rw [LargeX0_eq m s hm, LargeX1_eq m s hm, LargeX2_eq m s hm, LargeX3_eq m s hm]
  rw [LargeX0_factor, LargeX1_factor, LargeX2_factor, LargeX3_factor]
  rw [← LargeB0Positive0_identity, ← LargeB0Positive1_identity,
    ← LargeB0Positive2_identity, ← LargeB0Positive3_identity]
  have ha : m+6 ≠ 0 := by linarith
  have hb : m+3 ≠ 0 := by linarith
  have hc : m+7 ≠ 0 := by linarith
  have hd : m+8 ≠ 0 := by linarith
  field_simp [ha,hb,hc,hd]
  ring

set_option maxRecDepth 100000 in
theorem uniformFaceAPositiveHighVWLargeB0_nonneg
    (m s t : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) (ht : 1/2 ≤ t) :
    0 ≤ uniformFaceAPositiveHighVWLargeB0 m s t := by
  let r := 2*t-1
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have htId : t = (1+r)/2 := by dsimp [r]; ring
  rw [htId, LargeB0_shift_eq m s r hm hs]
  have h0 := LargeB0Positive0_nonneg m s hm hs
  have h1 := LargeB0Positive1_nonneg m s hm hs
  have h2 := LargeB0Positive2_nonneg m s hm hs
  have h3 := LargeB0Positive3_nonneg m s hm hs
  have hL : 0 ≤ LargeLNumerator m s := by unfold LargeLNumerator; positivity
  positivity
end SSP.K3AllStages
