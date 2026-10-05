import SSPLean.K3AllStagesMiddleHighBase

set_option autoImplicit false
namespace SSP.K3AllStages

theorem uniformFaceANonposMiddleHighB0_bernstein_v (m s v : ℝ) :
    uniformFaceANonposMiddleHighB0 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleHighB0 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleHighB0 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleHighB0 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleHighB0 m s u)) v := by
  have hfun : (fun u => uniformFaceANonposMiddleHighB0 m s u) =
      (fun u => uniformFaceANonposScaled m s u (m^2 + 39)) := by
    funext u
    simp [uniformFaceANonposMiddleHighB0, uniformFaceANonposMiddleHigh,
      uniformCubicSampleB0]
  change (fun u => uniformFaceANonposMiddleHighB0 m s u) v =
    cornerBern3
      (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleHighB0 m s u))
      (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleHighB0 m s u))
      (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleHighB0 m s u))
      (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleHighB0 m s u)) v
  rw [hfun]
  exact uniformFaceANonposScaled_hasCubicBernstein m s (m^2 + 39) v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceANonposMiddleHighB0_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
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

end SSP.K3AllStages
