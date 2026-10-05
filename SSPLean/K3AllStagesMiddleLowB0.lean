import SSPLean.K3AllStagesMiddleLowBase

set_option autoImplicit false
namespace SSP.K3AllStages

theorem uniformFaceANonposMiddleLowB0_bernstein_v (m s v : ℝ) :
    uniformFaceANonposMiddleLowB0 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleLowB0 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleLowB0 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleLowB0 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleLowB0 m s u)) v := by
  have hfun : (fun u => uniformFaceANonposMiddleLowB0 m s u) =
      (fun u => uniformFaceANonposScaled m s u 1) := by
    funext u
    simp [uniformFaceANonposMiddleLowB0, uniformFaceANonposMiddleLow,
      uniformCubicSampleB0]
  change (fun u => uniformFaceANonposMiddleLowB0 m s u) v =
    cornerBern3
      (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleLowB0 m s u))
      (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleLowB0 m s u))
      (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleLowB0 m s u))
      (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleLowB0 m s u)) v
  rw [hfun]
  exact uniformFaceANonposScaled_hasCubicBernstein m s 1 v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceANonposMiddleLowB0_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
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

end SSP.K3AllStages
