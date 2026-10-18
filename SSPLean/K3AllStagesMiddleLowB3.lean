import SSPLean.K3AllStagesMiddleLowBase

set_option autoImplicit false
namespace SSP.K3AllStages

theorem uniformFaceANonposMiddleLowB3_bernstein_v (m s v : ℝ) :
    uniformFaceANonposMiddleLowB3 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleLowB3 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleLowB3 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleLowB3 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleLowB3 m s u)) v := by
  have hfun : (fun u => uniformFaceANonposMiddleLowB3 m s u) =
      (fun u => uniformFaceANonposScaled m s u (m^2 + 39)) := by
    funext u
    simp [uniformFaceANonposMiddleLowB3, uniformFaceANonposMiddleLow,
      uniformCubicSampleB3]
    ring_nf
  change (fun u => uniformFaceANonposMiddleLowB3 m s u) v =
    cornerBern3
      (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleLowB3 m s u))
      (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleLowB3 m s u))
      (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleLowB3 m s u))
      (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleLowB3 m s u)) v
  rw [hfun]
  exact uniformFaceANonposScaled_hasCubicBernstein m s (m^2 + 39) v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceANonposMiddleLowB3_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
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
    simp only [NonposCompactPolynomial_eq m s _ _ hm hs]
    unfold NonposCompactPolynomial
    ring_nf
    positivity

end SSP.K3AllStages
