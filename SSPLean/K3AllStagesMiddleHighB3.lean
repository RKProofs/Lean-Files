import SSPLean.K3AllStagesMiddleHighBase

set_option autoImplicit false
namespace SSP.K3AllStages

theorem uniformFaceANonposMiddleHighB3_bernstein_v (m s v : ℝ) :
    uniformFaceANonposMiddleHighB3 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleHighB3 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleHighB3 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleHighB3 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleHighB3 m s u)) v := by
  have hfun : (fun u => uniformFaceANonposMiddleHighB3 m s u) =
      (fun u => uniformFaceANonposScaled m s u (uniformFaceANonposP m / 8)) := by
    funext u
    unfold uniformFaceANonposMiddleHighB3 uniformFaceANonposMiddleHigh
    simp only [uniformCubicSampleB3]
    congr 2; ring
  change (fun u => uniformFaceANonposMiddleHighB3 m s u) v =
    cornerBern3
      (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleHighB3 m s u))
      (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleHighB3 m s u))
      (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleHighB3 m s u))
      (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleHighB3 m s u)) v
  rw [hfun]
  exact uniformFaceANonposScaled_hasCubicBernstein m s (uniformFaceANonposP m / 8) v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceANonposMiddleHighB3_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposMiddleHighB3 m s v := by
  rw [uniformFaceANonposMiddleHighB3_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    first
    | simp only [uniformCubicSampleB0]
    | simp only [uniformCubicSampleB1]
    | simp only [uniformCubicSampleB2]
    | simp only [uniformCubicSampleB3]
    unfold uniformFaceANonposMiddleHighB3 uniformFaceANonposMiddleHigh
    simp only [uniformCubicSampleB3]
    simp only [NonposCompactPolynomial_eq m s _ _ hm hs]
    unfold NonposCompactPolynomial uniformFaceANonposP
    field_simp
    ring_nf
    positivity

end SSP.K3AllStages
