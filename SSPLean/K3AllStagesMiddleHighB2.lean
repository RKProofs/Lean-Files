import SSPLean.K3AllStagesMiddleHighBase

set_option autoImplicit false
namespace SSP.K3AllStages

theorem uniformFaceANonposMiddleHighB2_bernstein_v (m s v : ℝ) :
    uniformFaceANonposMiddleHighB2 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleHighB2 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleHighB2 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleHighB2 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleHighB2 m s u)) v := by
  let L := m^2 + 39
  let W := uniformFaceANonposP m / 8 - L
  let g := fun u : ℝ =>
    (1/3)*uniformFaceANonposScaled m s u L
      + (-(5/6))*uniformFaceANonposScaled m s u (L + W)
      + (-(3/2))*uniformFaceANonposScaled m s u (L + (1/3)*W)
      +3*uniformFaceANonposScaled m s u (L + (2/3)*W)
  have hfun : (fun u => uniformFaceANonposMiddleHighB2 m s u) = g := by
    funext u
    dsimp [g, L, W]
    unfold uniformFaceANonposMiddleHighB2 uniformFaceANonposMiddleHigh
    simp only [uniformCubicSampleB2]
    ring_nf
  change (fun u => uniformFaceANonposMiddleHighB2 m s u) v =
    cornerBern3
      (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleHighB2 m s u))
      (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleHighB2 m s u))
      (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleHighB2 m s u))
      (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleHighB2 m s u)) v
  rw [hfun]
  exact uniformFaceANonposScaled_linear4_bernstein_v
    (1/3) (-(5/6)) (-(3/2)) 3 m s
    L (L + W) (L + (1/3)*W) (L + (2/3)*W) v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceANonposMiddleHighB2_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposMiddleHighB2 m s v := by
  rw [uniformFaceANonposMiddleHighB2_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    first
    | simp only [uniformCubicSampleB0]
    | simp only [uniformCubicSampleB1]
    | simp only [uniformCubicSampleB2]
    | simp only [uniformCubicSampleB3]
    unfold uniformFaceANonposMiddleHighB2 uniformFaceANonposMiddleHigh
    simp only [uniformCubicSampleB2]
    simp only [NonposCompactPolynomial_eq m s _ _ hm hs]
    unfold NonposCompactPolynomial uniformFaceANonposP
    field_simp
    ring_nf
    positivity

end SSP.K3AllStages
