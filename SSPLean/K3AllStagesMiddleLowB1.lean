import SSPLean.K3AllStagesMiddleLowBase

set_option autoImplicit false
namespace SSP.K3AllStages

theorem uniformFaceANonposMiddleLowB1_bernstein_v (m s v : ℝ) :
    uniformFaceANonposMiddleLowB1 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleLowB1 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleLowB1 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleLowB1 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleLowB1 m s u)) v := by
  let g := fun u : ℝ =>
    -(5/6)*uniformFaceANonposScaled m s u 1
      +(1/3)*uniformFaceANonposScaled m s u (1 + (m^2 + 38))
      +3*uniformFaceANonposScaled m s u (1 + (1/3)*(m^2 + 38))
      + (-(3/2))*uniformFaceANonposScaled m s u (1 + (2/3)*(m^2 + 38))
  have hfun : (fun u => uniformFaceANonposMiddleLowB1 m s u) = g := by
    funext u
    dsimp [g]
    unfold uniformFaceANonposMiddleLowB1 uniformFaceANonposMiddleLow
    simp only [uniformCubicSampleB1]
    ring_nf
  change (fun u => uniformFaceANonposMiddleLowB1 m s u) v =
    cornerBern3
      (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleLowB1 m s u))
      (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleLowB1 m s u))
      (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleLowB1 m s u))
      (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleLowB1 m s u)) v
  rw [hfun]
  exact uniformFaceANonposScaled_linear4_bernstein_v
    (-(5/6)) (1/3) 3 (-(3/2)) m s
    1 (1 + (m^2 + 38)) (1 + (1/3)*(m^2 + 38))
    (1 + (2/3)*(m^2 + 38)) v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceANonposMiddleLowB1_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposMiddleLowB1 m s v := by
  rw [uniformFaceANonposMiddleLowB1_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  all_goals
    first
    | simp only [uniformCubicSampleB0]
    | simp only [uniformCubicSampleB1]
    | simp only [uniformCubicSampleB2]
    | simp only [uniformCubicSampleB3]
    unfold uniformFaceANonposMiddleLowB1 uniformFaceANonposMiddleLow
    simp only [uniformCubicSampleB1]
    simp only [NonposCompactPolynomial_eq m s _ _ hm hs]
    unfold NonposCompactPolynomial
    ring_nf
    positivity

end SSP.K3AllStages
