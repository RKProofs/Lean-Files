import SSPLean.K3AllStagesMiddleLowB2C0
import SSPLean.K3AllStagesMiddleLowB2C1
import SSPLean.K3AllStagesMiddleLowB2C2
import SSPLean.K3AllStagesMiddleLowB2C3

set_option autoImplicit false
namespace SSP.K3AllStages

theorem uniformFaceANonposMiddleLowB2_bernstein_v (m s v : ℝ) :
    uniformFaceANonposMiddleLowB2 m s v =
      cornerBern3
        (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleLowB2 m s u))
        (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleLowB2 m s u))
        (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleLowB2 m s u))
        (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleLowB2 m s u)) v := by
  let g := fun u : ℝ =>
    (1/3)*uniformFaceANonposScaled m s u 1
      + (-(5/6))*uniformFaceANonposScaled m s u (1 + (m^2 + 38))
      + (-(3/2))*uniformFaceANonposScaled m s u (1 + (1/3)*(m^2 + 38))
      +3*uniformFaceANonposScaled m s u (1 + (2/3)*(m^2 + 38))
  have hfun : (fun u => uniformFaceANonposMiddleLowB2 m s u) = g := by
    funext u
    dsimp [g]
    unfold uniformFaceANonposMiddleLowB2 uniformFaceANonposMiddleLow
    simp only [uniformCubicSampleB2]
    ring_nf
  change (fun u => uniformFaceANonposMiddleLowB2 m s u) v =
    cornerBern3
      (uniformCubicSampleB0 (fun u => uniformFaceANonposMiddleLowB2 m s u))
      (uniformCubicSampleB1 (fun u => uniformFaceANonposMiddleLowB2 m s u))
      (uniformCubicSampleB2 (fun u => uniformFaceANonposMiddleLowB2 m s u))
      (uniformCubicSampleB3 (fun u => uniformFaceANonposMiddleLowB2 m s u)) v
  rw [hfun]
  exact uniformFaceANonposScaled_linear4_bernstein_v
    (1/3) (-(5/6)) (-(3/2)) 3 m s
    1 (1 + (m^2 + 38)) (1 + (1/3)*(m^2 + 38))
    (1 + (2/3)*(m^2 + 38)) v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceANonposMiddleLowB2_nonneg
    (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ uniformFaceANonposMiddleLowB2 m s v := by
  rw [uniformFaceANonposMiddleLowB2_bernstein_v]
  apply cornerBern3_nonneg <;> try assumption
  · rw [MiddleLowB2Positive0_eq m s hm hs]
    exact MiddleLowB2Positive0_nonneg m s hm hs
  · rw [MiddleLowB2Positive1_eq m s hm hs]
    exact MiddleLowB2Positive1_nonneg m s hm hs
  · rw [MiddleLowB2Positive2_eq m s hm hs]
    exact MiddleLowB2Positive2_nonneg m s hm hs
  · rw [MiddleLowB2Positive3_eq m s hm hs]
    exact MiddleLowB2Positive3_nonneg m s hm hs

end SSP.K3AllStages
