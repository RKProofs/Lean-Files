import SSPLean.K3AllStagesTail

/-!
# Reusable cubic interpolation for the middle return-face charts

The normalized face core is cubic in `q`, while `uniformFaceANonposQ` is linear in the
terminal mixture coordinate.  This module proves that composition once and records closure
under four-term linear combinations.  The eight middle-chart coefficient modules can then
avoid unfolding the large core polynomial merely to rediscover cubicity.
-/

set_option autoImplicit false
namespace SSP.K3AllStages

def HasCubicBernstein (f : ℝ → ℝ) : Prop :=
  ∀ v, f v = cornerBern3 (uniformCubicSampleB0 f) (uniformCubicSampleB1 f)
    (uniformCubicSampleB2 f) (uniformCubicSampleB3 f) v

theorem uniformFaceANonposScaled_hasCubicBernstein (m s X : ℝ) :
    HasCubicBernstein (fun v => uniformFaceANonposScaled m s v X) := by
  intro v
  unfold uniformFaceANonposScaled
  simp_rw [uniformFaceACore_bernstein_q]
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3
  unfold uniformFaceANonposQ cornerBern3
  ring_nf

theorem uniformFaceANonposScaled_linear4_bernstein_v
    (a b c d m s X0 X1 X2 X3 v : ℝ) :
    a*uniformFaceANonposScaled m s v X0+b*uniformFaceANonposScaled m s v X1
      +c*uniformFaceANonposScaled m s v X2+d*uniformFaceANonposScaled m s v X3 =
    cornerBern3
      (uniformCubicSampleB0 (fun u =>
        a*uniformFaceANonposScaled m s u X0+b*uniformFaceANonposScaled m s u X1
          +c*uniformFaceANonposScaled m s u X2+d*uniformFaceANonposScaled m s u X3))
      (uniformCubicSampleB1 (fun u =>
        a*uniformFaceANonposScaled m s u X0+b*uniformFaceANonposScaled m s u X1
          +c*uniformFaceANonposScaled m s u X2+d*uniformFaceANonposScaled m s u X3))
      (uniformCubicSampleB2 (fun u =>
        a*uniformFaceANonposScaled m s u X0+b*uniformFaceANonposScaled m s u X1
          +c*uniformFaceANonposScaled m s u X2+d*uniformFaceANonposScaled m s u X3))
      (uniformCubicSampleB3 (fun u =>
        a*uniformFaceANonposScaled m s u X0+b*uniformFaceANonposScaled m s u X1
          +c*uniformFaceANonposScaled m s u X2+d*uniformFaceANonposScaled m s u X3)) v := by
  have h0 := uniformFaceANonposScaled_hasCubicBernstein m s X0
  have h1 := uniformFaceANonposScaled_hasCubicBernstein m s X1
  have h2 := uniformFaceANonposScaled_hasCubicBernstein m s X2
  have h3 := uniformFaceANonposScaled_hasCubicBernstein m s X3
  unfold HasCubicBernstein at h0 h1 h2 h3
  have h0v := h0 v
  have h1v := h1 v
  have h2v := h2 v
  have h3v := h3 v
  dsimp only at h0v h1v h2v h3v
  rw [h0v, h1v, h2v, h3v]
  unfold uniformCubicSampleB0 uniformCubicSampleB1
  unfold uniformCubicSampleB2 uniformCubicSampleB3 cornerBern3
  ring_nf

end SSP.K3AllStages
