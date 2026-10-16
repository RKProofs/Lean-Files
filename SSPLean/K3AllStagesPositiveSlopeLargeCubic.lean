import SSPLean.K3AllStagesPositiveSlopeLargeBase
import SSPLean.CubicBernsteinClosure

/-! Cubic structure of the large chart, proved without expanding its parameters. -/
set_option autoImplicit false
namespace SSP.K3AllStages
open SSP.CubicBernstein

theorem uniformFaceAPositiveHighVWLargeEndpoint_isCubic (m s w : ℝ) :
    IsCubic (fun t => uniformFaceAPositiveHighVWLargeEndpoint m s w t) := by
  let n := m+4
  let T := uniformFaceANonposT m s
  let L := uniformFaceACurrentM n T 1
  let K := fun t : ℝ => uniformFaceACurrentK n T (uniformFaceAPositiveQ m s (w*t))
  let k := K 0
  let l := K 1-k
  have hK (t : ℝ) : K t = k+l*t := by
    dsimp only [K,k,l]
    unfold uniformFaceAPositiveQ uniformFaceACurrentK uniformReturnK
    ring
  have hid : (fun t => uniformFaceAPositiveHighVWLargeEndpoint m s w t) =
      fun t => (n^3*L^3*uniformFaceACoreXC0 n T 1)*t^3+
        (n^2*L^2*uniformFaceACoreXC1 n T 1)*t^2*(k+l*t)+
        (n*L*uniformFaceACoreXC2 n T 1)*t*(k+l*t)^2+
        uniformFaceACoreXC3 n T 1*(k+l*t)^3 := by
    funext t
    unfold uniformFaceAPositiveHighVWLargeEndpoint
    change t^3*n^3*L^3*uniformFaceACoreXC0 n T 1+
      t^2*n^2*L^2*K t*uniformFaceACoreXC1 n T 1+
      t*n*L*(K t)^2*uniformFaceACoreXC2 n T 1+(K t)^3*uniformFaceACoreXC3 n T 1 = _
    rw [hK]
    ring
  rw [hid]
  exact homogeneous_affine _ _ _ _ _ _

theorem uniformFaceAPositiveHighVWLargeB1_isCubic (m s : ℝ) :
    IsCubic (uniformFaceAPositiveHighVWLargeB1 m s) := by
  have h := (((uniformFaceAPositiveHighVWLargeEndpoint_isCubic m s 0).const_mul (-(5/6))).add
    ((uniformFaceAPositiveHighVWLargeEndpoint_isCubic m s 1).const_mul (1/3)) |>.add
    ((uniformFaceAPositiveHighVWLargeEndpoint_isCubic m s (1/3)).const_mul 3) |>.add
    ((uniformFaceAPositiveHighVWLargeEndpoint_isCubic m s (2/3)).const_mul (-(3/2))))
  have hid : uniformFaceAPositiveHighVWLargeB1 m s = fun t =>
      (-(5/6))*uniformFaceAPositiveHighVWLargeEndpoint m s 0 t+
      (1/3)*uniformFaceAPositiveHighVWLargeEndpoint m s 1 t+
      3*uniformFaceAPositiveHighVWLargeEndpoint m s (1/3) t+
      (-(3/2))*uniformFaceAPositiveHighVWLargeEndpoint m s (2/3) t := by
    funext t
    unfold uniformFaceAPositiveHighVWLargeB1 uniformCubicSampleB1
    ring
  rw [hid]
  exact h

theorem uniformFaceAPositiveHighVWLargeB2_isCubic (m s : ℝ) :
    IsCubic (uniformFaceAPositiveHighVWLargeB2 m s) := by
  have h := (((uniformFaceAPositiveHighVWLargeEndpoint_isCubic m s 0).const_mul (1/3)).add
    ((uniformFaceAPositiveHighVWLargeEndpoint_isCubic m s 1).const_mul (-(5/6))) |>.add
    ((uniformFaceAPositiveHighVWLargeEndpoint_isCubic m s (1/3)).const_mul (-(3/2))) |>.add
    ((uniformFaceAPositiveHighVWLargeEndpoint_isCubic m s (2/3)).const_mul 3))
  have hid : uniformFaceAPositiveHighVWLargeB2 m s = fun t =>
      (1/3)*uniformFaceAPositiveHighVWLargeEndpoint m s 0 t+
      (-(5/6))*uniformFaceAPositiveHighVWLargeEndpoint m s 1 t+
      (-(3/2))*uniformFaceAPositiveHighVWLargeEndpoint m s (1/3) t+
      3*uniformFaceAPositiveHighVWLargeEndpoint m s (2/3) t := by
    funext t
    unfold uniformFaceAPositiveHighVWLargeB2 uniformCubicSampleB2
    ring
  rw [hid]
  exact h

end SSP.K3AllStages
