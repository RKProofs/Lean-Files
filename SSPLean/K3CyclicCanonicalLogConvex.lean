import SSPLean.K3CyclicComplexCanonicalMiddleChart
import SSPLean.K3CyclicComplexCanonicalFirstCurvature
import SSPLean.K3CyclicCanonicalThirdIntegral
import SSPLean.LogConvexCurvature
import SSPLean.LogConvexTransforms
import SSPLean.MatrixMomentReduction

/-! # Logarithmic convexity of the actual canonical coordinates

The convolution transport is unconditional. The complex-spectrum conclusions
use explicit Vieta data; no spectral classification or general canonical
representation is assumed to have been constructed by this file.
-/

set_option autoImplicit false
open Set Matrix MeasureTheory

namespace SSP.K3Cyclic

open SSP.LogConvexIntegral

theorem canonicalB_nonneg {a b c x2 x3 : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3) :
    ∀ i j, 0 ≤ canonicalB a b c x2 x3 i j := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first | exact le_rfl | exact ha | exact hb | exact hc | exact h2 | exact h3

theorem canonicalCoordinate_eq_pairing (a b c x2 x3 t : ℝ) (i : Fin 3) :
    ((NormedSpace.exp (t • canonicalB a b c x2 x3)).mulVec firstBasis) i =
      SSP.MatrixMomentReduction.pairing (canonicalB a b c x2 x3)
        (Pi.single i 1) firstBasis t := by
  simp only [SSP.MatrixMomentReduction.pairing,
    SSP.MatrixMomentReduction.pairingFun_apply, dotProduct]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, one_mul]
    rfl
  · intro j hj hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem canonicalMiddle_pos {a b c x2 x3 : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h2 : 0 < x2) (h3 : 0 ≤ x3)
    (t : ℝ) (ht : 0 < t) : 0 < canonicalMiddle a b c x2 x3 t := by
  have hne : canonicalMiddle a b c x2 x3 ≠ 0 := by
    intro hz
    have hd := (canonicalMiddle_hasDerivAt a b c x2 x3 0).deriv
    rw [hz] at hd
    simp only [deriv_zero, Pi.zero_apply, canonicalMiddleDeriv_zero] at hd
    linarith
  have hpair : SSP.MatrixMomentReduction.pairing (canonicalB a b c x2 x3)
      (Pi.single 1 1) firstBasis ≠ 0 := by
    convert hne using 1
    funext s
    exact (canonicalCoordinate_eq_pairing a b c x2 x3 s 1).symm
  rw [canonicalMiddle, canonicalCoordinate_eq_pairing]
  apply SSP.MatrixMomentReduction.pairing_pos _ _ _
    (canonicalB_nonneg ha hb hc h2.le h3) _ _ hpair t ht
  · intro i
    by_cases hi : i = 1 <;> simp [hi]
  · intro i
    fin_cases i <;> norm_num [firstBasis]

theorem canonicalFirst_pos {a b c x2 x3 : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3)
    (t : ℝ) (ht : 0 < t) : 0 < canonicalFirst a b c x2 x3 t := by
  have hne : canonicalFirst a b c x2 x3 ≠ 0 := by
    intro hz
    have h0 := canonicalFirst_zero a b c x2 x3
    rw [hz] at h0
    simp at h0
  have hpair : SSP.MatrixMomentReduction.pairing (canonicalB a b c x2 x3)
      (Pi.single 0 1) firstBasis ≠ 0 := by
    convert hne using 1
    funext s
    exact (canonicalCoordinate_eq_pairing a b c x2 x3 s 0).symm
  rw [canonicalFirst, canonicalCoordinate_eq_pairing]
  apply SSP.MatrixMomentReduction.pairing_pos _ _ _
    (canonicalB_nonneg ha hb hc h2 h3) _ _ hpair t ht
  · intro i
    by_cases hi : i = 0 <;> simp [hi]
  · intro i
    fin_cases i <;> norm_num [firstBasis]

theorem canonicalFirst_orderedRealRoots_log_quotient_convex
    {a b c x2 x3 u v w : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3)
    (huv : u ≤ v) (hvw : v ≤ w) (hw : 0 < w)
    (hsum : u+v+w = a+b) (hpair : u*v+u*w+v*w = a*b)
    (hprod : u*v*w = c*x2*x3) :
    ConvexOn ℝ (Ioi 0)
      (fun t => Real.log (canonicalFirst a b c x2 x3 t/t^2)) := by
  apply log_quotient_convex_of_curvature _ _ _ 2
    (canonicalFirst_hasDerivAt a b c x2 x3)
    (canonicalFirstDeriv_hasDerivAt a b c x2 x3)
    (canonicalFirst_pos ha hb hc h2 h3)
  intro t ht
  have h := canonicalFirst_orderedRealRoots_correctedCurvature3_nonneg
    ha hb hc h2 h3 huv hvw hw hsum hpair hprod ht.le
  rw [(canonicalFirst_hasDerivAt a b c x2 x3 t).deriv] at h
  have heq : deriv (canonicalFirst a b c x2 x3) = canonicalFirstDeriv a b c x2 x3 := by
    funext s
    exact (canonicalFirst_hasDerivAt a b c x2 x3 s).deriv
  rw [heq, (canonicalFirstDeriv_hasDerivAt a b c x2 x3 t).deriv] at h
  exact h

theorem canonicalFirst_complexPair_log_quotient_convex
    {a b c x2 x3 m omega d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3)
    (hd : 0 < d) (homega : omega ≠ 0)
    (hsum : a+b = d*(1+3*m))
    (hpair : a*b = d^2*(3*m^2+2*m+omega^2))
    (hprod : c*x2*x3 = d^3*((1+m)*(m^2+omega^2))) :
    ConvexOn ℝ (Ioi 0)
      (fun t => Real.log (canonicalFirst a b c x2 x3 t/t^2)) := by
  apply log_quotient_convex_of_curvature _ _ _ 2
    (canonicalFirst_hasDerivAt a b c x2 x3)
    (canonicalFirstDeriv_hasDerivAt a b c x2 x3)
    (canonicalFirst_pos ha hb hc h2 h3)
  intro t ht
  exact canonicalFirst_complexPair_correctedCurvature3_nonneg_of_vieta
    ha hb hd ht.le homega hsum hpair hprod

theorem canonicalThird_eq_convolution (a b c x2 x3 t : ℝ) :
    canonicalThird a b c x2 x3 t =
      x3*convolution (fun s => Real.exp (b*s)) (canonicalMiddle a b c x2 x3) t := by
  have h := canonicalThirdWeighted_eq_integral a b c x2 x3 t
  have he : Real.exp (b*t)*canonicalThirdWeighted a b c x2 x3 t =
      canonicalThird a b c x2 x3 t := by
    rw [canonicalThirdWeighted, ← mul_assoc, ← Real.exp_add]
    simp
  rw [← he, h, SSP.LogConvexIntegral.convolution, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  change Real.exp (b*t)*(x3*Real.exp (-b*s)*canonicalMiddle a b c x2 x3 s) =
    x3*(Real.exp (b*(t-s))*canonicalMiddle a b c x2 x3 s)
  have hexp : Real.exp (b*t)*Real.exp (-b*s) = Real.exp (b*(t-s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = x3*((Real.exp (b*t)*Real.exp (-b*s))*canonicalMiddle a b c x2 x3 s) := by ring
    _ = _ := by rw [hexp]

theorem canonicalThird_pos {a b c x2 x3 : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h2 : 0 < x2) (h3 : 0 < x3)
    (t : ℝ) (ht : 0 < t) : 0 < canonicalThird a b c x2 x3 t := by
  rw [canonicalThird_eq_convolution]
  apply mul_pos h3
  exact convolution_pos _ _ (by fun_prop)
    (continuous_iff_continuousAt.mpr fun s =>
      (canonicalMiddle_hasDerivAt a b c x2 x3 s).continuousAt)
    (fun s _ => Real.exp_pos _) (canonicalMiddle_pos ha hb hc h2 h3.le) t ht

/-- The third coordinate inherits the dimension-three logarithmic convexity
from the stronger dimension-two middle-coordinate result. -/
theorem canonicalThird_log_quotient_convex_of_middle
    {a b c x2 x3 : ℝ} (h3 : 0 < x3)
    (hmpos : ∀ t, 0 < t → 0 < canonicalMiddle a b c x2 x3 t)
    (hmconv : ConvexOn ℝ (Ioi 0)
      (fun t => Real.log (canonicalMiddle a b c x2 x3 t/t))) :
    ConvexOn ℝ (Ioi 0)
      (fun t => Real.log (canonicalThird a b c x2 x3 t/t^2)) := by
  have hmcont : Continuous (canonicalMiddle a b c x2 x3) :=
    continuous_iff_continuousAt.mpr fun s =>
      (canonicalMiddle_hasDerivAt a b c x2 x3 s).continuousAt
  have hconv := log_convolution_quotient_convex
    (fun s => Real.exp (b*s)) (canonicalMiddle a b c x2 x3) 0 1
    (by fun_prop) hmcont (fun s _ => Real.exp_pos _) hmpos
    (by simpa using log_exp_convex b) (by simpa using hmconv)
  have hpos := convolution_pos (fun s => Real.exp (b*s))
    (canonicalMiddle a b c x2 x3) (by fun_prop) hmcont
    (fun s _ => Real.exp_pos _) hmpos
  have hc := log_quotient_const_mul_convex _ 2 x3 h3 hpos (by simpa using hconv)
  simpa only [canonicalThird_eq_convolution] using hc

theorem canonicalMiddle_complexPair_log_quotient_convex
    {a b c x2 x3 mu d omega : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) (hc : 0 ≤ c)
    (h2 : 0 < x2) (h3 : 0 ≤ x3) (hd : 0 < d)
    (hsum : a+b = 3*mu+d)
    (hpair : a*b = 3*mu^2+2*mu*d+d^2*omega^2)
    (hprod : c*x2*x3 = (mu+d)*(mu^2+d^2*omega^2)) :
    ConvexOn ℝ (Ioi 0)
      (fun t => Real.log (canonicalMiddle a b c x2 x3 t/t)) := by
  have h := log_quotient_convex_of_curvature _ _ _ 1
    (canonicalMiddle_hasDerivAt a b c x2 x3)
    (canonicalMiddleDeriv_hasDerivAt a b c x2 x3)
    (canonicalMiddle_pos ha hb hc h2 h3)
    (fun t ht => by
      simpa only [Nat.cast_one, one_mul, middleCurvature3] using
        canonicalMiddle_complexPair_middleCurvature3_nonneg ha hb hab hd ht.le hsum hpair hprod)
  simpa only [pow_one] using h

theorem canonicalThird_complexPair_log_quotient_convex
    {a b c x2 x3 mu d omega : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) (hc : 0 ≤ c)
    (h2 : 0 < x2) (h3 : 0 < x3) (hd : 0 < d)
    (hsum : a+b = 3*mu+d)
    (hpair : a*b = 3*mu^2+2*mu*d+d^2*omega^2)
    (hprod : c*x2*x3 = (mu+d)*(mu^2+d^2*omega^2)) :
    ConvexOn ℝ (Ioi 0)
      (fun t => Real.log (canonicalThird a b c x2 x3 t/t^2)) :=
  canonicalThird_log_quotient_convex_of_middle h3
    (canonicalMiddle_pos ha hb hc h2 h3.le)
    (canonicalMiddle_complexPair_log_quotient_convex ha hb hab hc h2 h3.le hd hsum hpair hprod)

end SSP.K3Cyclic
