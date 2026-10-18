import SSPLean.LogConvexIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Dimension-additive convolution of positive log-convex density quotients -/

open MeasureTheory Set
open scoped Topology
set_option autoImplicit false

namespace SSP.LogConvexIntegral

noncomputable def convolution (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..t, f (t-x)*g x

/-- Rescaling the convolution to a fixed integration interval. -/
theorem convolution_scale (f g : ℝ → ℝ) (t : ℝ) (ht : t ≠ 0) :
    convolution f g t = t*(∫ y in (0 : ℝ)..1, f (t*(1-y))*g (t*y)) := by
  have h := intervalIntegral.integral_comp_mul_left
    (fun x => f (t-x)*g x) (a := (0 : ℝ)) (b := 1) ht
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  have heq : (fun y => f (t*(1-y))*g (t*y)) =
      (fun y => f (t-t*y)*g (t*y)) := by
    funext y
    congr 2
    ring
  rw [convolution, heq, h]
  rw [← mul_assoc, mul_inv_cancel₀ ht, one_mul]

/-- The convolution of quotients with exponents `p` and `q` has exponent `p+q+1`.
In dimension notation these are dimensions `p+1`, `q+1`, and `p+q+2`. -/
theorem log_convolution_quotient_convex (f g : ℝ → ℝ) (p q : ℕ)
    (hf : Continuous f) (hg : Continuous g)
    (hfpos : ∀ t, 0 < t → 0 < f t) (hgpos : ∀ t, 0 < t → 0 < g t)
    (hfconv : ConvexOn ℝ (Ioi 0) (fun t => Real.log (f t/t^p)))
    (hgconv : ConvexOn ℝ (Ioi 0) (fun t => Real.log (g t/t^q))) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (convolution f g t/t^(p+q+1))) := by
  let F := fun t y : ℝ => f (t*(1-y))*g (t*y)/t^(p+q)
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  have hFpos : ∀ t ∈ Ioi (0 : ℝ), ∀ᵐ y ∂μ, 0 < F t y := by
    intro t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact div_pos (mul_pos (hfpos _ (mul_pos ht (sub_pos.mpr hy.2)))
      (hgpos _ (mul_pos ht hy.1))) (pow_pos ht _)
  have hFint : ∀ t ∈ Ioi (0 : ℝ), Integrable (F t) μ := by
    intro t ht
    have hcont : Continuous (F t) := by dsimp [F]; fun_prop
    exact (hcont.continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hIpos : ∀ t ∈ Ioi (0 : ℝ), 0 < ∫ y, F t y ∂μ := by
    intro t ht
    apply (integral_pos_iff_support_of_nonneg_ae ((hFpos t ht).mono fun _ h => h.le)
      (hFint t ht)).mpr
    have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support (F t) := by
      intro y hy
      exact (div_pos (mul_pos (hfpos _ (mul_pos ht (sub_pos.mpr hy.2)))
        (hgpos _ (mul_pos ht hy.1))) (pow_pos ht _)).ne'
    have hmeas : 0 < μ (Ioo (0 : ℝ) 1) := by simp [μ]
    exact hmeas.trans_le (measure_mono hsub)
  have hlog : ∀ y ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Ioi (0 : ℝ),
      Real.log (F t y) =
      Real.log (f (t*(1-y))/(t*(1-y))^p)+
      Real.log (g (t*y)/(t*y)^q)+(p : ℝ)*Real.log (1-y)+(q : ℝ)*Real.log y := by
    intro y hy t ht
    have h1 := mul_pos ht (sub_pos.mpr hy.2)
    have h2 := mul_pos ht hy.1
    dsimp [F]
    rw [Real.log_div (mul_pos (hfpos _ h1) (hgpos _ h2)).ne' (pow_ne_zero _ ht.ne'),
      Real.log_mul (hfpos _ h1).ne' (hgpos _ h2).ne',
      Real.log_div (hfpos _ h1).ne' (pow_ne_zero _ h1.ne'),
      Real.log_div (hgpos _ h2).ne' (pow_ne_zero _ h2.ne')]
    simp only [Real.log_pow, Real.log_mul ht.ne' (sub_pos.mpr hy.2).ne',
      Real.log_mul ht.ne' hy.1.ne', Nat.cast_add]
    ring
  have hFconv : ∀ᵐ y ∂μ, ConvexOn ℝ (Ioi 0) (fun t => Real.log (F t y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hfscale : ConvexOn ℝ (Ioi 0)
        (fun t => Real.log (f (t*(1-y))/(t*(1-y))^p)) := by
      refine ⟨convex_Ioi _, ?_⟩
      intro x hx z hz a b ha hb hab
      have h := hfconv.2 (mul_pos hx (sub_pos.mpr hy.2))
        (mul_pos hz (sub_pos.mpr hy.2)) ha hb hab
      simp only [smul_eq_mul] at h ⊢
      rw [show (a*x+b*z)*(1-y) = a*(x*(1-y))+b*(z*(1-y)) by ring]
      exact h
    have hgscale : ConvexOn ℝ (Ioi 0)
        (fun t => Real.log (g (t*y)/(t*y)^q)) := by
      refine ⟨convex_Ioi _, ?_⟩
      intro x hx z hz a b ha hb hab
      have h := hgconv.2 (mul_pos hx hy.1) (mul_pos hz hy.1) ha hb hab
      simp only [smul_eq_mul] at h ⊢
      rw [show (a*x+b*z)*y = a*(x*y)+b*(z*y) by ring]
      exact h
    apply ((hfscale.add hgscale).add_const ((p : ℝ)*Real.log (1-y)) |>.add_const
      ((q : ℝ)*Real.log y)).congr
    intro t ht
    exact (hlog y hy t ht).symm
  have hc := log_integral_convex μ (Ioi 0) (convex_Ioi _) F hFpos hFint hIpos hFconv
  apply hc.congr
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (show 0 < t from ht)
  have hscale := convolution_scale f g t ht.ne'
  have hfixed : (∫ y, F t y ∂μ) = convolution f g t/t^(p+q+1) := by
    dsimp [μ, F]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_div, hscale, pow_succ]
    field_simp [ht0]
  change Real.log (∫ y, F t y ∂μ) = _
  rw [hfixed]

end SSP.LogConvexIntegral
