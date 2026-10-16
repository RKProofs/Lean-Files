import Mathlib

/-! # Positive integrals preserve log-convexity

A direct normalized weighted-Young argument proves the integral closure without
requiring an extra `Lp` interface. This is the closure used by dimension-additive
convolution of positive density quotients.
-/

open MeasureTheory Set
open scoped Topology
set_option autoImplicit false

namespace SSP.LogConvexIntegral

/-- A positive integral of functions with convex logarithms has a convex logarithm. -/
theorem log_integral_convex {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (D : Set ℝ) (hD : Convex ℝ D) (F : ℝ → α → ℝ)
    (hpos : ∀ t ∈ D, ∀ᵐ z ∂μ, 0 < F t z)
    (hint : ∀ t ∈ D, Integrable (F t) μ)
    (hIpos : ∀ t ∈ D, 0 < ∫ z, F t z ∂μ)
    (hconv : ∀ᵐ z ∂μ, ConvexOn ℝ D (fun t => Real.log (F t z))) :
    ConvexOn ℝ D (fun t => Real.log (∫ z, F t z ∂μ)) := by
  refine ⟨hD, ?_⟩
  intro x hx y hy a b ha hb hab
  let t := a*x+b*y
  have ht : t ∈ D := hD hx hy ha hb hab
  let Ix := ∫ z, F x z ∂μ
  let Iy := ∫ z, F y z ∂μ
  let K := Real.exp (a*Real.log Ix+b*Real.log Iy)
  have hIx : 0 < Ix := hIpos x hx
  have hIy : 0 < Iy := hIpos y hy
  have hK : 0 < K := Real.exp_pos _
  have hbound : ∀ᵐ z ∂μ,
      F t z ≤ K*(a*(F x z/Ix)+b*(F y z/Iy)) := by
    filter_upwards [hconv, hpos x hx, hpos y hy, hpos t ht] with z hz hzx hzy hzt
    have hlog := hz.2 hx hy ha hb hab
    simp only [smul_eq_mul] at hlog
    have he := Real.exp_le_exp.mpr (show Real.log (F t z)-Real.log K ≤
        a*Real.log (F x z/Ix)+b*Real.log (F y z/Iy) by
      rw [Real.log_div hzx.ne' hIx.ne', Real.log_div hzy.ne' hIy.ne']
      dsimp [K]
      rw [Real.log_exp]
      linarith)
    have hyoung := convexOn_exp.2 (Set.mem_univ (Real.log (F x z/Ix)))
      (Set.mem_univ (Real.log (F y z/Iy))) ha hb hab
    simp only [smul_eq_mul, Real.exp_log (div_pos hzx hIx),
      Real.exp_log (div_pos hzy hIy)] at hyoung
    rw [Real.exp_sub, Real.exp_log hzt, Real.exp_log hK] at he
    exact (div_le_iff₀ hK).mp (he.trans hyoung) |>.trans_eq (mul_comm _ _)
  have hright : Integrable (fun z => K*(a*(F x z/Ix)+b*(F y z/Iy))) μ :=
    (((hint x hx).div_const Ix).const_mul a |>.add
      (((hint y hy).div_const Iy).const_mul b)).const_mul K
  have hle := integral_mono_ae (hint t ht) hright hbound
  rw [integral_const_mul, integral_add
      (((hint x hx).div_const Ix).const_mul a)
      (((hint y hy).div_const Iy).const_mul b), integral_const_mul,
      integral_const_mul, integral_div, integral_div] at hle
  change (∫ z, F t z ∂μ) ≤ K*(a*(Ix/Ix)+b*(Iy/Iy)) at hle
  rw [div_self hIx.ne', div_self hIy.ne', mul_one, mul_one, hab, mul_one] at hle
  have hlog := Real.log_le_log (hIpos t ht) hle
  simpa only [K, Real.log_exp, smul_eq_mul] using hlog

end SSP.LogConvexIntegral
