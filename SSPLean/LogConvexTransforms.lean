import SSPLean.LogConvexConvolution

set_option autoImplicit false
open Set MeasureTheory

namespace SSP.LogConvexIntegral

theorem log_exp_convex (rate : ℝ) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (Real.exp (rate*t))) := by
  simp only [Real.log_exp]
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  exact le_of_eq (by ring)

theorem log_quotient_const_mul_convex (f : ℝ → ℝ) (p : ℕ) (c : ℝ)
    (hc : 0 < c) (hpos : ∀ t, 0 < t → 0 < f t)
    (hconv : ConvexOn ℝ (Ioi 0) (fun t => Real.log (f t/t^p))) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (c*f t/t^p)) := by
  apply (hconv.add_const (Real.log c)).congr
  intro t ht
  change Real.log (f t/t^p)+Real.log c = Real.log (c*f t/t^p)
  rw [mul_div_assoc, Real.log_mul hc.ne'
    (div_pos (hpos t ht) (pow_pos ht _)).ne']
  ring

theorem log_quotient_exp_mul_convex (f : ℝ → ℝ) (p : ℕ) (rate : ℝ)
    (hpos : ∀ t, 0 < t → 0 < f t)
    (hconv : ConvexOn ℝ (Ioi 0) (fun t => Real.log (f t/t^p))) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (Real.exp (rate*t)*f t/t^p)) := by
  apply ((log_exp_convex rate).add hconv).congr
  intro t ht
  change Real.log (Real.exp (rate*t))+Real.log (f t/t^p) =
    Real.log (Real.exp (rate*t)*f t/t^p)
  rw [mul_div_assoc, Real.log_mul (Real.exp_pos _).ne'
    (div_pos (hpos t ht) (pow_pos ht _)).ne']

theorem convolution_pos (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfpos : ∀ t, 0 < t → 0 < f t) (hgpos : ∀ t, 0 < t → 0 < g t)
    (t : ℝ) (ht : 0 < t) : 0 < convolution f g t := by
  rw [convolution_scale f g t ht.ne']
  apply mul_pos ht
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  let F := fun y : ℝ => f (t*(1-y))*g (t*y)
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  have hcont : Continuous F := by dsimp [F]; fun_prop
  have hint : Integrable F μ :=
    (hcont.continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hpos : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < F y := by
    intro y hy
    exact mul_pos (hfpos _ (mul_pos ht (sub_pos.mpr hy.2)))
      (hgpos _ (mul_pos ht hy.1))
  have hae : ∀ᵐ y ∂μ, 0 ≤ F y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact (hpos y hy).le
  apply (integral_pos_iff_support_of_nonneg_ae hae hint).mpr
  have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support F :=
    fun y hy => (hpos y hy).ne'
  exact (show 0 < μ (Ioo (0 : ℝ) 1) by simp [μ]).trans_le (measure_mono hsub)

/-- A nonnegative combination of two positive functions with convex logarithms
again has a convex logarithm, including the cases of a zero weight. -/
theorem log_nonneg_combination_convex (f g : ℝ → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a+b)
    (hfpos : ∀ t, 0 < t → 0 < f t) (hgpos : ∀ t, 0 < t → 0 < g t)
    (hf : ConvexOn ℝ (Ioi 0) (fun t => Real.log (f t)))
    (hg : ConvexOn ℝ (Ioi 0) (fun t => Real.log (g t))) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (a*f t+b*g t)) := by
  by_cases ha0 : a = 0
  · subst a
    simpa only [zero_mul, zero_add, pow_zero, div_one] using
      log_quotient_const_mul_convex g 0 b (by linarith) hgpos (by simpa using hg)
  by_cases hb0 : b = 0
  · subst b
    simpa only [zero_mul, add_zero, pow_zero, div_one] using
      log_quotient_const_mul_convex f 0 a (by linarith) hfpos (by simpa using hf)
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  let F : ℝ → Bool → ℝ := fun t z => if z then a*f t else b*g t
  have hpos : ∀ t ∈ Ioi (0 : ℝ), ∀ᵐ z ∂(Measure.count : Measure Bool), 0 < F t z := by
    intro t ht
    apply Filter.Eventually.of_forall
    intro z
    cases z
    · exact mul_pos hb' (hgpos t ht)
    · exact mul_pos ha' (hfpos t ht)
  have hint : ∀ t ∈ Ioi (0 : ℝ), Integrable (F t) Measure.count := by
    intro t ht
    exact Integrable.of_finite
  have hIpos : ∀ t ∈ Ioi (0 : ℝ), 0 < ∫ z, F t z ∂Measure.count := by
    intro t ht
    simp only [integral_count, F, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    exact add_pos (mul_pos ha' (hfpos t ht)) (mul_pos hb' (hgpos t ht))
  have hconv : ∀ᵐ z ∂(Measure.count : Measure Bool),
      ConvexOn ℝ (Ioi 0) (fun t => Real.log (F t z)) := by
    apply Filter.Eventually.of_forall
    intro z
    cases z
    · simpa only [F, Bool.false_eq_true, ↓reduceIte, pow_zero, div_one] using
        log_quotient_const_mul_convex g 0 b hb' hgpos (by simpa using hg)
    · simpa only [F, ↓reduceIte, pow_zero, div_one] using
        log_quotient_const_mul_convex f 0 a ha' hfpos (by simpa using hf)
  have hc := log_integral_convex Measure.count (Ioi 0) (convex_Ioi _) F
    hpos hint hIpos hconv
  simpa only [integral_count, F, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte] using hc

theorem log_nonneg_three_combination_convex (f g h : ℝ → ℝ) (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hfpos : ∀ t, 0 < t → 0 < f t) (hgpos : ∀ t, 0 < t → 0 < g t)
    (hhpos : ∀ t, 0 < t → 0 < h t)
    (hf : ConvexOn ℝ (Ioi 0) (fun t => Real.log (f t)))
    (hg : ConvexOn ℝ (Ioi 0) (fun t => Real.log (g t)))
    (hh : ConvexOn ℝ (Ioi 0) (fun t => Real.log (h t))) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (a*f t+b*g t+c*h t)) := by
  by_cases hab : a+b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    by_cases hc0 : c = 0
    · simpa [ha0,hb0,hc0] using convexOn_const (0 : ℝ) (convex_Ioi (0 : ℝ))
    · simpa only [ha0,hb0,zero_mul,add_zero,zero_add,pow_zero,div_one] using
        log_quotient_const_mul_convex h 0 c (lt_of_le_of_ne hc (Ne.symm hc0))
          hhpos (by simpa using hh)
  · have habpos : 0 < a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
    have hp : ∀ t, 0 < t → 0 < a*f t+b*g t := by
      intro t ht
      by_cases ha0 : a = 0
      · simp only [ha0,zero_mul,zero_add]
        exact mul_pos (by linarith) (hgpos t ht)
      · exact add_pos_of_pos_of_nonneg
          (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) (hfpos t ht))
          (mul_nonneg hb (hgpos t ht).le)
    simpa only [one_mul] using log_nonneg_combination_convex
      (fun t => a*f t+b*g t) h 1 c (by norm_num) hc (by linarith) hp hhpos
      (log_nonneg_combination_convex f g a b ha hb habpos hfpos hgpos hf hg) hh

end SSP.LogConvexIntegral
