import SSPLean.K3CyclicRealTailLarge
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Mixed uniform-moment estimate for the three-state real-spectrum tail

This file isolates the pointwise maximization and interval-integration
argument used to bound the mixed term in the signed-moment determinant.
-/

set_option autoImplicit false

namespace SSP.K3CyclicRealTail

/-- The one-variable factor whose maximum produces `crossCoefficient`. -/
noncomputable def gapProfile (n : ℕ) (t : ℝ) : ℝ :=
  t ^ (n - 1) * (1 - t) ^ 2

/-- Derivative of the pointwise profile, in sign-transparent form. -/
theorem hasDerivAt_gapProfile {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    HasDerivAt (gapProfile n)
      (t ^ (n - 2) * (1 - t) *
        ((n - 1 : ℕ) - (n + 1 : ℕ) * t)) t := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  convert! (((hasDerivAt_pow (2 + r - 1) t).mul
    (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).pow 2))) using 1
  all_goals
    simp [show 2 + r - 1 = r + 1 by omega,
      show 2 + r - 2 = r by omega, pow_succ]
    ring

/-- The critical point of `gapProfile`. -/
noncomputable def gapCritical (n : ℕ) : ℝ :=
  (n - 1 : ℝ) / (n + 1 : ℝ)

theorem gapCritical_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ gapCritical n := by
  unfold gapCritical
  apply div_nonneg
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · positivity

theorem gapCritical_le_one (n : ℕ) : gapCritical n ≤ 1 := by
  unfold gapCritical
  have hden : 0 < (n + 1 : ℝ) := by positivity
  apply (div_le_one hden).mpr
  have hn0 : (0 : ℝ) ≤ n := by positivity
  linarith

theorem gapCritical_balance {n : ℕ} (hn : 1 ≤ n) :
    (n + 1 : ℝ) * gapCritical n = (n - 1 : ℕ) := by
  unfold gapCritical
  have hden : (n + 1 : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hden]
  norm_num only [Nat.cast_sub hn, Nat.cast_one]

theorem gapProfile_le_critical {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gapProfile n t ≤ gapProfile n (gapCritical n) := by
  have hp0 : 0 ≤ gapCritical n := gapCritical_nonneg (by omega)
  have hp1 : gapCritical n ≤ 1 := gapCritical_le_one n
  have hbalance := gapCritical_balance (by omega : 1 ≤ n)
  have hcont : Continuous (gapProfile n) := by
    unfold gapProfile
    fun_prop
  have hmono : MonotoneOn (gapProfile n) (Set.Icc 0 (gapCritical n)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg
      (convex_Icc (0 : ℝ) (gapCritical n)) hcont.continuousOn
    · intro x hx
      exact (hasDerivAt_gapProfile hn x).hasDerivWithinAt
    · intro x hx
      have hxmem : x ∈ Set.Icc (0 : ℝ) (gapCritical n) := by
        exact interior_subset hx
      have hx0 : 0 ≤ x := hxmem.1
      have hxp : x ≤ gapCritical n := hxmem.2
      have hx1 : x ≤ 1 := hxp.trans hp1
      have hcoeff :
          0 ≤ ((n - 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) * x := by
        norm_num only [Nat.cast_add, Nat.cast_one] at hbalance ⊢
        nlinarith
      exact mul_nonneg (mul_nonneg (pow_nonneg hx0 _) (by linarith)) hcoeff
  have hanti : AntitoneOn (gapProfile n) (Set.Icc (gapCritical n) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (convex_Icc (gapCritical n) (1 : ℝ)) hcont.continuousOn
    · intro x hx
      exact (hasDerivAt_gapProfile hn x).hasDerivWithinAt
    · intro x hx
      have hxmem : x ∈ Set.Icc (gapCritical n) (1 : ℝ) := by
        exact interior_subset hx
      have hpx : gapCritical n ≤ x := hxmem.1
      have hx1 : x ≤ 1 := hxmem.2
      have hx0 : 0 ≤ x := hp0.trans hpx
      have hcoeff :
          ((n - 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) * x ≤ 0 := by
        norm_num only [Nat.cast_add, Nat.cast_one] at hbalance ⊢
        nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (pow_nonneg hx0 _) (by linarith)) hcoeff
  by_cases htp : t ≤ gapCritical n
  · exact hmono ⟨ht0, htp⟩ ⟨hp0, le_rfl⟩ htp
  · have hpt : gapCritical n ≤ t := le_of_not_ge htp
    exact hanti ⟨le_rfl, hp1⟩ ⟨hpt, ht1⟩ hpt

theorem gapProfile_critical_eq_crossCoefficient {n : ℕ} (hn : 2 ≤ n) :
    gapProfile n (gapCritical n) = crossCoefficient n := by
  unfold gapProfile gapCritical crossCoefficient
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  have hden : (n + 1 : ℝ) ≠ 0 := by positivity
  rw [div_pow]
  field_simp [hden, pow_ne_zero]
  rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
  ring

/-- Exact pointwise maximization used in the mixed-moment estimate. -/
theorem gapProfile_le_crossCoefficient {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ^ (n - 1) * (1 - t) ^ 2 ≤ crossCoefficient n := by
  rw [← gapProfile_critical_eq_crossCoefficient hn]
  exact gapProfile_le_critical hn ht0 ht1

/-- Pointwise integrand whose double average is `mixedUniformCross`. -/
noncomputable def mixedKernel (n : ℕ) (x y : ℝ) : ℝ :=
  x ^ (n - 1) * y ^ (n - 1) * (x - y) ^ 2

theorem mixedKernel_nonneg {n : ℕ} {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ mixedKernel n x y := by
  unfold mixedKernel
  positivity

/-- The endpoint cap `y ≤ v` gives the first pointwise bound. -/
theorem mixedKernel_le_v {n : ℕ} (hn : 1 ≤ n) {x y v : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x) (hyv : y ≤ v) :
    mixedKernel n x y ≤ v ^ (n - 1) * x ^ (n + 1) := by
  have hv : 0 ≤ v := hy.trans hyv
  have hpow : y ^ (n - 1) ≤ v ^ (n - 1) := pow_le_pow_left₀ hy hyv _
  have hsq : (x - y) ^ 2 ≤ x ^ 2 := by nlinarith
  unfold mixedKernel
  calc
    x ^ (n - 1) * y ^ (n - 1) * (x - y) ^ 2 ≤
        x ^ (n - 1) * v ^ (n - 1) * x ^ 2 := by
      gcongr
    _ = v ^ (n - 1) * x ^ (n + 1) := by
      rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
      ring

/-- Pointwise maximization gives the second bound, uniformly in `y`. -/
theorem mixedKernel_le_crossCoefficient {n : ℕ} (hn : 2 ≤ n) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    mixedKernel n x y ≤ crossCoefficient n * x ^ (n + 1) := by
  by_cases hxzero : x = 0
  · subst x
    have hyzero : y = 0 := by linarith
    subst y
    simp [mixedKernel]
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxzero)
    let t : ℝ := y / x
    have ht0 : 0 ≤ t := div_nonneg hy0 hx0
    have ht1 : t ≤ 1 := (div_le_one hxpos).mpr hyx
    have hgap := gapProfile_le_crossCoefficient hn ht0 ht1
    have hkernel : mixedKernel n x y = x ^ (2 * n) * gapProfile n t := by
      unfold mixedKernel gapProfile t
      rw [div_pow]
      field_simp [hxzero]
      rw [show 2 * n = (n - 1) + (n - 1) + 2 by omega, pow_add, pow_add]
      ring
    have hpow : x ^ (2 * n) ≤ x ^ (n + 1) := by
      exact pow_le_pow_of_le_one hx0 hx1 (by omega)
    rw [hkernel]
    calc
      x ^ (2 * n) * gapProfile n t ≤ x ^ (2 * n) * crossCoefficient n :=
        mul_le_mul_of_nonneg_left hgap (pow_nonneg hx0 _)
      _ ≤ x ^ (n + 1) * crossCoefficient n :=
        mul_le_mul_of_nonneg_right hpow (crossCoefficient_nonneg n)
      _ = crossCoefficient n * x ^ (n + 1) := by ring

theorem mixedKernel_expand {n : ℕ} (hn : 1 ≤ n) (x y : ℝ) :
    mixedKernel n x y =
      x ^ (n - 1) * y ^ (n + 1) + x ^ (n + 1) * y ^ (n - 1) -
        2 * x ^ n * y ^ n := by
  unfold mixedKernel
  have hx1 : x ^ (n + 1) = x ^ (n - 1) * x ^ 2 := by
    rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
  have hy1 : y ^ (n + 1) = y ^ (n - 1) * y ^ 2 := by
    rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
  have hxn : x ^ n = x ^ (n - 1) * x := by
    calc
      x ^ n = x ^ ((n - 1) + 1) := by congr 1; omega
      _ = x ^ (n - 1) * x := pow_succ x (n - 1)
  have hyn : y ^ n = y ^ (n - 1) * y := by
    calc
      y ^ n = y ^ ((n - 1) + 1) := by congr 1; omega
      _ = y ^ (n - 1) * y := pow_succ y (n - 1)
  rw [hx1, hy1, hxn, hyn]
  ring

/-- Integrating the kernel first in `y` produces the three separated
moments. -/
theorem intervalIntegral_mixedKernel_inner {n : ℕ} (hn : 1 ≤ n)
    (u v x : ℝ) :
    (∫ y in u..v, mixedKernel n x y) =
      x ^ (n - 1) * (∫ y in u..v, y ^ (n + 1)) +
        x ^ (n + 1) * (∫ y in u..v, y ^ (n - 1)) -
          2 * x ^ n * (∫ y in u..v, y ^ n) := by
  simp_rw [mixedKernel_expand hn]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_const_mul]
  · exact (by fun_prop : Continuous (fun y : ℝ =>
      x ^ (n - 1) * y ^ (n + 1))).intervalIntegrable u v
  · exact (by fun_prop : Continuous (fun y : ℝ =>
      x ^ (n + 1) * y ^ (n - 1))).intervalIntegrable u v
  · exact (by fun_prop : Continuous (fun y : ℝ =>
      x ^ (n - 1) * y ^ (n + 1) +
        x ^ (n + 1) * y ^ (n - 1))).intervalIntegrable u v
  · exact (by fun_prop : Continuous (fun y : ℝ =>
      2 * x ^ n * y ^ n)).intervalIntegrable u v

/-- Double integral of the mixed kernel, before division by the two interval
lengths. -/
noncomputable def mixedKernelIntegral (u v : ℝ) (n : ℕ) : ℝ :=
  ∫ x in v..1, ∫ y in u..v, mixedKernel n x y

theorem mixedKernelIntegral_eq_products {n : ℕ} (hn : 1 ≤ n) (u v : ℝ) :
    mixedKernelIntegral u v n =
      (∫ x in v..1, x ^ (n - 1)) * (∫ y in u..v, y ^ (n + 1)) +
        (∫ x in v..1, x ^ (n + 1)) * (∫ y in u..v, y ^ (n - 1)) -
          2 * (∫ x in v..1, x ^ n) * (∫ y in u..v, y ^ n) := by
  unfold mixedKernelIntegral
  simp_rw [intervalIntegral_mixedKernel_inner hn]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul]
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      x ^ (n - 1) * (∫ y in u..v, y ^ (n + 1)))).intervalIntegrable v 1
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      x ^ (n + 1) * (∫ y in u..v, y ^ (n - 1)))).intervalIntegrable v 1
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      x ^ (n - 1) * (∫ y in u..v, y ^ (n + 1)) +
        x ^ (n + 1) * (∫ y in u..v, y ^ (n - 1)))).intervalIntegrable v 1
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      2 * x ^ n * (∫ y in u..v, y ^ n))).intervalIntegrable v 1

theorem uniformMoment_one_eq_intervalAverage {v : ℝ} (hv1 : v ≠ 1) (m : ℕ) :
    uniformMoment 1 v m = (∫ x in v..1, x ^ m) / (1 - v) := by
  rw [uniformMoment_comm]
  exact uniformMoment_eq_intervalIntegral_div hv1 m

/-- Algebraic identification of the mixed term with its nonnegative double
integral. -/
theorem mixedUniformCross_eq_kernelIntegral {u v : ℝ} (huv : u ≠ v)
    (hv1 : v ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    mixedUniformCross u v n =
      mixedKernelIntegral u v n / ((1 - v) * (v - u)) := by
  unfold mixedUniformCross
  rw [uniformMoment_one_eq_intervalAverage hv1,
    uniformMoment_one_eq_intervalAverage hv1,
    uniformMoment_one_eq_intervalAverage hv1,
    uniformMoment_eq_intervalIntegral_div huv,
    uniformMoment_eq_intervalIntegral_div huv,
    uniformMoment_eq_intervalIntegral_div huv,
    mixedKernelIntegral_eq_products hn]
  have h₁ : 1 - v ≠ 0 := sub_ne_zero.mpr hv1.symm
  have h₂ : v - u ≠ 0 := sub_ne_zero.mpr huv.symm
  field_simp [h₁, h₂]

theorem mixedKernelIntegral_nonneg {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv1 : v ≤ 1) (n : ℕ) : 0 ≤ mixedKernelIntegral u v n := by
  unfold mixedKernelIntegral
  apply intervalIntegral.integral_nonneg hv1
  intro x hx
  apply intervalIntegral.integral_nonneg huv
  intro y hy
  exact mixedKernel_nonneg (hu.trans (huv.trans hx.1)) (hu.trans hy.1)

/-- Consequently the algebraic mixed term is nonnegative on ordered,
nondegenerate intervals. -/
theorem mixedUniformCross_nonneg {u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hv1 : v < 1) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ mixedUniformCross u v n := by
  rw [mixedUniformCross_eq_kernelIntegral huv.ne hv1.ne hn]
  exact div_nonneg (mixedKernelIntegral_nonneg hu huv.le hv1.le n)
    (mul_nonneg (sub_nonneg.mpr hv1.le) (sub_nonneg.mpr huv.le))

/-- Integrate any pointwise estimate of the form
`mixedKernel n x y ≤ d * x^(n+1)`. -/
theorem mixedKernelIntegral_le_of_pointwise {u v d : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (huv : u ≤ v) (hv1 : v ≤ 1)
    (hpoint : ∀ x ∈ Set.Icc v 1, ∀ y ∈ Set.Icc u v,
      mixedKernel n x y ≤ d * x ^ (n + 1)) :
    mixedKernelIntegral u v n ≤
      (v - u) * d * (∫ x in v..1, x ^ (n + 1)) := by
  have hinner : ∀ x ∈ Set.Icc v 1,
      (∫ y in u..v, mixedKernel n x y) ≤ (v - u) * (d * x ^ (n + 1)) := by
    intro x hx
    have hkint : IntervalIntegrable (fun y : ℝ => mixedKernel n x y)
        MeasureTheory.volume u v :=
      (by unfold mixedKernel; fun_prop :
        Continuous (fun y : ℝ => mixedKernel n x y)).intervalIntegrable u v
    have hcint : IntervalIntegrable (fun _y : ℝ => d * x ^ (n + 1))
        MeasureTheory.volume u v := intervalIntegrable_const
    have hi := intervalIntegral.integral_mono_on huv hkint hcint (hpoint x hx)
    convert hi using 1
    simp [intervalIntegral.integral_const]
    ring
  have hinnerContinuous : Continuous (fun x : ℝ =>
      ∫ y in u..v, mixedKernel n x y) := by
    have hfun : (fun x : ℝ => ∫ y in u..v, mixedKernel n x y) =
        (fun x : ℝ =>
          x ^ (n - 1) * (∫ y in u..v, y ^ (n + 1)) +
            x ^ (n + 1) * (∫ y in u..v, y ^ (n - 1)) -
              2 * x ^ n * (∫ y in u..v, y ^ n)) := by
      funext x
      exact intervalIntegral_mixedKernel_inner hn u v x
    rw [hfun]
    fun_prop
  unfold mixedKernelIntegral
  have hinnerInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in u..v, mixedKernel n x y) MeasureTheory.volume v 1 :=
    hinnerContinuous.intervalIntegrable v 1
  have hrhsInt : IntervalIntegrable (fun x : ℝ =>
      (v - u) * (d * x ^ (n + 1))) MeasureTheory.volume v 1 :=
    (by fun_prop : Continuous (fun x : ℝ =>
      (v - u) * (d * x ^ (n + 1)))).intervalIntegrable v 1
  have hi := intervalIntegral.integral_mono_on hv1 hinnerInt hrhsInt hinner
  convert hi using 1
  simp only [intervalIntegral.integral_const_mul, mul_assoc]

theorem mixedKernelIntegral_le_v {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv1 : v ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    mixedKernelIntegral u v n ≤
      (v - u) * v ^ (n - 1) * (∫ x in v..1, x ^ (n + 1)) := by
  apply mixedKernelIntegral_le_of_pointwise hn huv hv1
  intro x hx y hy
  exact mixedKernel_le_v hn (hu.trans (huv.trans hx.1)) (hu.trans hy.1)
    (hy.2.trans hx.1) hy.2

theorem mixedKernelIntegral_le_crossCoefficient {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hv1 : v ≤ 1) {n : ℕ} (hn : 2 ≤ n) :
    mixedKernelIntegral u v n ≤
      (v - u) * crossCoefficient n * (∫ x in v..1, x ^ (n + 1)) := by
  apply mixedKernelIntegral_le_of_pointwise (by omega) huv hv1
  intro x hx y hy
  exact mixedKernel_le_crossCoefficient hn (hu.trans (huv.trans hx.1)) hx.2
    (hu.trans hy.1) (hy.2.trans hx.1)

theorem mixedUniformCross_le_of_kernelIntegral_bound
    {u v d : ℝ} (huv : u < v) (hv1 : v < 1) {n : ℕ} (hn : 1 ≤ n)
    (hbound : mixedKernelIntegral u v n ≤
      (v - u) * d * (∫ x in v..1, x ^ (n + 1))) :
    mixedUniformCross u v n ≤ d * uniformMoment 1 v (n + 1) := by
  rw [mixedUniformCross_eq_kernelIntegral huv.ne hv1.ne hn,
    uniformMoment_one_eq_intervalAverage hv1.ne]
  have hden : 0 < (1 - v) * (v - u) :=
    mul_pos (sub_pos.mpr hv1) (sub_pos.mpr huv)
  calc
    mixedKernelIntegral u v n / ((1 - v) * (v - u)) ≤
        ((v - u) * d * (∫ x in v..1, x ^ (n + 1))) /
          ((1 - v) * (v - u)) :=
      (div_le_div_iff_of_pos_right hden).mpr hbound
    _ = d * ((∫ x in v..1, x ^ (n + 1)) / (1 - v)) := by
      have h₁ : 1 - v ≠ 0 := sub_ne_zero.mpr hv1.ne'
      have h₂ : v - u ≠ 0 := sub_ne_zero.mpr huv.ne.symm
      field_simp [h₁, h₂]

/-- Complete mixed-term estimate from the manuscript. -/
theorem mixedUniformCross_bounds {u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (hv1 : v < 1) {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ mixedUniformCross u v n ∧
      mixedUniformCross u v n ≤
        min (v ^ (n - 1)) (crossCoefficient n) * uniformMoment 1 v (n + 1) := by
  have hn1 : 1 ≤ n := by omega
  refine ⟨mixedUniformCross_nonneg hu huv hv1 hn1, ?_⟩
  have hlow := mixedUniformCross_le_of_kernelIntegral_bound
    (n := n) (d := v ^ (n - 1)) huv hv1 hn1
    (mixedKernelIntegral_le_v hu huv.le hv1.le hn1)
  have hhigh := mixedUniformCross_le_of_kernelIntegral_bound
    (n := n) (d := crossCoefficient n) huv hv1 hn1
    (mixedKernelIntegral_le_crossCoefficient hu huv.le hv1.le hn)
  rw [min_mul_of_nonneg _ _ (uniformMoment_nonneg (by norm_num) (hu.trans huv.le) _)]
  exact le_min hlow hhigh

/-- When the inner interval collapses, only the outer kernel integral
remains. -/
noncomputable def mixedKernelSelfIntegral (v : ℝ) (n : ℕ) : ℝ :=
  ∫ x in v..1, mixedKernel n x v

theorem mixedKernelSelfIntegral_eq_products {n : ℕ} (hn : 1 ≤ n) (v : ℝ) :
    mixedKernelSelfIntegral v n =
      v ^ (n + 1) * (∫ x in v..1, x ^ (n - 1)) +
        v ^ (n - 1) * (∫ x in v..1, x ^ (n + 1)) -
          2 * v ^ n * (∫ x in v..1, x ^ n) := by
  unfold mixedKernelSelfIntegral
  simp_rw [mixedKernel_expand hn]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul]
    ring
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      x ^ (n - 1) * v ^ (n + 1))).intervalIntegrable v 1
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      x ^ (n + 1) * v ^ (n - 1))).intervalIntegrable v 1
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      x ^ (n - 1) * v ^ (n + 1) +
        x ^ (n + 1) * v ^ (n - 1))).intervalIntegrable v 1
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      2 * x ^ n * v ^ n)).intervalIntegrable v 1

theorem mixedUniformCross_self_eq_kernelIntegral {v : ℝ} (hv1 : v ≠ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    mixedUniformCross v v n = mixedKernelSelfIntegral v n / (1 - v) := by
  unfold mixedUniformCross
  simp only [uniformMoment_self]
  rw [uniformMoment_one_eq_intervalAverage hv1,
    uniformMoment_one_eq_intervalAverage hv1,
    uniformMoment_one_eq_intervalAverage hv1,
    mixedKernelSelfIntegral_eq_products hn]
  have hden : 1 - v ≠ 0 := sub_ne_zero.mpr hv1.symm
  field_simp [hden]

theorem mixedKernelSelfIntegral_nonneg {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (n : ℕ) : 0 ≤ mixedKernelSelfIntegral v n := by
  unfold mixedKernelSelfIntegral
  apply intervalIntegral.integral_nonneg hv1
  intro x hx
  exact mixedKernel_nonneg (hv.trans hx.1) hv

theorem mixedKernelSelfIntegral_le_of_pointwise {v d : ℝ} {n : ℕ}
    (hv1 : v ≤ 1)
    (hpoint : ∀ x ∈ Set.Icc v 1, mixedKernel n x v ≤ d * x ^ (n + 1)) :
    mixedKernelSelfIntegral v n ≤ d * (∫ x in v..1, x ^ (n + 1)) := by
  unfold mixedKernelSelfIntegral
  have hkint : IntervalIntegrable (fun x : ℝ => mixedKernel n x v)
      MeasureTheory.volume v 1 :=
    (by unfold mixedKernel; fun_prop :
      Continuous (fun x : ℝ => mixedKernel n x v)).intervalIntegrable v 1
  have hdint : IntervalIntegrable (fun x : ℝ => d * x ^ (n + 1))
      MeasureTheory.volume v 1 :=
    (by fun_prop : Continuous (fun x : ℝ => d * x ^ (n + 1))).intervalIntegrable v 1
  have hi := intervalIntegral.integral_mono_on hv1 hkint hdint hpoint
  simpa only [intervalIntegral.integral_const_mul] using hi

theorem mixedUniformCross_self_bounds {v : ℝ} (hv : 0 ≤ v) (hv1 : v < 1)
    {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ mixedUniformCross v v n ∧
      mixedUniformCross v v n ≤
        min (v ^ (n - 1)) (crossCoefficient n) * uniformMoment 1 v (n + 1) := by
  have hn1 : 1 ≤ n := by omega
  have hnonneg : 0 ≤ mixedUniformCross v v n := by
    rw [mixedUniformCross_self_eq_kernelIntegral hv1.ne hn1]
    exact div_nonneg (mixedKernelSelfIntegral_nonneg hv hv1.le n) (sub_nonneg.mpr hv1.le)
  have hlowKernel : mixedKernelSelfIntegral v n ≤
      v ^ (n - 1) * (∫ x in v..1, x ^ (n + 1)) := by
    apply mixedKernelSelfIntegral_le_of_pointwise hv1.le
    intro x hx
    exact mixedKernel_le_v hn1 (hv.trans hx.1) hv hx.1 le_rfl
  have hhighKernel : mixedKernelSelfIntegral v n ≤
      crossCoefficient n * (∫ x in v..1, x ^ (n + 1)) := by
    apply mixedKernelSelfIntegral_le_of_pointwise hv1.le
    intro x hx
    exact mixedKernel_le_crossCoefficient hn (hv.trans hx.1) hx.2 hv hx.1
  have htoMoment : ∀ d : ℝ,
      mixedKernelSelfIntegral v n ≤ d * (∫ x in v..1, x ^ (n + 1)) →
      mixedUniformCross v v n ≤ d * uniformMoment 1 v (n + 1) := by
    intro d hd
    rw [mixedUniformCross_self_eq_kernelIntegral hv1.ne hn1,
      uniformMoment_one_eq_intervalAverage hv1.ne]
    calc
      mixedKernelSelfIntegral v n / (1 - v) ≤
          (d * (∫ x in v..1, x ^ (n + 1))) / (1 - v) :=
        (div_le_div_iff_of_pos_right (sub_pos.mpr hv1)).mpr hd
      _ = d * ((∫ x in v..1, x ^ (n + 1)) / (1 - v)) := by ring
  refine ⟨hnonneg, ?_⟩
  rw [min_mul_of_nonneg _ _ (uniformMoment_nonneg (by norm_num) hv _)]
  exact le_min (htoMoment _ hlowKernel) (htoMoment _ hhighKernel)

/-- With the mixed estimate discharged, the scalar transition tail is the
only remaining hypothesis in the strict interior of the root simplex. -/
theorem normalizedComplete_logConvex_of_transitionTail_strict
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv1 : v < 1)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) {n : ℕ} (hn : 6 ≤ n)
    (htail : LargeTransitionTail n) :
    normalizedComplete u v n ^ 2 ≤
      normalizedComplete u v (n - 1) * normalizedComplete u v (n + 1) := by
  have hmixed := mixedUniformCross_bounds hu huv hv1 (by omega : 2 ≤ n)
  have hu1 : u ≠ 1 := by
    have hv0 : 0 ≤ v := hu.trans huv.le
    intro hueq
    subst u
    have hsqrtv := Real.sqrt_nonneg v
    norm_num at hroot
    nlinarith
  exact normalizedComplete_logConvex_of_transitionTail
    hu (hu.trans huv.le) hv1.le huv.le hroot hn hu1 htail hmixed.1 hmixed.2

theorem normalizedComplete_logConvex_of_transitionTail_self
    {v : ℝ} (hv : 0 ≤ v) (hv1 : v < 1)
    (hroot : Real.sqrt v + Real.sqrt v ≤ 1) {n : ℕ} (hn : 6 ≤ n)
    (htail : LargeTransitionTail n) :
    normalizedComplete v v n ^ 2 ≤
      normalizedComplete v v (n - 1) * normalizedComplete v v (n + 1) := by
  have hmixed := mixedUniformCross_self_bounds hv hv1 (by omega : 2 ≤ n)
  exact normalizedComplete_logConvex_of_transitionTail
    hv hv hv1.le le_rfl hroot hn hv1.ne htail hmixed.1 hmixed.2

@[simp] theorem diagonal_zero_one (n : ℕ) : diagonal 0 1 n = 1 := by
  induction n with
  | zero => simp
  | succ n _ih => rw [diagonal_succ]; simp

@[simp] theorem complete3_zero_one (n : ℕ) : complete3 0 1 n = n + 1 := by
  unfold complete3
  simp

@[simp] theorem normalizedComplete_zero_one (n : ℕ) :
    normalizedComplete 0 1 n = 1 := by
  unfold normalizedComplete
  rw [complete3_zero_one]
  field_simp

theorem normalizedComplete_logConvex_zero_one (n : ℕ) :
    normalizedComplete 0 1 n ^ 2 ≤
      normalizedComplete 0 1 (n - 1) * normalizedComplete 0 1 (n + 1) := by
  simp

/-- Boundary-inclusive large-index assembly.  Thus after this file the only
remaining substantive hypothesis is `LargeTransitionTail`. -/
theorem normalizedComplete_logConvex_of_transitionTail_all
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv1 : v ≤ 1)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) {n : ℕ} (hn : 6 ≤ n)
    (htail : LargeTransitionTail n) :
    normalizedComplete u v n ^ 2 ≤
      normalizedComplete u v (n - 1) * normalizedComplete u v (n + 1) := by
  rcases huv.eq_or_lt with rfl | huvlt
  · by_cases huone : u = 1
    · subst u
      norm_num at hroot
    · exact normalizedComplete_logConvex_of_transitionTail_self hu
        (lt_of_le_of_ne hv1 huone) hroot hn htail
  · by_cases hvone : v = 1
    · subst v
      have hsqrtu0 : Real.sqrt u = 0 := by
        have hsqrtu := Real.sqrt_nonneg u
        norm_num at hroot
        linarith
      have hu0 : u = 0 := by
        have hsquare := Real.sq_sqrt hu
        nlinarith
      subst u
      exact normalizedComplete_logConvex_zero_one n
    · exact normalizedComplete_logConvex_of_transitionTail_strict hu huvlt
        (lt_of_le_of_ne hv1 hvone) hroot hn htail

end SSP.K3CyclicRealTail
