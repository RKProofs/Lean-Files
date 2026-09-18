import SSPLean.AbsorptionLaw
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The third moment of the finite-CTMC absorption law

This file continues `SSPLean.AbsorptionLaw` by proving the concrete identity

`E_i[X^3] = 6 (N^3 𝟙)_i`, where `N = (I - Q)⁻¹`.

Keeping this development in a separate module avoids changing the already stable first- and
second-moment interface while the order-three renewal bridge is assembled.
-/

open scoped Matrix.Norms.Operator
open NormedSpace Matrix SSP.Semigroup SSP.Survival Set Filter Topology MeasureTheory

set_option autoImplicit false

namespace SSP.Law

/-- The cubic weighted layer-cake identity, using `∫₀ˣ 3t² dt = x³`. -/
theorem lintegral_cube_eq {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) (i : Fin s) :
    (∫⁻ x, ENNReal.ofReal ((id x)^3) ∂(survivalStieltjes Q hQ hrow i).measure)
      = ∫⁻ t in Ioi (0 : ℝ),
          (survivalStieltjes Q hQ hrow i).measure {a : ℝ | t < id a}
            * ENNReal.ofReal (3 * t^2) := by
  have hg : ∀ t : ℝ, t > 0 → IntervalIntegrable (fun u => 3 * u^2) volume 0 t :=
    fun t _ => (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 t
  have hgnn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ 3 * t^2 := by
    exact Filter.Eventually.of_forall fun t => mul_nonneg (by norm_num) (sq_nonneg t)
  have hlc := lintegral_comp_eq_lintegral_meas_lt_mul
    (survivalStieltjes Q hQ hrow i).measure (ae_nonneg Q hQ hrow i) aemeasurable_id hg hgnn
  rw [← hlc]
  refine lintegral_congr fun x => ?_
  congr 1
  rw [intervalIntegral.integral_const_mul, integral_pow]
  ring

/-- The twice-integrated by-parts antiderivative for `t² · surv(t)`.

`H₂(t) = -t² S_{N𝟙}(t) - 2t S_{N²𝟙}(t) - 2 S_{N³𝟙}(t)` has derivative
`t² S_𝟙(t)`.
-/
theorem hasDerivAt_squared_weighted_antiderivative {s : ℕ}
    (Q : Matrix (Fin s) (Fin s) ℝ) (hu : IsUnit (1 - Q)) (i : Fin s) (t : ℝ) :
    HasDerivAt (fun u : ℝ =>
        -((u * u) * ((NormedSpace.exp (u • (Q - 1))).mulVec
          ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i)
        - 2 * (u * ((NormedSpace.exp (u • (Q - 1))).mulVec
          ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i)
        - 2 * ((NormedSpace.exp (u • (Q - 1))).mulVec
          ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec
            ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ)))))) i)
      ((t * t) * ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1 : ℝ))) i) t := by
  have h1 := hasDerivAt_antiderivative_gen Q hu (fun _ => (1 : ℝ)) i t
  have h2 := hasDerivAt_antiderivative_gen Q hu
    ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ))) i t
  have h3 := hasDerivAt_antiderivative_gen Q hu
    ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i t
  have hsq := (hasDerivAt_id t).mul (hasDerivAt_id t)
  change HasDerivAt (fun u : ℝ => u * u) (1 * t + t * 1) t at hsq
  have hp1 := hsq.mul h1
  change HasDerivAt
      (fun u : ℝ => (u * u) * ((NormedSpace.exp (u • (Q - 1))).mulVec
        ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i)
      ((1 * t + t * 1) * ((NormedSpace.exp (t • (Q - 1))).mulVec
          ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i
        + (t * t) * (-((NormedSpace.exp (t • (Q - 1))).mulVec
          (fun _ => (1 : ℝ))) i)) t at hp1
  have hp2 := (hasDerivAt_id t).mul h2
  change HasDerivAt
      (fun u : ℝ => u * ((NormedSpace.exp (u • (Q - 1))).mulVec
        ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i)
      (1 * ((NormedSpace.exp (t • (Q - 1))).mulVec
          ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i
        + t * (-((NormedSpace.exp (t • (Q - 1))).mulVec
          ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i)) t at hp2
  have hfin := hp1.neg.sub (hp2.const_mul 2) |>.sub (h3.const_mul 2)
  have hval :
      -((1 * t + t * 1) * ((NormedSpace.exp (t • (Q - 1))).mulVec
          ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i
        + (t * t) * (-((NormedSpace.exp (t • (Q - 1))).mulVec
          (fun _ => (1 : ℝ))) i))
      - 2 * (1 * ((NormedSpace.exp (t • (Q - 1))).mulVec
          ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i
        + t * (-((NormedSpace.exp (t • (Q - 1))).mulVec
          ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i))
      - 2 * (-((NormedSpace.exp (t • (Q - 1))).mulVec
          ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i)
      = (t * t) * ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1 : ℝ))) i := by
    ring
  rw [← hval]
  exact hfin

/-! ## Quadratically weighted exponential decay -/

/-- `t² e^{-ct} → 0` when `c > 0`. -/
theorem tendsto_sq_mul_exp_decay (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ => (t * t) * Real.exp (-(t * c)))
      Filter.atTop (nhds 0) := by
  have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have hcomp : Filter.Tendsto (fun t : ℝ => t * c) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hc Filter.tendsto_id
  have h1 := hbase.comp hcomp
  have h2 : Filter.Tendsto
      (fun t : ℝ => (c⁻¹ * c⁻¹) * ((t * c)^2 * Real.exp (-(t * c))))
      Filter.atTop (nhds ((c⁻¹ * c⁻¹) * 0)) := h1.const_mul _
  rw [mul_zero] at h2
  refine h2.congr fun t => ?_
  field_simp [hc.ne']

/-- `(t² exp(t(Q-I))y)_i → 0`, uniformly dominated by a quadratic times an exponential. -/
theorem tendsto_sq_mul_survival_zero {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (y : Fin s → ℝ) (i : Fin s) :
    Filter.Tendsto
      (fun t : ℝ => (t * t) * ((NormedSpace.exp (t • (Q - 1))).mulVec y) i)
      Filter.atTop (nhds 0) := by
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hbound : ∀ᶠ t : ℝ in Filter.atTop,
      ‖(t * t) * ((NormedSpace.exp (t • (Q - 1))).mulVec y) i‖
        ≤ ((t * t) * Real.exp (-(t * (1 - θ)))) * ‖y‖ := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht ht)]
    have h := (norm_le_pi_norm ((NormedSpace.exp (t • (Q - 1))).mulVec y) i).trans
      (Matrix.linfty_opNorm_mulVec _ y)
    calc
      (t * t) * ‖((NormedSpace.exp (t • (Q - 1))).mulVec y) i‖
          ≤ (t * t) * (‖NormedSpace.exp (t • (Q - 1))‖ * ‖y‖) :=
            mul_le_mul_of_nonneg_left h (mul_nonneg ht ht)
      _ ≤ (t * t) * (Real.exp (-(t * (1 - θ))) * ‖y‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg ht ht)
            exact mul_le_mul_of_nonneg_right
              (norm_exp_smul_sub_one_le Q θ t hnorm ht) (norm_nonneg _)
      _ = ((t * t) * Real.exp (-(t * (1 - θ)))) * ‖y‖ := by ring
  have hlim : Filter.Tendsto
      (fun t : ℝ => ((t * t) * Real.exp (-(t * (1 - θ)))) * ‖y‖)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_sq_mul_exp_decay (1 - θ) h1θ).mul_const ‖y‖
  exact squeeze_zero_norm' hbound hlim

/-- The cubic by-parts antiderivative tends to zero at `+∞`. -/
theorem tendsto_squared_weighted_antiderivative {s : ℕ}
    (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    Filter.Tendsto (fun u : ℝ =>
        -((u * u) * ((NormedSpace.exp (u • (Q - 1))).mulVec
          ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i)
        - 2 * (u * ((NormedSpace.exp (u • (Q - 1))).mulVec
          ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i)
        - 2 * ((NormedSpace.exp (u • (Q - 1))).mulVec
          ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec
            ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ)))))) i)
      Filter.atTop (nhds 0) := by
  have h1 := tendsto_sq_mul_survival_zero Q θ hnorm hθ
    ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ))) i
  have h2 := tendsto_mul_survival_zero Q θ hnorm hθ
    ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i
  have h3 := SSP.Semigroup.tendsto_survival_zero Q θ hnorm hθ
    ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec
      ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i
  simpa using (h1.neg).sub (h2.const_mul 2) |>.sub (h3.const_mul 2)

/-- A convenient exponential domination for `t²e^{-ct}` on the nonnegative ray. -/
theorem sq_mul_exp_bound (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t) :
    t^2 * Real.exp (-c * t)
      ≤ ((16 / c^2) * Real.exp (-2)) * Real.exp (-(c / 2) * t) := by
  have hu : 0 ≤ (c / 4) * t := by positivity
  have hkey := mul_exp_le ((c / 4) * t) hu
  have hsq : (((c / 4) * t) * Real.exp (-((c / 4) * t)))^2
      ≤ (Real.exp (-1))^2 := by
    exact pow_le_pow_left₀ (mul_nonneg hu (Real.exp_pos _).le) hkey 2
  have hlhs : t^2 * Real.exp (-c * t)
      = (16 / c^2) *
          ((((c / 4) * t) * Real.exp (-((c / 4) * t)))^2) *
          Real.exp (-(c / 2) * t) := by
    have hex : (Real.exp (-(t * c / 4)))^2 * Real.exp (-(t * c / 2))
        = Real.exp (-(t * c)) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [pow_two] at hex ⊢
    field_simp [hc.ne']
    rw [← hex]
    ring
  rw [hlhs]
  have hcoef : 0 ≤ 16 / c^2 := by positivity
  have hexp : 0 ≤ Real.exp (-(c / 2) * t) := (Real.exp_pos _).le
  calc
    (16 / c^2) *
          ((((c / 4) * t) * Real.exp (-((c / 4) * t)))^2) *
          Real.exp (-(c / 2) * t)
        ≤ (16 / c^2) * (Real.exp (-1))^2 * Real.exp (-(c / 2) * t) := by
          gcongr
    _ = ((16 / c^2) * Real.exp (-2)) * Real.exp (-(c / 2) * t) := by
          have he : (Real.exp (-1))^2 = Real.exp (-2) := by
            rw [pow_two, ← Real.exp_add]
            norm_num
          rw [he]

/-- `t² · surv(t)` is integrable on `(0,∞)`. -/
theorem integrableOn_squared_weighted {s : ℕ}
    (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => t^2 * ((NormedSpace.exp (t • (Q - 1))).mulVec
        (fun _ => (1 : ℝ))) i)
      (Ioi 0) MeasureTheory.volume := by
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hhalf : (0 : ℝ) < (1 - θ) / 2 := by linarith
  have hcont : Continuous
      (fun t : ℝ => t^2 * ((NormedSpace.exp (t • (Q - 1))).mulVec
        (fun _ => (1 : ℝ))) i) :=
    (continuous_id.pow 2).mul (continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_mulVec_exp (Q - 1) (fun _ => (1 : ℝ)) i t).continuousAt)
  set K : ℝ := ((16 / (1 - θ)^2) * Real.exp (-2)) *
    ‖(fun _ => (1 : ℝ) : Fin s → ℝ)‖ with hK
  have hdom : MeasureTheory.IntegrableOn
      (fun t : ℝ => K * Real.exp (-((1 - θ) / 2) * t)) (Ioi 0) volume :=
    (exp_neg_integrableOn_Ioi 0 hhalf).const_mul K
  refine MeasureTheory.Integrable.mono' hdom hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
  have hs := (norm_le_pi_norm
    ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1 : ℝ))) i).trans
      (Matrix.linfty_opNorm_mulVec _ (fun _ => (1 : ℝ)))
  calc
    t^2 * ‖((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1 : ℝ))) i‖
        ≤ t^2 * (Real.exp (-(t * (1 - θ))) *
            ‖(fun _ => (1 : ℝ) : Fin s → ℝ)‖) := by
          refine mul_le_mul_of_nonneg_left (hs.trans ?_) (sq_nonneg t)
          exact mul_le_mul_of_nonneg_right
            (norm_exp_smul_sub_one_le Q θ t hnorm ht0) (norm_nonneg _)
    _ = (t^2 * Real.exp (-(1 - θ) * t)) *
          ‖(fun _ => (1 : ℝ) : Fin s → ℝ)‖ := by
          rw [show -(t * (1 - θ)) = -(1 - θ) * t by ring]
          ring
    _ ≤ (((16 / (1 - θ)^2) * Real.exp (-2)) *
          Real.exp (-((1 - θ) / 2) * t)) *
          ‖(fun _ => (1 : ℝ) : Fin s → ℝ)‖ :=
      mul_le_mul_of_nonneg_right (sq_mul_exp_bound (1 - θ) t h1θ ht0) (norm_nonneg _)
    _ = K * Real.exp (-((1 - θ) / 2) * t) := by rw [hK]; ring

/-- The quadratically weighted survival integral is `2(N³𝟙)ᵢ`. -/
theorem integral_squared_weighted {s : ℕ}
    (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hu : IsUnit (1 - Q)) (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    (∫ t in Ioi (0 : ℝ),
        t^2 * ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1 : ℝ))) i)
      = 2 * ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec
        ((1 - Q)⁻¹.mulVec (fun _ => 1)))) i := by
  set H := fun u : ℝ =>
    -((u * u) * ((NormedSpace.exp (u • (Q - 1))).mulVec
      ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i)
    - 2 * (u * ((NormedSpace.exp (u • (Q - 1))).mulVec
      ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i)
    - 2 * ((NormedSpace.exp (u • (Q - 1))).mulVec
      ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec
        ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ)))))) i with hHdef
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt H
      (t^2 * ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1 : ℝ))) i) t := by
    intro t _
    simpa [H, pow_two] using hasDerivAt_squared_weighted_antiderivative Q hu i t
  have hcont : ContinuousWithinAt H (Ici 0) 0 := by
    exact ((hasDerivAt_squared_weighted_antiderivative Q hu i 0).continuousAt).continuousWithinAt
  have hint := integrableOn_squared_weighted Q θ hnorm hθ i
  have hlim : Filter.Tendsto H Filter.atTop (nhds 0) :=
    tendsto_squared_weighted_antiderivative Q θ hnorm hθ i
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hH0 : H 0 = -2 * ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec
      ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i := by
    simp [hHdef, NormedSpace.exp_zero]
  rw [hH0] at hftc
  linarith [hftc]

/-! ## The third moment as a genuine expectation -/

/-- The cubic layer-cake tail integrand is `ofReal (3 t² surv(t))`. -/
theorem lintegral_cube_tail {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    (∫⁻ t in Ioi (0 : ℝ),
        (survivalStieltjes Q hQ hrow i).measure {a : ℝ | t < id a}
          * ENNReal.ofReal (3 * t^2))
      = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
          (3 * (t^2 * ((NormedSpace.exp (t • (Q - 1))).mulVec
            (fun _ => (1 : ℝ))) i)) := by
  refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [tail_set_id t,
    measure_Ioi_eq_survival Q θ hQ hrow hnorm hθ i t (le_of_lt ht),
    ← ENNReal.ofReal_mul (survival_nonneg Q hQ t (le_of_lt ht) i)]
  congr 1
  ring

/-- **Concrete third-moment formula for the finite-CTMC absorption law.**

For `N = (I-Q)⁻¹`, the absorption time started at `i` satisfies
`E_i[X³] = 6 (N³𝟙)_i`.
-/
theorem third_moment_eq {s : ℕ}
    (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hu : IsUnit (1 - Q)) (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    (∫ x, (id x)^3 ∂(survivalStieltjes Q hQ hrow i).measure)
      = 6 * ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec
        ((1 - Q)⁻¹.mulVec (fun _ => 1)))) i := by
  have hae3 : 0 ≤ᵐ[(survivalStieltjes Q hQ hrow i).measure]
      (fun x : ℝ => (id x)^3) := by
    filter_upwards [ae_nonneg Q hQ hrow i] with x hx
    exact pow_nonneg hx 3
  set g := fun t : ℝ => 3 * (t^2 *
    ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1 : ℝ))) i) with hg
  have hgint : IntegrableOn g (Ioi 0) volume := by
    rw [hg]
    exact (integrableOn_squared_weighted Q θ hnorm hθ i).const_mul 3
  have hgae : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hg]
    have hs := survival_nonneg Q hQ t (le_of_lt ht) i
    positivity
  have hgval : (∫ t in Ioi (0 : ℝ), g t)
      = 6 * ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec
        ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i := by
    rw [hg, integral_const_mul, integral_squared_weighted Q θ hu hnorm hθ i]
    ring
  have h1 := lintegral_cube_eq Q hQ hrow i
  rw [lintegral_cube_tail Q θ hQ hrow hnorm hθ i] at h1
  have h2 := ofReal_integral_eq_lintegral_ofReal hgint hgae
  rw [← h2] at h1
  have hint3 : Integrable (fun x : ℝ => (id x)^3)
      (survivalStieltjes Q hQ hrow i).measure := by
    refine ⟨(continuous_id.pow 3).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have heq : (∫⁻ x, ‖(id x)^3‖ₑ ∂(survivalStieltjes Q hQ hrow i).measure)
        = ∫⁻ x, ENNReal.ofReal ((id x)^3)
            ∂(survivalStieltjes Q hQ hrow i).measure := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae3] with x hx
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hx]
    rw [heq, h1]
    exact ENNReal.ofReal_lt_top
  have h3 := ofReal_integral_eq_lintegral_ofReal hint3 hae3
  rw [h1, hgval] at h3
  have hrhs : 0 ≤ 6 * ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec
      ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i := by
    rw [← hgval]
    exact integral_nonneg_of_ae hgae
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hae3) hrhs).mp h3

end SSP.Law
