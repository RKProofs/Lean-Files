import SSPLean.SurvivalMonotone
import SSPLean.MomentBridge

/-!
# The absorption time as a random variable, and its first moment

`SSPLean.SurvivalMonotone` builds the law of the absorption time as a measure `μ` on `ℝ`, via its
CDF.  Taking `X = id` on that space makes `X` a genuine random variable whose survival function is
`μ(Ioi t) = surv(t)`, and Mathlib's layer-cake theorem turns `E[X]` into `∫₀^∞ surv`, which
`SSPLean.SemigroupMoments` evaluates as `(N𝟙)ᵢ`.

This is the step that replaces the probabilistic assumption of `SSPLean.AldousShepp` by a proof.
-/

open scoped Matrix.Norms.Operator
open NormedSpace Matrix SSP.Semigroup SSP.Survival Set Filter Topology MeasureTheory

set_option autoImplicit false

namespace SSP.Law

/-- **The survival function of the law.**  `μ(Ioi x) = surv(x)` for `x ≥ 0`: the tail probability
of the absorption time is exactly `(exp(x(Q−I))𝟙)ᵢ`, which is what identifies `X = id` on this
space as *the* absorption time. -/
theorem measure_Ioi_eq_survival {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) (x : ℝ) (hx : 0 ≤ x) :
    (survivalStieltjes Q hQ hrow i).measure (Ioi x)
      = ENNReal.ofReal (((NormedSpace.exp (x • (Q - 1))).mulVec (fun _ => (1:ℝ))) i) := by
  rw [StieltjesFunction.measure_Ioi _ (cdfF_tendsto_atTop Q θ hnorm hθ i) x]
  congr 1
  change (1:ℝ) - cdfF Q i x = _
  rw [cdfF_eqOn_Ici Q i (mem_Ici.mpr hx)]
  ring

/-- **`X = id` is a.e. nonnegative.**  The law gives no mass to `(−∞,0]`
(`SSP.Survival.measure_Iic_zero`), so although `id` is negative on the left half-line, it is
nonnegative almost everywhere — which is what the layer-cake theorem requires. -/
theorem ae_nonneg {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) (i : Fin s) :
    0 ≤ᵐ[(survivalStieltjes Q hQ hrow i).measure] (id : ℝ → ℝ) := by
  have hz := measure_Iic_zero Q hQ hrow i
  rw [Filter.EventuallyLE, Filter.eventually_iff]
  have hsub : {x : ℝ | ¬ (0 ≤ id x)} ⊆ Iic 0 := by
    intro x hx; simp only [mem_setOf_eq, id, not_le] at hx; exact le_of_lt hx
  have h0 : (survivalStieltjes Q hQ hrow i).measure {x : ℝ | ¬ (0 ≤ id x)} = 0 :=
    measure_mono_null hsub hz
  rw [mem_ae_iff]; convert h0 using 2; ext x; simp [id]

/-- **The layer-cake identity for the law.**  Unconditional — no integrability needed, because
this is the `lintegral` form. -/
theorem lintegral_id_eq {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) (i : Fin s) :
    (∫⁻ x, ENNReal.ofReal (id x) ∂(survivalStieltjes Q hQ hrow i).measure)
      = ∫⁻ t in Ioi 0, (survivalStieltjes Q hQ hrow i).measure {a : ℝ | t < id a} :=
  lintegral_eq_lintegral_meas_lt _ (ae_nonneg Q hQ hrow i) aemeasurable_id

/-- The tail set of `id` above `t` is `Ioi t`. -/
theorem tail_set_id (t : ℝ) : {a : ℝ | t < id a} = Ioi t := by ext a; simp [id]

/-- **The layer-cake right-hand side is the survival integral.**  Combining `tail_set_id` with
`measure_Ioi_eq_survival`, the tail-measure integrand on `(0,∞)` is `ofReal (surv t)`. -/
theorem lintegral_tail_eq_survival {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    (∫⁻ t in Ioi 0, (survivalStieltjes Q hQ hrow i).measure {a : ℝ | t < id a})
      = ∫⁻ t in Ioi (0:ℝ),
          ENNReal.ofReal (((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i) := by
  refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [tail_set_id t, measure_Ioi_eq_survival Q θ hQ hrow hnorm hθ i t (le_of_lt ht)]

/-! ## The first moment, as a genuine expectation

The layer-cake identity is in `ENNReal`; converting to a real Bochner integral needs
integrability of `id`, which is *derived* here rather than assumed: the `lintegral` right-hand
side is finite because `SSP.Semigroup.integrableOn_survival` says the survival function is
integrable on `(0,∞)`.

This is why the `lintegral` form of the layer cake was used above: the real-valued
`Integrable.integral_eq_integral_meas_lt` takes `Integrable id μ` as an input, which is
essentially the finiteness we are trying to establish. -/

/-- The layer-cake integral is finite, because the survival function is integrable. -/
theorem lintegral_finite {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    (∫⁻ x, ENNReal.ofReal (id x) ∂(survivalStieltjes Q hQ hrow i).measure) ≠ ⊤ := by
  rw [lintegral_id_eq Q hQ hrow i, lintegral_tail_eq_survival Q θ hQ hrow hnorm hθ i]
  exact ((integrableOn_survival Q θ hnorm hθ (fun _ => (1:ℝ)) i).lintegral_lt_top).ne

/-- **`X = id` is integrable**: the absorption time has a finite mean. -/
theorem integrable_id {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    Integrable (id : ℝ → ℝ) (survivalStieltjes Q hQ hrow i).measure := by
  refine ⟨aestronglyMeasurable_id, ?_⟩
  rw [HasFiniteIntegral]
  have hae := ae_nonneg Q hQ hrow i
  have heq : (∫⁻ x, ‖id x‖ₑ ∂(survivalStieltjes Q hQ hrow i).measure)
      = ∫⁻ x, ENNReal.ofReal (id x) ∂(survivalStieltjes Q hQ hrow i).measure := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hx]
  rw [heq]
  exact lt_of_le_of_ne le_top (lintegral_finite Q θ hQ hrow hnorm hθ i)

/-- **`E[X] = (N𝟙)ᵢ`.**

The first moment of the absorption time, as the expectation of an honest random variable on an
honest probability space, equals the resolvent entry.  No moment dictionary is assumed: the law is
constructed from the survival function in `SSPLean.SurvivalMonotone`, `X = id` is identified as the
absorption time by `measure_Ioi_eq_survival`, the layer cake converts `E[X]` to `∫₀^∞ surv`, and
`SSP.Semigroup.integral_survival` evaluates that as `(N𝟙)ᵢ`. -/
theorem expectation_eq {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) (hu : IsUnit (1 - Q))
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    (∫ x, id x ∂(survivalStieltjes Q hQ hrow i).measure)
      = ((1 - Q)⁻¹.mulVec (fun _ => 1)) i := by
  have hae := ae_nonneg Q hQ hrow i
  have hint := integrable_id Q θ hQ hrow hnorm hθ i
  have h1 := ofReal_integral_eq_lintegral_ofReal hint hae
  rw [lintegral_id_eq Q hQ hrow i, lintegral_tail_eq_survival Q θ hQ hrow hnorm hθ i] at h1
  have hsint := integrableOn_survival Q θ hnorm hθ (fun _ => (1:ℝ)) i
  have hsae : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun t => ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact survival_nonneg Q hQ t (le_of_lt ht) i
  have h2 := ofReal_integral_eq_lintegral_ofReal hsint hsae
  rw [← h2, integral_survival Q θ hu hnorm hθ i] at h1
  have hN : 0 ≤ ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ))) i := by
    rw [← integral_survival Q θ hu hnorm hθ i]
    exact integral_nonneg_of_ae hsae
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hae) hN).mp h1

/-! ## The second moment

The weighted layer cake with `g(t) = 2t` gives `E[X²] = ∫₀^∞ 2t·surv(t) dt`.  Note this is the
**`t`-weighted** integral, not the `N𝟙`-weighted one — so the integration by parts avoided in
`SSPLean.SemigroupMoments` (where `integral_resolvent` at `y := N𝟙` sufficed) becomes unavoidable
here.  The antiderivative is explicit:

```
  H(t) := −t·(exp(tG)·N𝟙)ᵢ − (exp(tG)·N²𝟙)ᵢ ,     H′(t) = t·surv(t) ,
```

using `d/dt (exp(tG)·Ny)ᵢ = −(exp(tG)·y)ᵢ` twice, so `H(0) = −(N²𝟙)ᵢ` and `H(∞) = 0`. -/

/-- **The weighted layer cake for the law**, with `g(t) = 2t` so that `∫₀^{X} 2t dt = X²`. -/
theorem lintegral_sq_eq {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) (i : Fin s) :
    (∫⁻ x, ENNReal.ofReal ((id x)^2) ∂(survivalStieltjes Q hQ hrow i).measure)
      = ∫⁻ t in Ioi (0:ℝ),
          (survivalStieltjes Q hQ hrow i).measure {a : ℝ | t < id a}
            * ENNReal.ofReal (2*t) := by
  have hg : ∀ t : ℝ, t > 0 → IntervalIntegrable (fun u => 2*u) volume 0 t := fun t _ =>
    (continuous_const.mul continuous_id).intervalIntegrable 0 t
  have hgnn : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ 2*t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    linarith [mem_Ioi.mp ht]
  have hlc := lintegral_comp_eq_lintegral_meas_lt_mul
    (survivalStieltjes Q hQ hrow i).measure (ae_nonneg Q hQ hrow i) aemeasurable_id hg hgnn
  rw [← hlc]
  refine lintegral_congr fun ω => ?_
  congr 1
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/-- **The by-parts antiderivative for the `t`-weighted integral.**
`H(t) = −t(exp(tG)N𝟙)ᵢ − (exp(tG)N²𝟙)ᵢ` satisfies `H′(t) = t·surv(t)`. -/
theorem hasDerivAt_weighted_antiderivative {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hu : IsUnit (1 - Q)) (i : Fin s) (t : ℝ) :
    HasDerivAt (fun u : ℝ =>
        -(u * ((NormedSpace.exp (u • (Q - 1))).mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ)))) i)
        - ((NormedSpace.exp (u • (Q - 1))).mulVec
            ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ))))) i)
      (t * ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i) t := by
  have hA := hasDerivAt_antiderivative_gen Q hu (fun _ => (1:ℝ)) i t
  have hB := hasDerivAt_antiderivative_gen Q hu ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ))) i t
  have hprod : HasDerivAt
      (fun u : ℝ => u * ((NormedSpace.exp (u • (Q - 1))).mulVec
        ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ)))) i)
      (1 * ((NormedSpace.exp (t • (Q - 1))).mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ)))) i
        + t * (-((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i)) t :=
    (hasDerivAt_id t).mul hA
  have hfin := hprod.neg.sub hB
  have hval : -(1 * ((NormedSpace.exp (t • (Q - 1))).mulVec
        ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ)))) i
      + t * (-((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i))
      - (-((NormedSpace.exp (t • (Q - 1))).mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ)))) i)
      = t * ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i := by ring
  rw [← hval]
  exact hfin

/-! ### Decay of the by-parts antiderivative

`H(∞) = 0` needs the `t·(exp(tG)N𝟙)ᵢ` term to vanish, which is polynomial-times-exponential
decay rather than the plain exponential decay of `SSP.Semigroup.tendsto_survival_zero`. -/

/-- `t·e^{−ct} → 0` for `c > 0`. -/
theorem tendsto_mul_exp_decay (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ => t * Real.exp (-(t * c))) Filter.atTop (nhds 0) := by
  have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hcomp : Filter.Tendsto (fun t : ℝ => t * c) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hc Filter.tendsto_id
  have h1 := hbase.comp hcomp
  have h2 : Filter.Tendsto (fun t : ℝ => c⁻¹ * ((t*c)^1 * Real.exp (-(t*c))))
      Filter.atTop (nhds (c⁻¹ * 0)) := h1.const_mul _
  rw [mul_zero] at h2
  refine h2.congr fun t => ?_
  rw [pow_one]; field_simp

/-- `t·(exp(t(Q−I))y)ᵢ → 0`, by squeezing against `t·e^{−t(1−θ)}·‖y‖`. -/
theorem tendsto_mul_survival_zero {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (y : Fin s → ℝ) (i : Fin s) :
    Filter.Tendsto (fun t : ℝ => t * ((NormedSpace.exp (t • (Q - 1))).mulVec y) i)
      Filter.atTop (nhds 0) := by
  have h1θ : (0:ℝ) < 1 - θ := by linarith
  have hbound : ∀ᶠ t : ℝ in Filter.atTop,
      ‖t * ((NormedSpace.exp (t • (Q - 1))).mulVec y) i‖
        ≤ (t * Real.exp (-(t * (1 - θ)))) * ‖y‖ := by
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with t ht
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ht]
    have h := (norm_le_pi_norm ((NormedSpace.exp (t • (Q - 1))).mulVec y) i).trans
      (Matrix.linfty_opNorm_mulVec _ y)
    calc t * ‖((NormedSpace.exp (t • (Q - 1))).mulVec y) i‖
        ≤ t * (‖NormedSpace.exp (t • (Q - 1))‖ * ‖y‖) := mul_le_mul_of_nonneg_left h ht
      _ ≤ t * (Real.exp (-(t * (1 - θ))) * ‖y‖) := by
          refine mul_le_mul_of_nonneg_left ?_ ht
          exact mul_le_mul_of_nonneg_right
            (norm_exp_smul_sub_one_le Q θ t hnorm ht) (norm_nonneg _)
      _ = (t * Real.exp (-(t * (1 - θ)))) * ‖y‖ := by ring
  have hlim : Filter.Tendsto (fun t : ℝ => (t * Real.exp (-(t * (1 - θ)))) * ‖y‖)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_mul_exp_decay (1 - θ) h1θ).mul_const ‖y‖
  exact squeeze_zero_norm' hbound hlim

/-- **`H(∞) = 0`**: both terms of the by-parts antiderivative decay. -/
theorem tendsto_weighted_antiderivative {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    Filter.Tendsto (fun u : ℝ =>
        -(u * ((NormedSpace.exp (u • (Q - 1))).mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ)))) i)
        - ((NormedSpace.exp (u • (Q - 1))).mulVec
            ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ))))) i)
      Filter.atTop (nhds 0) := by
  have h1 := tendsto_mul_survival_zero Q θ hnorm hθ ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ))) i
  have h2 := SSP.Semigroup.tendsto_survival_zero Q θ hnorm hθ
    ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ)))) i
  simpa using (h1.neg).sub h2

/-! ### Integrability of the `t`-weighted survival function

Mathlib has no integrability lemma for `t·e^{−ct}` on a ray, so the dominating bound is built
here: `t·e^{−ct} ≤ (2/c)e^{−1}·e^{−(c/2)t}`, the constant being the exact maximum of
`u·e^{−u}`. -/

/-- `u·e^{−u} ≤ e^{−1}`, from `x + 1 ≤ eˣ` at `x = u − 1`. -/
theorem mul_exp_le (u : ℝ) (_hu : 0 ≤ u) : u * Real.exp (-u) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (u - 1)
  have h2 : u ≤ Real.exp u * Real.exp (-1) := by
    calc u = (u - 1) + 1 := by ring
      _ ≤ Real.exp (u - 1) := h
      _ = Real.exp u * Real.exp (-1) := by rw [← Real.exp_add]; ring_nf
  calc u * Real.exp (-u) ≤ (Real.exp u * Real.exp (-1)) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (-1) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf

/-- `t·e^{−ct} ≤ (2/c)e^{−1}·e^{−(c/2)t}`: split one half of the exponent off and apply
`mul_exp_le` to `u = (c/2)t`. -/
theorem mul_exp_bound (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t) :
    t * Real.exp (-c * t) ≤ ((2/c) * Real.exp (-1)) * Real.exp (-(c/2) * t) := by
  have hu : 0 ≤ (c/2) * t := by positivity
  have hkey := mul_exp_le ((c/2) * t) hu
  have hrw : t * Real.exp (-c * t)
      = (2/c) * (((c/2)*t) * Real.exp (-((c/2)*t))) * Real.exp (-(c/2)*t) := by
    have hex : Real.exp (-((c/2)*t)) * Real.exp (-(c/2)*t) = Real.exp (-c*t) := by
      rw [← Real.exp_add]; ring_nf
    calc t * Real.exp (-c * t)
        = (2/c) * ((c/2)*t) * Real.exp (-c*t) := by field_simp
      _ = (2/c) * ((c/2)*t) * (Real.exp (-((c/2)*t)) * Real.exp (-(c/2)*t)) := by rw [hex]
      _ = (2/c) * (((c/2)*t) * Real.exp (-((c/2)*t))) * Real.exp (-(c/2)*t) := by ring
  rw [hrw]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left hkey (by positivity)

/-- **`t·surv(t)` is integrable on `(0,∞)`.** -/
theorem integrableOn_weighted {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => t * ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i)
      (Ioi 0) MeasureTheory.volume := by
  have h1θ : (0:ℝ) < 1 - θ := by linarith
  have hhalf : (0:ℝ) < (1-θ)/2 := by linarith
  have hcont : Continuous
      (fun t : ℝ => t * ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i) :=
    continuous_id.mul (continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_mulVec_exp (Q - 1) (fun _ => (1:ℝ)) i t).continuousAt)
  set K : ℝ := ((2/(1-θ)) * Real.exp (-1)) * ‖(fun _ => (1:ℝ) : Fin s → ℝ)‖ with hK
  have hdom : MeasureTheory.IntegrableOn
      (fun t : ℝ => K * Real.exp (-((1-θ)/2) * t)) (Ioi 0) MeasureTheory.volume :=
    (exp_neg_integrableOn_Ioi 0 hhalf).const_mul K
  refine MeasureTheory.Integrable.mono' hdom hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0:ℝ) ≤ t := le_of_lt ht
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hs := (norm_le_pi_norm ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i).trans
    (Matrix.linfty_opNorm_mulVec _ (fun _ => (1:ℝ)))
  calc t * ‖((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i‖
      ≤ t * (Real.exp (-(t * (1 - θ))) * ‖(fun _ => (1:ℝ) : Fin s → ℝ)‖) := by
        refine mul_le_mul_of_nonneg_left (hs.trans ?_) ht0
        exact mul_le_mul_of_nonneg_right
          (norm_exp_smul_sub_one_le Q θ t hnorm ht0) (norm_nonneg _)
    _ = (t * Real.exp (-(1-θ) * t)) * ‖(fun _ => (1:ℝ) : Fin s → ℝ)‖ := by
        rw [show -(t * (1 - θ)) = -(1-θ)*t by ring]; ring
    _ ≤ (((2/(1-θ)) * Real.exp (-1)) * Real.exp (-((1-θ)/2) * t))
          * ‖(fun _ => (1:ℝ) : Fin s → ℝ)‖ :=
        mul_le_mul_of_nonneg_right (mul_exp_bound (1-θ) t h1θ ht0) (norm_nonneg _)
    _ = K * Real.exp (-((1-θ)/2) * t) := by rw [hK]; ring

/-- **`∫₀^∞ t·surv(t) dt = (N²𝟙)ᵢ`.**  FTC-2 on the by-parts antiderivative `H`, using
`H(0) = −(N²𝟙)ᵢ` and `H(∞) = 0`. -/
theorem integral_weighted {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hu : IsUnit (1 - Q)) (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    (∫ t in Ioi (0:ℝ), t * ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i)
      = ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => 1))) i := by
  set H := fun u : ℝ =>
    -(u * ((NormedSpace.exp (u • (Q - 1))).mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ)))) i)
    - ((NormedSpace.exp (u • (Q - 1))).mulVec
        ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ))))) i with hHdef
  have hderiv : ∀ t ∈ Ioi (0:ℝ), HasDerivAt H
      (t * ((NormedSpace.exp (t • (Q - 1))).mulVec (fun _ => (1:ℝ))) i) t :=
    fun t _ => hasDerivAt_weighted_antiderivative Q hu i t
  have hcont : ContinuousWithinAt H (Ici 0) 0 :=
    ((hasDerivAt_weighted_antiderivative Q hu i 0).continuousAt).continuousWithinAt
  have hint := integrableOn_weighted Q θ hnorm hθ i
  have hlim : Filter.Tendsto H Filter.atTop (nhds 0) :=
    tendsto_weighted_antiderivative Q θ hnorm hθ i
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hH0 : H 0 = -(((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ)))) i) := by
    simp [hHdef, NormedSpace.exp_zero]
  rw [hH0] at hftc
  linarith [hftc]

/-! ### The second moment, as a genuine expectation -/

/-- The weighted layer-cake tail integrand is `ofReal (2t·surv t)`. -/
theorem lintegral_sq_tail {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    (∫⁻ t in Ioi (0:ℝ),
        (survivalStieltjes Q hQ hrow i).measure {a : ℝ | t < id a} * ENNReal.ofReal (2*t))
      = ∫⁻ t in Ioi (0:ℝ),
          ENNReal.ofReal (2 * (t * ((NormedSpace.exp (t • (Q-1))).mulVec (fun _ => (1:ℝ))) i)) := by
  refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [tail_set_id t, measure_Ioi_eq_survival Q θ hQ hrow hnorm hθ i t (le_of_lt ht),
    ← ENNReal.ofReal_mul (survival_nonneg Q hQ t (le_of_lt ht) i)]
  congr 1; ring

/-- **`E[X²] = 2(N²𝟙)ᵢ`.**

The second moment of the absorption time, as a genuine expectation.  Route: the weighted layer
cake (`lintegral_sq_eq`) with `g(t) = 2t`, the tail identity, then FTC-2 on the by-parts
antiderivative (`integral_weighted`), and finally the `ENNReal → ℝ` conversion.  Integrability of
`X²` is *derived* from finiteness of the layer-cake integral, exactly as for the first moment. -/
theorem second_moment_eq {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ) (θ : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) (hu : IsUnit (1 - Q))
    (hnorm : ‖Q‖ ≤ θ) (hθ : θ < 1) (i : Fin s) :
    (∫ x, (id x)^2 ∂(survivalStieltjes Q hQ hrow i).measure)
      = 2 * ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => 1))) i := by
  -- a.e. nonnegativity of id^2 is automatic
  have hae2 : 0 ≤ᵐ[(survivalStieltjes Q hQ hrow i).measure] (fun x : ℝ => (id x)^2) :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  -- the weighted integrand, on Ioi 0
  set g := fun t : ℝ => 2 * (t * ((NormedSpace.exp (t • (Q-1))).mulVec (fun _ => (1:ℝ))) i) with hg
  have hgint : IntegrableOn g (Ioi 0) volume := by
    rw [hg]; exact (integrableOn_weighted Q θ hnorm hθ i).const_mul 2
  have hgae : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hg]
    have := survival_nonneg Q hQ t (le_of_lt ht) i
    have ht0 : (0:ℝ) ≤ t := le_of_lt ht
    positivity
  -- the value of ∫ g
  have hgval : (∫ t in Ioi (0:ℝ), g t)
      = 2 * ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ)))) i := by
    rw [hg, integral_const_mul, integral_weighted Q θ hu hnorm hθ i]
  -- lintegral chain
  have h1 := lintegral_sq_eq Q hQ hrow i
  rw [lintegral_sq_tail Q θ hQ hrow hnorm hθ i] at h1
  have h2 := ofReal_integral_eq_lintegral_ofReal hgint hgae
  rw [← h2] at h1
  -- integrability of id^2
  have hint2 : Integrable (fun x : ℝ => (id x)^2) (survivalStieltjes Q hQ hrow i).measure := by
    refine ⟨(continuous_id.pow 2).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have heq : (∫⁻ x, ‖(id x)^2‖ₑ ∂(survivalStieltjes Q hQ hrow i).measure)
        = ∫⁻ x, ENNReal.ofReal ((id x)^2) ∂(survivalStieltjes Q hQ hrow i).measure := by
      refine lintegral_congr fun x => ?_
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [heq, h1]
    exact ENNReal.ofReal_lt_top
  have h3 := ofReal_integral_eq_lintegral_ofReal hint2 hae2
  rw [h1] at h3
  rw [hgval] at h3
  have hrhs : 0 ≤ 2 * ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1:ℝ)))) i := by
    rw [← hgval]; exact integral_nonneg_of_ae hgae
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hae2) hrhs).mp h3

end SSP.Law
