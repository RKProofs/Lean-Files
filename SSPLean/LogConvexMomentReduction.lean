import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic

/-!
# From a log-convex density quotient to the sharp adjacent-moment hierarchy

The analytic proof uses monotonicity of the logarithmic derivative and two
integrations by parts. No Fisher-information or probability-space hypotheses
are needed: moments are the integrals of the density on positive times.
-/

open MeasureTheory Filter Set Real
open scoped Topology

set_option autoImplicit false

namespace SSP.MomentReduction

noncomputable def moment (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t^n*f t

/-- Polynomially weighted exponentially decaying continuous functions are integrable. -/
theorem weighted_integrable (f : ℝ → ℝ) (hf : ContinuousOn f (Ici 0))
    (c : ℝ) (hc : 0 < c)
    (hdec : f =O[atTop] fun t => Real.exp (-c*t)) (n : ℕ) :
    IntegrableOn (fun t => t^n*f t) (Ioi 0) := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop n (b := c/2) (by linarith)).isBigO
  have hb := hp.mul hdec
  have heq : (fun t => Real.exp ((c/2)*t)*Real.exp (-c*t)) =
      (fun t => Real.exp (-(c/2)*t)) := by
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hb
  exact integrable_of_isBigO_exp_neg (by linarith)
    ((continuousOn_id.pow n).mul hf) hb

/-- The same decay assumption eliminates every polynomial boundary term at infinity. -/
theorem weighted_tendsto_zero (f : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hdec : f =O[atTop] fun t => Real.exp (-c*t)) (n : ℕ) :
    Tendsto (fun t => t^n*f t) atTop (𝓝 0) := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop n (b := c/2) (by linarith))
  have hb := hp.mul_isBigO hdec
  have heq : (fun t => Real.exp ((c/2)*t)*Real.exp (-c*t)) =
      (fun t => Real.exp (-(c/2)*t)) := by
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hb
  apply hb.tendsto_zero_of_tendsto
  convert tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by linarith : 0 < c/2)) using 1;
    (first | rfl | (ext t; simp [neg_mul]))

/-- Integration by parts with a positive polynomial power. -/
theorem integral_weighted_deriv (f f' : ℝ → ℝ)
    (hf : ContinuousOn f (Ici 0)) (hder : ∀ t, 0 < t → HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Ici 0)) (c : ℝ) (hc : 0 < c)
    (hdec : f =O[atTop] fun t => Real.exp (-c*t))
    (hdec' : f' =O[atTop] fun t => Real.exp (-c*t)) (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^(n+1)*f' t) = -(n+1 : ℝ)*moment f n := by
  have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => t^(n+1))
      ((n+1 : ℝ)*t^n) t := by
    intro t ht
    convert (hasDerivAt_id t).pow (n+1) using 1 <;>
      (first | rfl | simp)
  have h0 : Tendsto (fun t => t^(n+1)*f t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hf0 := hf 0 (by simp)
    have hlim := ((continuousWithinAt_id.pow (n+1)).mul hf0).tendsto
    have hrestrict : Ioi (0 : ℝ) ⊆ Ici 0 := Ioi_subset_Ici_self
    convert hlim.mono_left (nhdsWithin_mono 0 hrestrict) using 1 <;>
      (first | rfl | simp)
  have hi := integral_Ioi_mul_deriv_eq_deriv_mul hu hder
    (weighted_integrable f' hf' c hc hdec' (n+1))
    (by
      change Integrable (fun t => ((n+1 : ℝ)*t^n)*f t) _
      simpa only [mul_assoc] using (weighted_integrable f hf c hc hdec n).const_mul (n+1 : ℝ)) h0
    (weighted_tendsto_zero f c hc hdec (n+1))
  simpa only [moment, Pi.mul_apply, mul_assoc, integral_const_mul, zero_sub, sub_zero,
    neg_mul, Nat.cast_add, Nat.cast_one] using hi

/-- The logarithmic derivative of a positive log-convex quotient is increasing. -/
theorem log_deriv_monotone (f f' : ℝ → ℝ) (p : ℕ)
    (hpos : ∀ t, 0 < t → 0 < f t)
    (hder : ∀ t, 0 < t → HasDerivAt f (f' t) t)
    (hconv : ConvexOn ℝ (Ioi 0) (fun t => Real.log (f t/t^p))) :
    MonotoneOn (fun t => f' t/f t-(p : ℝ)/t) (Ioi 0) := by
  let g := fun t => Real.log (f t/t^p)
  have hg : ∀ t, 0 < t → HasDerivAt g (f' t/f t-(p : ℝ)/t) t := by
    intro t ht
    have hlog := ((hder t ht).log (hpos t ht).ne').sub
      (((hasDerivAt_id t).pow p).log (pow_ne_zero p ht.ne'))
    have hd : HasDerivAt (fun t => Real.log (f t)-Real.log (t^p))
        (f' t/f t-(p : ℝ)/t) t := by
      have hp : (p : ℝ)*t^(p-1)/t^p = (p : ℝ)/t := by
        cases p with
        | zero => simp
        | succ p =>
          simp only [Nat.add_sub_cancel, pow_succ]
          field_simp
      convert hlog using 1 <;> (first | rfl | (simpa only [Pi.pow_apply, id_eq, mul_one] using congrArg (fun x => f' t/f t-x) hp.symm))
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.eventually_mem ht] with x hx
    exact Real.log_div (hpos x hx).ne' (pow_ne_zero p hx.ne')
  have hm := hconv.monotoneOn_deriv (fun t ht => (hg t ht).differentiableAt)
  intro x hx y hy hxy
  have h := hm hx hy hxy
  change deriv g x ≤ deriv g y at h
  rw [(hg x hx).deriv, (hg y hy).deriv] at h
  exact h

/-- All positive-time moments of a strictly positive, exponentially decaying density are positive. -/
theorem moment_pos (f : ℝ → ℝ) (n : ℕ)
    (hpos : ∀ t, 0 < t → 0 < f t)
    (hint : IntegrableOn (fun t => t^n*f t) (Ioi 0)) : 0 < moment f n := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun t => t^n*f t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (mul_pos (pow_pos ht _) (hpos t ht)).le
  apply (integral_pos_iff_support_of_nonneg_ae hn hint).mpr
  have hsub : Ioi (0 : ℝ) ⊆ Function.support (fun t => t^n*f t) := by
    intro t ht
    exact (mul_pos (pow_pos ht _) (hpos t ht)).ne'
  have hm : (volume.restrict (Ioi (0 : ℝ))) (Ioi 0) = ⊤ := by simp
  exact lt_of_lt_of_le (by simp [hm]) (measure_mono hsub)

/-- Sharp adjacent-moment inequality from log-convexity of the density quotient.
The dimension is `p+1`; the adjacent-moment index is `r+1`. -/
theorem hierarchy_of_logConvex (f f' : ℝ → ℝ) (p r : ℕ)
    (hf : ContinuousOn f (Ici 0)) (hf' : ContinuousOn f' (Ici 0))
    (hpos : ∀ t, 0 < t → 0 < f t)
    (hder : ∀ t, 0 < t → HasDerivAt f (f' t) t)
    (c : ℝ) (hc : 0 < c)
    (hdec : f =O[atTop] fun t => Real.exp (-c*t))
    (hdec' : f' =O[atTop] fun t => Real.exp (-c*t))
    (hconv : ConvexOn ℝ (Ioi 0) (fun t => Real.log (f t/t^p))) :
    (p+r+2 : ℝ)*moment f (r+1)^2 ≤
      (p+r+1 : ℝ)*moment f r*moment f (r+2) := by
  let M0 := moment f r
  let M1 := moment f (r+1)
  let M2 := moment f (r+2)
  let a := M2/M1
  let L := fun t => f' t/f t-(p : ℝ)/t
  have hI := fun n => weighted_integrable f hf c hc hdec n
  have hI' := fun n => weighted_integrable f' hf' c hc hdec' n
  have hM1 : 0 < M1 := moment_pos f (r+1) hpos (hI _)
  have hM2 : 0 < M2 := moment_pos f (r+2) hpos (hI _)
  have ha : 0 < a := div_pos hM2 hM1
  have hmono := log_deriv_monotone f f' p hpos hder hconv
  let H := fun t => (t-a)*t^(r+1)*f' t-
    (p : ℝ)*(t-a)*t^r*f t-L a*((t-a)*t^(r+1)*f t)
  have hHid : ∀ t, 0 < t → H t = (t-a)*(L t-L a)*t^(r+1)*f t := by
    intro t ht
    dsimp [H, L]
    rw [pow_succ]
    field_simp [(hpos t ht).ne', ht.ne']
  have hHnonneg : ∀ t, 0 < t → 0 ≤ H t := by
    intro t ht
    rw [hHid t ht]
    have hprod : 0 ≤ (t-a)*(L t-L a) := by
      rcases le_total t a with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
          (sub_nonpos.mpr (hmono ht ha h))
      · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (hmono ha ht h))
    exact mul_nonneg (mul_nonneg hprod (pow_nonneg ht.le _)) (hpos t ht).le
  have hid1 : (fun t => (t-a)*t^(r+1)*f' t) =
      (fun t => t^(r+2)*f' t-a*(t^(r+1)*f' t)) := by
    funext t
    rw [show r+2 = (r+1)+1 by omega, pow_succ]
    ring
  have hid2 : (fun t => (p : ℝ)*(t-a)*t^r*f t) =
      (fun t => (p : ℝ)*(t^(r+1)*f t-a*(t^r*f t))) := by
    funext t
    rw [pow_succ]
    ring
  have hid3 : (fun t => L a*((t-a)*t^(r+1)*f t)) =
      (fun t => L a*(t^(r+2)*f t-a*(t^(r+1)*f t))) := by
    funext t
    rw [show r+2 = (r+1)+1 by omega, pow_succ]
    ring
  have hInt1 : IntegrableOn (fun t => (t-a)*t^(r+1)*f' t) (Ioi 0) := by
    rw [hid1]
    exact (hI' _).sub ((hI' _).const_mul a)
  have hInt2 : IntegrableOn (fun t => (p : ℝ)*(t-a)*t^r*f t) (Ioi 0) := by
    rw [hid2]
    exact ((hI _).sub ((hI _).const_mul a)).const_mul p
  have hInt3 : IntegrableOn (fun t => L a*((t-a)*t^(r+1)*f t)) (Ioi 0) := by
    rw [hid3]
    exact ((hI _).sub ((hI _).const_mul a)).const_mul (L a)
  have hnonneg : 0 ≤ ∫ t in Ioi (0 : ℝ), H t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hHnonneg t ht
  have hIntH : (∫ t in Ioi (0 : ℝ), H t) =
      -(r+2 : ℝ)*M1+a*(r+1 : ℝ)*M0-
      (p : ℝ)*(M1-a*M0)-L a*(M2-a*M1) := by
    change (∫ t in Ioi (0 : ℝ),
      (((fun t => (t-a)*t^(r+1)*f' t) - (fun t => (p : ℝ)*(t-a)*t^r*f t)) -
      (fun t => L a*((t-a)*t^(r+1)*f t))) t) = _
    have hs1 := integral_sub (hInt1.sub hInt2) hInt3
    have hs2 := integral_sub hInt1 hInt2
    simp only [Pi.sub_apply] at hs1 hs2
    simp only [Pi.sub_apply]
    rw [hs1, hs2, hid1, hid2, hid3]
    rw [integral_sub (hI' _) ((hI' _).const_mul a), integral_const_mul,
      integral_const_mul, integral_sub (hI _) ((hI _).const_mul a), integral_const_mul,
      integral_const_mul, integral_sub (hI _) ((hI _).const_mul a), integral_const_mul]
    rw [show r+2 = (r+1)+1 by omega,
      integral_weighted_deriv f f' hf hder hf' c hc hdec hdec' (r+1),
      integral_weighted_deriv f f' hf hder hf' c hc hdec hdec' r]
    simp only [M0, M1, M2, moment, Nat.cast_add, Nat.cast_one]
    ring
  rw [hIntH] at hnonneg
  have haM : a*M1 = M2 := by dsimp [a]; exact div_mul_cancel₀ _ hM1.ne'
  have hineq : (p+r+2 : ℝ)*M1 ≤ (p+r+1 : ℝ)*a*M0 := by
    rw [← haM] at hnonneg
    linarith only [hnonneg]
  have hmul := mul_le_mul_of_nonneg_right hineq hM1.le
  change (p+r+2 : ℝ)*M1^2 ≤ (p+r+1 : ℝ)*M0*M2
  convert hmul using 1 <;> try rfl
  · ring
  · rw [← haM]
    ring

end SSP.MomentReduction
