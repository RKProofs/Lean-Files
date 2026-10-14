import SSPLean.K3CyclicCanonicalThird
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Integral representation of the canonical third coordinate -/

set_option autoImplicit false

namespace SSP.K3Cyclic

noncomputable def canonicalThirdWeighted
    (a b c x2 x3 t : ℝ) : ℝ :=
  Real.exp (-b * t) * canonicalThird a b c x2 x3 t

theorem canonicalThirdWeighted_hasDerivAt
    (a b c x2 x3 t : ℝ) :
    HasDerivAt (canonicalThirdWeighted a b c x2 x3)
      (x3 * Real.exp (-b * t) * canonicalMiddle a b c x2 x3 t) t := by
  have hlin : HasDerivAt (fun u : ℝ => -b * u) (-b) t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (-b)
  have he := (Real.hasDerivAt_exp (-b * t)).comp t hlin
  have hthird := canonicalThird_hasDerivAt a b c x2 x3 t
  have h := he.mul hthird
  convert h using 1
  all_goals try rfl
  simp only [Function.comp_apply]
  rw [canonicalThirdDeriv_eq_middle]
  ring

/-- Variation of constants for the last edge of the canonical cycle. -/
theorem canonicalThirdWeighted_eq_integral
    (a b c x2 x3 t : ℝ) :
    canonicalThirdWeighted a b c x2 x3 t =
      ∫ s in (0 : ℝ)..t,
        x3 * Real.exp (-b * s) * canonicalMiddle a b c x2 x3 s := by
  have hmcont : Continuous (canonicalMiddle a b c x2 x3) :=
    continuous_iff_continuousAt.mpr fun s =>
      (canonicalMiddle_hasDerivAt a b c x2 x3 s).continuousAt
  have hint : IntervalIntegrable
      (fun s : ℝ => x3 * Real.exp (-b * s) *
        canonicalMiddle a b c x2 x3 s) MeasureTheory.volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t)
    (f := canonicalThirdWeighted a b c x2 x3)
    (f' := fun s => x3 * Real.exp (-b * s) *
      canonicalMiddle a b c x2 x3 s)
    (fun s _ => canonicalThirdWeighted_hasDerivAt a b c x2 x3 s) hint
  rw [hFTC]
  simp [canonicalThirdWeighted]

end SSP.K3Cyclic
