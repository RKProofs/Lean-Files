import Mathlib

/-! # From corrected curvature to dimension-corrected logarithmic convexity -/

set_option autoImplicit false
open Set

namespace SSP.LogConvexIntegral

/-- The derivative interface allows matrix-coordinate proofs to use their explicit
derivatives, without an additional smoothness or derivative-identification layer. -/
theorem log_quotient_convex_of_curvature
    (f f1 f2 : ℝ → ℝ) (p : ℕ)
    (h0 : ∀ t, HasDerivAt f (f1 t) t)
    (h1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hpos : ∀ t, 0 < t → 0 < f t)
    (hcurv : ∀ t, 0 < t →
      0 ≤ t^2*(f t*f2 t-(f1 t)^2)+(p : ℝ)*(f t)^2) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (f t/t^p)) := by
  let g := fun t => Real.log (f t)-(p : ℝ)*Real.log t
  let g1 := fun t => f1 t/f t-(p : ℝ)/t
  let g2 := fun t => (f2 t*f t-(f1 t)^2)/(f t)^2+(p : ℝ)/t^2
  have hg : ∀ t, 0 < t → HasDerivAt g (g1 t) t := by
    intro t ht
    convert ((h0 t).log (hpos t ht).ne').sub
      (((hasDerivAt_id t).log ht.ne').const_mul (p : ℝ)) using 1 <;> try rfl
    dsimp [g1]
    ring
  have hg1 : ∀ t, 0 < t → HasDerivAt g1 (g2 t) t := by
    intro t ht
    have hd := ((h1 t).div (h0 t) (hpos t ht).ne').sub
      ((hasDerivAt_const t (p : ℝ)).div (hasDerivAt_id t) ht.ne')
    convert hd using 1 <;> try rfl
    dsimp [g2]
    ring
  have hg2 : ∀ t, 0 < t → 0 ≤ g2 t := by
    intro t ht
    have hft : f t ≠ 0 := (hpos t ht).ne'
    have ht0 : t ≠ 0 := ht.ne'
    have hid : g2 t = (t^2*(f t*f2 t-(f1 t)^2)+(p : ℝ)*(f t)^2)/
        (t^2*(f t)^2) := by
      dsimp [g2]
      field_simp
    rw [hid]
    exact div_nonneg (hcurv t ht) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hconv : ConvexOn ℝ (Ioi 0) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi (0 : ℝ))
      (f' := g1) (f'' := g2)
    · intro t ht
      exact (hg t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hg t (by simpa only [interior_Ioi, mem_Ioi] using ht)).hasDerivWithinAt
    · intro t ht
      exact (hg1 t (by simpa only [interior_Ioi, mem_Ioi] using ht)).hasDerivWithinAt
    · intro t ht
      exact hg2 t (by simpa only [interior_Ioi, mem_Ioi] using ht)
  apply hconv.congr
  intro t ht
  dsimp [g]
  rw [Real.log_div (hpos t ht).ne' (pow_ne_zero _ (show t ≠ 0 from ne_of_gt ht)),
    Real.log_pow]

/-- Increasing the quotient exponent preserves convexity. -/
theorem log_quotient_convex_mono (f : ℝ → ℝ) {p q : ℕ} (hpq : p ≤ q)
    (hpos : ∀ t, 0 < t → 0 < f t)
    (hc : ConvexOn ℝ (Ioi 0) (fun t => Real.log (f t/t^p))) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (f t/t^q)) := by
  have hneglog : ConvexOn ℝ (Ioi 0) (fun t : ℝ => -Real.log t) :=
    strictConcaveOn_log_Ioi.concaveOn.neg
  have hcast : (0 : ℝ) ≤ (q : ℝ)-p := sub_nonneg.mpr (by exact_mod_cast hpq)
  apply (hc.add (hneglog.smul hcast)).congr
  intro t ht
  simp only [Pi.add_apply, smul_eq_mul]
  rw [Real.log_div (hpos t ht).ne' (pow_ne_zero _ (show t ≠ 0 from ne_of_gt ht)),
    Real.log_div (hpos t ht).ne' (pow_ne_zero _ (show t ≠ 0 from ne_of_gt ht))]
  simp only [Real.log_pow]
  ring

end SSP.LogConvexIntegral
