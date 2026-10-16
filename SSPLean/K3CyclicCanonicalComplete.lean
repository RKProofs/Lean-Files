import SSPLean.K3CyclicSpectralData

/-! # Complete canonical three-state logarithmic convexity

The spectral case split is constructed from canonical sign conditions.
This theorem proves the canonical cubic lemma, not the general-to-canonical
representation theorem for arbitrary three-state matrices.
-/

set_option autoImplicit false
open Set

namespace SSP.K3Cyclic
open SSP.LogConvexIntegral

theorem canonicalFirst_zero_feedback_eq_one (a b x2 x3 : ℝ) :
    canonicalFirst a b 0 x2 x3 = fun _ => 1 := by
  apply SSP.CubicODE.eq_of_cubic_ode
    (c0 := (0 : ℝ)) (c1 := -a*b) (c2 := a+b) (t0 := 0)
    (f1 := canonicalFirstDeriv a b 0 x2 x3)
    (f2 := canonicalFirstDeriv2 a b 0 x2 x3)
    (g1 := fun _ => 0) (g2 := fun _ => 0)
  · exact canonicalFirst_hasDerivAt a b 0 x2 x3
  · exact canonicalFirstDeriv_hasDerivAt a b 0 x2 x3
  · intro t
    convert canonicalFirstDeriv2_hasDerivAt a b 0 x2 x3 t using 1 <;> try rfl
    ring
  · intro t; simpa using hasDerivAt_const t (1 : ℝ)
  · intro t; simpa using hasDerivAt_const t (0 : ℝ)
  · intro t; simpa using hasDerivAt_const t (0 : ℝ)
  · simp
  · simp
  · simp

theorem canonicalMiddle_zero_diagonals_feedback_eq_linear (x2 x3 : ℝ) :
    canonicalMiddle 0 0 0 x2 x3 = fun t => x2*t := by
  apply SSP.CubicODE.eq_of_cubic_ode
    (c0 := (0 : ℝ)) (c1 := (0 : ℝ)) (c2 := (0 : ℝ)) (t0 := 0)
    (f1 := canonicalMiddleDeriv 0 0 0 x2 x3)
    (f2 := canonicalMiddleDeriv2 0 0 0 x2 x3)
    (g1 := fun _ => x2) (g2 := fun _ => 0)
  · exact canonicalMiddle_hasDerivAt 0 0 0 x2 x3
  · exact canonicalMiddleDeriv_hasDerivAt 0 0 0 x2 x3
  · intro t; simpa using canonicalMiddleDeriv2_hasDerivAt 0 0 0 x2 x3 t
  · intro t; simpa using (hasDerivAt_id t).const_mul x2
  · intro t; simpa using hasDerivAt_const t x2
  · intro t; simpa using hasDerivAt_const t (0 : ℝ)
  · simp
  · simp
  · simp

/-- The canonical cubic lemma, for each of the three actual exponential coordinates.
The zero-feedback and zero-diagonal degeneracies are included. -/
theorem canonical_coordinates_log_quotient_convex
    {a b c x2 x3 : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (h2 : 0 < x2) (h3 : 0 < x3) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (canonicalFirst a b c x2 x3 t/t^2)) ∧
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (canonicalMiddle a b c x2 x3 t/t)) ∧
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (canonicalThird a b c x2 x3 t/t^2)) := by
  have hb : 0 ≤ b := ha.trans hab
  have hQ : 0 ≤ c*x2*x3 := mul_nonneg (mul_nonneg hc h2.le) h3.le
  have hdata : 0 < b ∨ 0 < c*x2*x3 ∨ (a = 0 ∧ b = 0 ∧ c = 0) := by
    by_cases hb0 : 0 < b
    · exact Or.inl hb0
    by_cases hc0 : 0 < c
    · exact Or.inr (Or.inl (mul_pos (mul_pos hc0 h2) h3))
    · exact Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩)
  have hfirst_middle :
      ConvexOn ℝ (Ioi 0) (fun t => Real.log (canonicalFirst a b c x2 x3 t/t^2)) ∧
      ConvexOn ℝ (Ioi 0) (fun t => Real.log (canonicalMiddle a b c x2 x3 t/t)) := by
    rcases hdata with hbpos | hQpos | ⟨rfl,rfl,rfl⟩
    · rcases canonical_spectralData ha hab hQ (Or.inl hbpos) with hreal | hcomplex
      · obtain ⟨u,v,w,huv,hvw,hw,hs,hp,hq⟩ := hreal
        exact ⟨canonicalFirst_orderedRealRoots_log_quotient_convex ha hb hc h2.le h3.le
            huv hvw hw hs hp hq,
          canonicalMiddle_orderedRealRoots_log_quotient_convex ha hb hab hc h2 h3.le
            huv hvw hw hs hp hq⟩
      · obtain ⟨mu,d,omega,hd,ho,hs,hp,hq⟩ := hcomplex
        have hs' : a+b = d*(1+3*(mu/d)) := by field_simp; nlinarith [hs]
        have hp' : a*b = d^2*(3*(mu/d)^2+2*(mu/d)+omega^2) := by
          field_simp; nlinarith [hp]
        have hq' : c*x2*x3 = d^3*((1+mu/d)*((mu/d)^2+omega^2)) := by
          field_simp; nlinarith [hq]
        exact ⟨canonicalFirst_complexPair_log_quotient_convex ha hb hc h2.le h3.le
            hd ho hs' hp' hq',
          canonicalMiddle_complexPair_log_quotient_convex ha hb hab hc h2 h3.le
            hd hs hp hq⟩
    · rcases canonical_spectralData ha hab hQ (Or.inr hQpos) with hreal | hcomplex
      · obtain ⟨u,v,w,huv,hvw,hw,hs,hp,hq⟩ := hreal
        exact ⟨canonicalFirst_orderedRealRoots_log_quotient_convex ha hb hc h2.le h3.le
            huv hvw hw hs hp hq,
          canonicalMiddle_orderedRealRoots_log_quotient_convex ha hb hab hc h2 h3.le
            huv hvw hw hs hp hq⟩
      · obtain ⟨mu,d,omega,hd,ho,hs,hp,hq⟩ := hcomplex
        have hs' : a+b = d*(1+3*(mu/d)) := by field_simp; nlinarith [hs]
        have hp' : a*b = d^2*(3*(mu/d)^2+2*(mu/d)+omega^2) := by
          field_simp; nlinarith [hp]
        have hq' : c*x2*x3 = d^3*((1+mu/d)*((mu/d)^2+omega^2)) := by
          field_simp; nlinarith [hq]
        exact ⟨canonicalFirst_complexPair_log_quotient_convex ha hb hc h2.le h3.le
            hd ho hs' hp' hq',
          canonicalMiddle_complexPair_log_quotient_convex ha hb hab hc h2 h3.le
            hd hs hp hq⟩
    · constructor
      · rw [canonicalFirst_zero_feedback_eq_one]
        exact log_quotient_convex_mono (fun _ => 1) (p := 0) (q := 2) (by omega)
          (by intro t ht; norm_num) (by simpa using convexOn_const (0 : ℝ) (convex_Ioi (0 : ℝ)))
      · rw [canonicalMiddle_zero_diagonals_feedback_eq_linear]
        apply (convexOn_const (Real.log x2) (convex_Ioi (0 : ℝ))).congr
        intro t ht
        change Real.log x2 = Real.log (x2*t/t)
        rw [mul_div_cancel_right₀ x2 (ne_of_gt ht)]
  exact ⟨hfirst_middle.1,hfirst_middle.2,
    canonicalThird_log_quotient_convex_of_middle h3
      (canonicalMiddle_pos ha hb hc h2 h3.le) hfirst_middle.2⟩

noncomputable def canonicalMixture
    (a b c x2 x3 pi1 pi2 pi3 t : ℝ) : ℝ :=
  pi1*canonicalFirst a b c x2 x3 t+
    pi2*canonicalMiddle a b c x2 x3 t+pi3*canonicalThird a b c x2 x3 t

/-- Positive mixtures of the three canonical starts satisfy the same
dimension-three quotient bound, including identically zero mixtures. -/
theorem canonicalMixture_log_quotient_convex
    {a b c x2 x3 pi1 pi2 pi3 : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (h2 : 0 < x2) (h3 : 0 < x3)
    (hp1 : 0 ≤ pi1) (hp2 : 0 ≤ pi2) (hp3 : 0 ≤ pi3) :
    ConvexOn ℝ (Ioi 0)
      (fun t => Real.log (canonicalMixture a b c x2 x3 pi1 pi2 pi3 t/t^2)) := by
  have hb : 0 ≤ b := ha.trans hab
  obtain ⟨hf,hm,ht⟩ := canonical_coordinates_log_quotient_convex ha hab hc h2 h3
  have hm2 := log_quotient_convex_mono (canonicalMiddle a b c x2 x3)
    (p := 1) (q := 2) (by omega) (canonicalMiddle_pos ha hb hc h2 h3.le)
    (by simpa using hm)
  have h := log_nonneg_three_combination_convex
    (fun t => canonicalFirst a b c x2 x3 t/t^2)
    (fun t => canonicalMiddle a b c x2 x3 t/t^2)
    (fun t => canonicalThird a b c x2 x3 t/t^2) pi1 pi2 pi3 hp1 hp2 hp3
    (fun t ht => div_pos (canonicalFirst_pos ha hb hc h2.le h3.le t ht) (pow_pos ht _))
    (fun t ht => div_pos (canonicalMiddle_pos ha hb hc h2 h3.le t ht) (pow_pos ht _))
    (fun t ht => div_pos (canonicalThird_pos ha hb hc h2 h3 t ht) (pow_pos ht _))
    hf hm2 ht
  simpa only [canonicalMixture,add_div,mul_div_assoc] using h

end SSP.K3Cyclic
