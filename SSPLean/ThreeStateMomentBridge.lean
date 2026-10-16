import SSPLean.K3CyclicCanonicalComplete

/-! # From a positive canonical representation to all three-state moments

`CanonicalPairingRepresentation` contains a representation identity, not a
curvature or moment assumption. Its existence for general three-state matrices is proved in
`ThreeStateConjectures.lean`, which closes `MomentConjecture 3`.
-/

set_option autoImplicit false
open Set Matrix

namespace SSP.MatrixMomentReduction

open SSP.K3Cyclic SSP.LogConvexIntegral

structure CanonicalPairingRepresentation (F : ℝ → ℝ) where
  a : ℝ
  b : ℝ
  c : ℝ
  x2 : ℝ
  x3 : ℝ
  pi1 : ℝ
  pi2 : ℝ
  pi3 : ℝ
  shift : ℝ
  a_nonneg : 0 ≤ a
  ordered : a ≤ b
  c_nonneg : 0 ≤ c
  x2_pos : 0 < x2
  x3_pos : 0 < x3
  pi1_nonneg : 0 ≤ pi1
  pi2_nonneg : 0 ≤ pi2
  pi3_nonneg : 0 ≤ pi3
  identity : ∀ t, F t = Real.exp (shift*t)*canonicalMixture a b c x2 x3 pi1 pi2 pi3 t

theorem canonicalPairingRepresentation_log_quotient_convex
    (F : ℝ → ℝ) (R : CanonicalPairingRepresentation F)
    (hpos : ∀ t, 0 < t → 0 < F t) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (F t/t^2)) := by
  have hp : ∀ t, 0 < t → 0 < canonicalMixture R.a R.b R.c R.x2 R.x3 R.pi1 R.pi2 R.pi3 t := by
    intro t ht
    have h := hpos t ht
    rw [R.identity] at h
    exact pos_of_mul_pos_right h (Real.exp_pos _).le
  have hc := log_quotient_exp_mul_convex _ 2 R.shift hp
    (canonicalMixture_log_quotient_convex R.a_nonneg R.ordered R.c_nonneg
      R.x2_pos R.x3_pos R.pi1_nonneg R.pi2_nonneg R.pi3_nonneg)
  exact hc.congr (fun t _ => by rw [R.identity])

/-- Representation-existence statement proved by
`threeStateCanonicalRepresentationTheorem` in `ThreeStateConjectures`. -/
def ThreeStateCanonicalRepresentationTheorem : Prop :=
  ∀ (A : Mat 3) (u v : Fin 3 → ℝ),
    (∀ i j, 0 ≤ A i j) → (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ v i) →
    pairing A u v ≠ 0 → Nonempty (CanonicalPairingRepresentation (pairing A u v))

theorem matrixConjecture_three_of_canonical_representations
    (hrep : ThreeStateCanonicalRepresentationTheorem) : MatrixConjecture 3 := by
  intro A u v hA hu hv hne
  obtain ⟨R⟩ := hrep A u v hA hu hv hne
  simpa only [show 3-1 = 2 by omega] using
    canonicalPairingRepresentation_log_quotient_convex _ R (pairing_pos A u v hA hu hv hne)

/-- Every moment index follows once the representation-existence theorem is
provided; all canonical analysis and integration are discharged in Lean. -/
theorem momentConjecture_three_of_canonical_representations
    (hrep : ThreeStateCanonicalRepresentationTheorem) : MomentConjecture 3 :=
  matrixConjecture_implies_momentConjecture (by omega)
    (matrixConjecture_three_of_canonical_representations hrep)

/-- A concrete stable three-state law whose uniformized pairing has a positive
canonical representation satisfies Conjecture 1's inequality for every index. -/
theorem conjecture_one_three_state_of_canonical_representation
    (P : Mat 3) (u v : Fin 3 → ℝ) (rate atom : ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1)
    (R : CanonicalPairingRepresentation (pairing (rate • P) u v))
    (k : ℕ) (hk : 1 ≤ k) :
    ((3+k : ℕ) : ℝ)/((3+k-1 : ℕ) : ℝ)*rawMoment P u v rate atom k^2 ≤
      rawMoment P u v rate atom (k-1)*rawMoment P u v rate atom (k+1) := by
  by_cases hzero : pairing (rate • P) u v = 0
  · have hd : density P u v rate = 0 := by
      rw [density_uniformization,hzero]
      ext t; simp
    simp only [rawMoment,hd,SSP.MomentReduction.moment,Pi.zero_apply,mul_zero,
      MeasureTheory.integral_zero,zero_add,show k ≠ 0 by omega,show k+1 ≠ 0 by omega,if_false,
      zero_pow (by norm_num : 2 ≠ 0),mul_zero,le_refl]
  have hA : ∀ i j, 0 ≤ (rate • P) i j := fun i j => mul_nonneg hrate.le (hP i j)
  have hpF := pairing_pos (rate • P) u v hA hu hv hzero
  have hp : ∀ t, 0 < t → 0 < density P u v rate t := by
    intro t ht
    rw [density_uniformization]
    exact mul_pos (Real.exp_pos _) (hpF t ht)
  have hc : ConvexOn ℝ (Ioi 0) (fun t => Real.log (density P u v rate t/t^2)) := by
    simpa only [density_uniformization] using logConvex_exp_shift _ 2 rate hpF
      (canonicalPairingRepresentation_log_quotient_convex _ R hpF)
  obtain ⟨c,hcpos,hdec,hdec'⟩ := density_decay P u v rate hrate hρ
  have h := SSP.MomentReduction.hierarchy_of_logConvex (density P u v rate)
    (densityDeriv P u v rate) 2 (k-1)
    (density_continuous P u v rate).continuousOn
    (densityDeriv_continuous P u v rate).continuousOn hp
    (fun t _ => density_hasDerivAt P u v rate t) c hcpos hdec hdec' hc
  have hidx : k-1+1 = k := by omega
  have hidx2 : k-1+2 = k+1 := by omega
  rw [hidx,hidx2] at h
  have hden : (0 : ℝ) < ((3+k-1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < 3+k-1 by omega)
  have hcoeff1 : (2 : ℝ)+((k-1 : ℕ) : ℝ)+2 = ((3+k : ℕ) : ℝ) := by norm_cast; omega
  have hcoeff2 : (2 : ℝ)+((k-1 : ℕ) : ℝ)+1 = ((3+k-1 : ℕ) : ℝ) := by norm_cast; omega
  simp only [Nat.cast_ofNat] at h
  rw [hcoeff1,hcoeff2] at h
  have hmplus : 0 ≤ SSP.MomentReduction.moment (density P u v rate) (k+1) := by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (pow_nonneg ht.le _) (hp t ht).le
  simp only [rawMoment,show k ≠ 0 by omega,show k+1 ≠ 0 by omega,if_false,add_zero]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  by_cases hk1 : k-1 = 0
  · simp only [hk1,if_true]
    have h' := h
    rw [hk1] at h'
    nlinarith [mul_nonneg hden.le (mul_nonneg hatom hmplus)]
  · simpa only [if_neg hk1,add_zero,mul_assoc,mul_comm,mul_left_comm] using h

end SSP.MatrixMomentReduction
