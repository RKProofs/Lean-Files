import SSPLean.BlockTriangularClosure

set_option autoImplicit false
open Matrix Set MeasureTheory
namespace SSP.MatrixMomentReduction

/-- Concrete pairing version of the moment reduction: no conjecture is needed
for matrices other than the given uniformized pairing. -/
theorem conjecture_one_of_pairing_logConvex {s : ℕ} (hs : 1 ≤ s)
    (P : Mat s) (u v : Fin s → ℝ) (rate atom : ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1)
    (hconvF : ConvexOn ℝ (Ioi 0) (fun t => Real.log (pairing (rate • P) u v t/t^(s-1))))
    (k : ℕ) (hk : 1 ≤ k) :
    ((s+k : ℕ) : ℝ)/((s+k-1 : ℕ) : ℝ)*rawMoment P u v rate atom k^2 ≤
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
  have hc : ConvexOn ℝ (Ioi 0) (fun t => Real.log (density P u v rate t/t^(s-1))) := by
    simpa only [density_uniformization] using logConvex_exp_shift _ (s-1) rate hpF hconvF
  obtain ⟨c,hcpos,hdec,hdec'⟩ := density_decay P u v rate hrate hρ
  have h := SSP.MomentReduction.hierarchy_of_logConvex (density P u v rate)
    (densityDeriv P u v rate) (s-1) (k-1)
    (density_continuous P u v rate).continuousOn
    (densityDeriv_continuous P u v rate).continuousOn hp
    (fun t _ => density_hasDerivAt P u v rate t) c hcpos hdec hdec' hc
  have hidx : k-1+1 = k := by omega
  have hidx2 : k-1+2 = k+1 := by omega
  rw [hidx,hidx2] at h
  have hden : (0 : ℝ) < ((s+k-1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < s+k-1 by omega)
  have hcoeff1 : ((s-1 : ℕ) : ℝ)+((k-1 : ℕ) : ℝ)+2 = ((s+k : ℕ) : ℝ) := by norm_cast; omega
  have hcoeff2 : ((s-1 : ℕ) : ℝ)+((k-1 : ℕ) : ℝ)+1 = ((s+k-1 : ℕ) : ℝ) := by norm_cast; omega
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

namespace SSP.BlockTriangular
open SSP.MatrixMomentReduction

/-- Conjecture 1 for stable upper triangular block matrices, assuming
Conjecture 2 in the two diagonal block dimensions. -/
theorem conjecture_one_block_triangular {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hconjB : MatrixConjecture p) (hconjE : MatrixConjecture q)
    (B : SSP.MatrixMomentReduction.Mat p) (C : Matrix (Fin p) (Fin q) ℝ)
    (E : SSP.MatrixMomentReduction.Mat q)
    (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) (hE : ∀ i j, 0 ≤ E i j)
    (u v : Fin (p+q) → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (rate atom : ℝ) (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ ((upperBlock B C E).map (algebraMap ℝ ℂ)) < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ((p+q+k : ℕ) : ℝ)/((p+q+k-1 : ℕ) : ℝ)*rawMoment (upperBlock B C E) u v rate atom k^2 ≤
      rawMoment (upperBlock B C E) u v rate atom (k-1)*
        rawMoment (upperBlock B C E) u v rate atom (k+1) := by
  apply conjecture_one_of_pairing_logConvex (by omega) _ _ _ _ _
    (upperBlock_nonneg B C E hB hC hE) hu hv hrate hatom hρ _ k hk
  rw [← upperBlock_smul]
  exact block_triangular_closure hp hq hconjB hconjE (rate • B) (rate • C) (rate • E)
    (fun i j => mul_nonneg hrate.le (hB i j))
    (fun i j => mul_nonneg hrate.le (hC i j))
    (fun i j => mul_nonneg hrate.le (hE i j)) u v hu hv

/-- Unconditional four-state case: two nonnegative 2×2 diagonal blocks. -/
theorem conjecture_one_two_by_two_blocks
    (B E : SSP.MatrixMomentReduction.Mat 2) (C : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) (hE : ∀ i j, 0 ≤ E i j)
    (u v : Fin (2+2) → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (rate atom : ℝ) (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ ((upperBlock B C E).map (algebraMap ℝ ℂ)) < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ((4+k : ℕ) : ℝ)/((4+k-1 : ℕ) : ℝ)*rawMoment (upperBlock B C E) u v rate atom k^2 ≤
      rawMoment (upperBlock B C E) u v rate atom (k-1)*
        rawMoment (upperBlock B C E) u v rate atom (k+1) := by
  exact conjecture_one_block_triangular (by omega) (by omega)
    matrixConjecture_two matrixConjecture_two B C E hB hC hE
    u v hu hv rate atom hrate hatom hρ k hk

end SSP.BlockTriangular
