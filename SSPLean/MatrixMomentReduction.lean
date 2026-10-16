import SSPLean.LogConvexMomentReduction
import SSPLean.SemigroupMoments
import SSPLean.SpectralDecay
import SSPLean.SurvivalMonotone
import SSPLean.MatrixTwoLogConvex

/-!
# Conjecture 2 implies Conjecture 1

A stable uniformized phase-type generator is `rate • (P - I)`, where `rate > 0`,
`P` is entrywise nonnegative and has spectral radius below one. The density is
`uᵀ exp(t rate(P-I)) v`, with nonnegative endpoint vectors. The endpoint vectors
need not be normalized: the moment inequality is homogeneous in the density.
-/

open scoped Matrix.Norms.Operator Topology
open Matrix NormedSpace MeasureTheory Filter Set

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace SSP.MatrixMomentReduction

abbrev Mat (s : ℕ) := Matrix (Fin s) (Fin s) ℝ

noncomputable local instance (s : ℕ) : AddCommGroup (Mat s) := Matrix.linftyOpNormedAddCommGroup.toAddCommGroup
noncomputable local instance (s : ℕ) : TopologicalSpace (Mat s) :=
  Matrix.linftyOpNormedAddCommGroup.toUniformSpace.toTopologicalSpace
noncomputable local instance (s : ℕ) : Module ℝ (Mat s) := Matrix.linftyOpNormedSpace.toModule
noncomputable local instance (s : ℕ) : NormedAddCommGroup (Mat s) := Matrix.linftyOpNormedAddCommGroup
noncomputable local instance (s : ℕ) : SeminormedAddCommGroup (Mat s) := Matrix.linftyOpSeminormedAddCommGroup
noncomputable local instance (s : ℕ) : NormedSpace ℝ (Mat s) := Matrix.linftyOpNormedSpace

noncomputable def pairingFun {s : ℕ} (u v : Fin s → ℝ) : Mat s →L[ℝ] ℝ :=
  ∑ i, u i • SSP.Semigroup.rowFun v i

@[simp] theorem pairingFun_apply {s : ℕ} (u v : Fin s → ℝ) (M : Mat s) :
    pairingFun u v M = dotProduct u (M.mulVec v) := by
  simp only [pairingFun, _root_.sum_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

noncomputable def pairing {s : ℕ} (A : Mat s) (u v : Fin s → ℝ) (t : ℝ) : ℝ :=
  pairingFun u v (NormedSpace.exp (t • A))

/-- Conjecture 2 at the fixed dimension `s`, for the nonzero scalar pairing. -/
def MatrixConjecture (s : ℕ) : Prop :=
  ∀ (A : Mat s) (u v : Fin s → ℝ),
    (∀ i j, 0 ≤ A i j) → (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ v i) →
    pairing A u v ≠ 0 →
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (pairing A u v t/t^(s-1)))

noncomputable def density {s : ℕ} (P : Mat s) (u v : Fin s → ℝ) (rate : ℝ) : ℝ → ℝ :=
  pairing (rate • (P-1)) u v

noncomputable def densityDeriv {s : ℕ} (P : Mat s) (u v : Fin s → ℝ) (rate : ℝ) : ℝ → ℝ :=
  fun t => pairingFun u v (NormedSpace.exp (t • (rate • (P-1))) * (rate • (P-1)))

/-- The derivative is the actual derivative of the matrix-exponential density. -/
theorem density_hasDerivAt {s : ℕ} (P : Mat s) (u v : Fin s → ℝ) (rate t : ℝ) :
    HasDerivAt (density P u v rate) (densityDeriv P u v rate t) t := by
  convert
    (pairingFun u v).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (rate • (P-1)) t) using 1 <;> rfl

theorem density_continuous {s : ℕ} (P : Mat s) (u v : Fin s → ℝ) (rate : ℝ) :
    Continuous (density P u v rate) :=
  continuous_iff_continuousAt.mpr fun t => (density_hasDerivAt P u v rate t).continuousAt

theorem densityDeriv_continuous {s : ℕ} (P : Mat s) (u v : Fin s → ℝ) (rate : ℝ) :
    Continuous (densityDeriv P u v rate) := by
  apply (pairingFun u v).continuous.comp
  exact (continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) (rate • (P-1)) t).continuousAt).mul continuous_const

theorem exp_sub_one {s : ℕ} (P : Mat s) (t : ℝ) :
    NormedSpace.exp (t • (P-1)) = Real.exp (-t) • NormedSpace.exp (t • P) := by
  convert SSP.Semigroup.exp_smul_sub_one P t using 1 <;> rfl

/-- Uniformization, as an equality of the actual scalar pairings. -/
theorem density_uniformization {s : ℕ} (P : Mat s) (u v : Fin s → ℝ) (rate : ℝ) :
    density P u v rate = fun t => Real.exp (-rate*t)*pairing (rate • P) u v t := by
  funext t
  simp only [density, pairing]
  rw [show t • (rate • (P-1)) = (rate*t) • (P-1) by module,
    exp_sub_one, map_smul, smul_eq_mul]
  have he : Real.exp (-(rate*t)) = Real.exp (-rate*t) := by congr 1; ring
  rw [he]
  have ht : (rate*t) • P = t • (rate • P) := by rw [smul_smul, mul_comm]
  rw [ht]

/-- Pairing coefficients of powers are nonnegative. -/
theorem power_pairing_nonneg {s : ℕ} (P : Mat s) (u v : Fin s → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) (n : ℕ) :
    0 ≤ pairingFun u v (P^n) := by
  simp only [pairingFun_apply, dotProduct, Matrix.mulVec]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hu i)
    (Finset.sum_nonneg fun j _ => mul_nonneg (SSP.Survival.pow_nonneg_entry P hP n i j) (hv j))

/-- The scalar pairing has its genuine convergent exponential series. -/
theorem pairing_series {s : ℕ} (P : Mat s) (u v : Fin s → ℝ) (t : ℝ) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹*t^n)*pairingFun u v (P^n))
      (pairing P u v t) := by
  have hs : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (t • P)^n) :=
    (NormedSpace.expSeries_summable (𝕂 := ℝ) (t • P)).congr fun n => by
      rw [NormedSpace.expSeries_apply_eq]
  have hm := (pairingFun u v).hasSum hs.hasSum
  rw [← congrFun (NormedSpace.exp_eq_tsum ℝ) (t • P)] at hm
  simpa only [smul_pow, map_smul, smul_smul, smul_eq_mul, pairingFun_apply, pairing] using hm

/-- A nonzero nonnegative matrix pairing is positive at every positive time. -/
theorem pairing_pos {s : ℕ} (P : Mat s) (u v : Fin s → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hne : pairing P u v ≠ 0) (t : ℝ) (ht : 0 < t) :
    0 < pairing P u v t := by
  have hcoeff : ∃ n : ℕ, 0 < pairingFun u v (P^n) := by
    by_contra h
    push Not at h
    have hz : ∀ n : ℕ, pairingFun u v (P^n) = 0 := fun n =>
      le_antisymm (h n) (power_pairing_nonneg P u v hP hu hv n)
    apply hne
    ext x
    have hs := (pairing_series P u v x).tsum_eq
    simpa [hz] using hs.symm
  obtain ⟨n, hn⟩ := hcoeff
  have hs := pairing_series P u v t
  rw [← hs.tsum_eq]
  apply hs.summable.tsum_pos
    (fun n => mul_nonneg (mul_nonneg (by positivity) (pow_nonneg ht.le _))
      (power_pairing_nonneg P u v hP hu hv n)) n
  exact mul_pos (mul_pos (by positivity) (pow_pos ht _)) hn

/-- Geometric power bounds give an exponential bound for the actual matrix exponential. -/
theorem norm_exp_of_power_bound {s : ℕ} (P : Mat s) (θ C t : ℝ)
    (_hθ : 0 ≤ θ) (_hC : 0 ≤ C) (ht : 0 ≤ t)
    (hpow : ∀ n : ℕ, ‖P^n‖ ≤ C*θ^n) :
    ‖NormedSpace.exp (t • P)‖ ≤ C*Real.exp (t*θ) := by
  have hs : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹)*(t*θ)^n) := by
    simpa [div_eq_inv_mul] using Real.summable_pow_div_factorial (t*θ)
  have hn : ∀ n : ℕ, ‖((n.factorial : ℝ)⁻¹) • (t • P)^n‖ ≤
      C*(((n.factorial : ℝ)⁻¹)*(t*θ)^n) := by
    intro n
    rw [smul_pow, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (n.factorial : ℝ)⁻¹), abs_of_nonneg (pow_nonneg ht n)]
    calc (n.factorial : ℝ)⁻¹*(t^n*‖P^n‖)
        ≤ (n.factorial : ℝ)⁻¹*(t^n*(C*θ^n)) := by gcongr; exact hpow n
      _ = C*((n.factorial : ℝ)⁻¹*(t*θ)^n) := by rw [mul_pow]; ring
  have hsn : Summable (fun n : ℕ => ‖((n.factorial : ℝ)⁻¹) • (t • P)^n‖) :=
    (hs.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hn
  rw [NormedSpace.exp_eq_tsum ℝ]
  calc ‖∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • (t • P)^n‖
      ≤ ∑' n : ℕ, ‖((n.factorial : ℝ)⁻¹) • (t • P)^n‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' n : ℕ, C*((n.factorial : ℝ)⁻¹*(t*θ)^n) :=
      Summable.tsum_le_tsum hn hsn (hs.mul_left C)
    _ = C*Real.exp (t*θ) := by
      rw [tsum_mul_left]
      congr 1
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
      simp only [smul_eq_mul]

/-- Spectral stability supplies decay for the density and its actual derivative. -/
theorem density_decay {s : ℕ} (P : Mat s) (u v : Fin s → ℝ) (rate : ℝ)
    (hrate : 0 < rate)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1) :
    ∃ c : ℝ, 0 < c ∧
      density P u v rate =O[atTop] (fun t => Real.exp (-c*t)) ∧
      densityDeriv P u v rate =O[atTop] (fun t => Real.exp (-c*t)) := by
  obtain ⟨θ, hθ, hθ1, C, hC, hpow⟩ :=
    SSP.exists_geometric_bound_of_spectralRadius_lt_one s P hρ
  let c := rate*(1-θ)
  have hc : 0 < c := mul_pos hrate (sub_pos.mpr hθ1)
  have hmat : ∀ t, 0 ≤ t →
      ‖NormedSpace.exp (t • (rate • (P-1)))‖ ≤ C*Real.exp (-c*t) := by
    intro t ht
    rw [show t • (rate • (P-1)) = (rate*t) • (P-1) by module,
      exp_sub_one, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(rate*t))*‖NormedSpace.exp ((rate*t) • P)‖
        ≤ Real.exp (-(rate*t))*(C*Real.exp ((rate*t)*θ)) := by
          gcongr
          exact norm_exp_of_power_bound P θ C (rate*t) hθ hC (mul_nonneg hrate.le ht) hpow
      _ = C*Real.exp (-c*t) := by
        rw [mul_left_comm, mul_assoc, ← Real.exp_add]
        dsimp [c]
        congr 2
        ring
  refine ⟨c, hc, ?_, ?_⟩
  · apply Asymptotics.IsBigO.of_bound (‖pairingFun u v‖*C)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    change ‖pairingFun u v (NormedSpace.exp (t • (rate • (P-1))))‖ ≤ _
    rw [Real.norm_eq_abs (Real.exp (-c*t)), abs_of_pos (Real.exp_pos _)]
    exact ((pairingFun u v).le_opNorm _).trans
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (hmat t ht) (norm_nonneg (pairingFun u v)))
  · apply Asymptotics.IsBigO.of_bound (‖pairingFun u v‖*C*‖rate • (P-1)‖)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    change ‖pairingFun u v (NormedSpace.exp (t • (rate • (P-1))) * (rate • (P-1)))‖ ≤ _
    rw [Real.norm_eq_abs (Real.exp (-c*t)), abs_of_pos (Real.exp_pos _)]
    exact ((pairingFun u v).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left
        ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (hmat t ht) (norm_nonneg _)))
        (norm_nonneg (pairingFun u v))).trans_eq (by ring))

/-- Multiplication by a positive exponential preserves quotient log-convexity. -/
theorem logConvex_exp_shift (F : ℝ → ℝ) (p : ℕ) (rate : ℝ)
    (hpos : ∀ t, 0 < t → 0 < F t)
    (hconv : ConvexOn ℝ (Ioi 0) (fun t => Real.log (F t/t^p))) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log ((Real.exp (-rate*t)*F t)/t^p)) := by
  have haff : ConvexOn ℝ (Ioi 0) (fun t : ℝ => -rate*t) := by
    refine ⟨convex_Ioi _, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith
  apply (haff.add hconv).congr
  intro t ht
  simp only [Pi.add_apply]
  rw [mul_div_assoc, Real.log_mul (Real.exp_pos _).ne'
    (div_pos (hpos t ht) (pow_pos ht _)).ne', Real.log_exp]

/-- Conjecture 2 implies the complete moment hierarchy for every stable
uniformized matrix density. There are no assumed integral identities or
boundary limits in this theorem. -/
theorem conjecture_two_implies_conjecture_one {s : ℕ} (hs : 1 ≤ s)
    (hconj : MatrixConjecture s)
    (P : Mat s) (u v : Fin s → ℝ) (rate : ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hrate : 0 < rate)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1) (r : ℕ) :
    (s+r+1 : ℝ)*SSP.MomentReduction.moment (density P u v rate) (r+1)^2 ≤
      (s+r : ℝ)*SSP.MomentReduction.moment (density P u v rate) r*
        SSP.MomentReduction.moment (density P u v rate) (r+2) := by
  by_cases hzero : pairing (rate • P) u v = 0
  · have hd : density P u v rate = 0 := by
      rw [density_uniformization, hzero]
      ext t
      simp
    simp [hd, SSP.MomentReduction.moment]
  have hA : ∀ i j, 0 ≤ (rate • P) i j := fun i j => mul_nonneg hrate.le (hP i j)
  have hposF := pairing_pos (rate • P) u v hA hu hv hzero
  have hpos : ∀ t, 0 < t → 0 < density P u v rate t := by
    intro t ht
    rw [density_uniformization]
    exact mul_pos (Real.exp_pos _) (hposF t ht)
  have hconv := logConvex_exp_shift (pairing (rate • P) u v) (s-1) rate hposF
    (hconj (rate • P) u v hA hu hv hzero)
  have hconvD : ConvexOn ℝ (Ioi 0)
      (fun t => Real.log (density P u v rate t/t^(s-1))) := by
    simpa only [density_uniformization] using hconv
  obtain ⟨c, hc, hdec, hdec'⟩ := density_decay P u v rate hrate hρ
  have h := SSP.MomentReduction.hierarchy_of_logConvex (density P u v rate)
    (densityDeriv P u v rate) (s-1) r
    (density_continuous P u v rate).continuousOn
    (densityDeriv_continuous P u v rate).continuousOn hpos
    (fun t _ => density_hasDerivAt P u v rate t) c hc hdec hdec' hconvD
  have hsR : ((s-1 : ℕ) : ℝ)+1 = s := by
    exact_mod_cast Nat.sub_add_cancel hs
  have h1 : (s+r+1 : ℝ) = ((s-1 : ℕ) : ℝ)+r+2 := by linarith
  have h2 : (s+r : ℝ) = ((s-1 : ℕ) : ℝ)+r+1 := by linarith
  rw [h1, h2]
  exact h

/-- The two-by-two proof supplies the matrix conjecture's exact interface. -/
theorem matrixConjecture_two : MatrixConjecture 2 := by
  intro A u v hA hu hv hne
  simpa only [show 2-1 = 1 by omega, pow_one, pairing, pairingFun_apply, SSP.MatrixTwo.scalar] using
    SSP.MatrixTwo.conjecture_two_two_by_two A u v hA hu hv hne

/-- Conjecture 1 for all two-state phase-type densities and every moment index. -/
theorem conjecture_one_two_state (P : Mat 2) (u v : Fin 2 → ℝ) (rate : ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hrate : 0 < rate)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1) (r : ℕ) :
    (r+3 : ℝ)*SSP.MomentReduction.moment (density P u v rate) (r+1)^2 ≤
      (r+2 : ℝ)*SSP.MomentReduction.moment (density P u v rate) r*
        SSP.MomentReduction.moment (density P u v rate) (r+2) := by
  simpa only [Nat.cast_ofNat, add_comm (2 : ℝ), add_assoc, show (1+2 : ℝ) = 3 by norm_num] using
    conjecture_two_implies_conjecture_one (by norm_num) matrixConjecture_two
      P u v rate hP hu hv hrate hρ r

/-- Raw moments when the law also has an atom at zero. Its zeroth moment includes
that atom, while all positive-order moments are unchanged. -/
noncomputable def rawMoment {s : ℕ} (P : Mat s) (u v : Fin s → ℝ)
    (rate atom : ℝ) (n : ℕ) : ℝ :=
  SSP.MomentReduction.moment (density P u v rate) n + if n = 0 then atom else 0

theorem density_nonneg {s : ℕ} (P : Mat s) (u v : Fin s → ℝ) (rate : ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hrate : 0 < rate) (t : ℝ) (ht : 0 < t) : 0 ≤ density P u v rate t := by
  rw [density_uniformization]
  apply mul_nonneg (Real.exp_pos _).le
  have hs := pairing_series (rate • P) u v t
  rw [← hs.tsum_eq]
  apply tsum_nonneg
  intro n
  exact mul_nonneg (by positivity) (power_pairing_nonneg (rate • P) u v
    (fun i j => mul_nonneg hrate.le (hP i j)) hu hv n)

/-- Conjecture 2 implies the hierarchy including an arbitrary nonnegative atom at zero. -/
theorem hierarchy_with_atom {s : ℕ} (hs : 1 ≤ s) (hconj : MatrixConjecture s)
    (P : Mat s) (u v : Fin s → ℝ) (rate atom : ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1) (r : ℕ) :
    (s+r+1 : ℝ)*rawMoment P u v rate atom (r+1)^2 ≤
      (s+r : ℝ)*rawMoment P u v rate atom r*rawMoment P u v rate atom (r+2) := by
  have h := conjecture_two_implies_conjecture_one hs hconj P u v rate hP hu hv hrate hρ r
  have hn : ∀ n, 0 ≤ SSP.MomentReduction.moment (density P u v rate) n := by
    intro n
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (pow_nonneg ht.le n) (density_nonneg P u v rate hP hu hv hrate t ht)
  simp only [rawMoment, show r+1 ≠ 0 by omega, show r+2 ≠ 0 by omega,
    if_false, add_zero]
  by_cases hr : r = 0
  · subst r
    simp only [Nat.cast_zero, zero_add, add_zero, if_true] at *
    exact h.trans (by nlinarith [mul_nonneg hatom (hn 2), (show (0 : ℝ) ≤ s by positivity)])
  · simpa only [if_neg hr, add_zero] using h

/-- Conjecture 1 in its original adjacent-index and ratio form, for every `k ≥ 1`. -/
theorem conjecture_two_implies_conjecture_one_ratio {s : ℕ} (hs : 1 ≤ s)
    (hconj : MatrixConjecture s) (P : Mat s) (u v : Fin s → ℝ) (rate atom : ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ((s+k : ℕ) : ℝ)/((s+k-1 : ℕ) : ℝ)*rawMoment P u v rate atom k^2 ≤
      rawMoment P u v rate atom (k-1)*rawMoment P u v rate atom (k+1) := by
  have h := hierarchy_with_atom hs hconj P u v rate atom hP hu hv hrate hatom hρ (k-1)
  have hidx : k-1+1 = k := Nat.sub_add_cancel hk
  have hidx2 : k-1+2 = k+1 := by omega
  have hden : (0 : ℝ) < ((s+k-1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < s+k-1 by omega)
  have hcoeff1 : ((s : ℝ)+((k-1 : ℕ) : ℝ)+1) = ((s+k : ℕ) : ℝ) := by
    norm_cast
    omega
  have hcoeff2 : ((s : ℝ)+((k-1 : ℕ) : ℝ)) = ((s+k-1 : ℕ) : ℝ) := by
    norm_cast
    omega
  rw [hidx, hidx2, hcoeff1, hcoeff2] at h
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  convert h using 1 <;> try rfl
  ring

/-- The uniformized density is the original matrix-exponential density. -/
theorem density_eq_matrix_exp {s : ℕ} (P : Mat s) (u v : Fin s → ℝ) (rate t : ℝ) :
    density P u v rate t = dotProduct u
      ((NormedSpace.exp (t • (rate • (P-1)))).mulVec v) := by
  exact pairingFun_apply u v _

/-- The moment inequality of Conjecture 1, in a fixed dimension, including an atom at zero. -/
def MomentConjecture (s : ℕ) : Prop :=
  ∀ (P : Mat s) (u v : Fin s → ℝ) (rate atom : ℝ),
    (∀ i j, 0 ≤ P i j) → (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ v i) →
    0 < rate → 0 ≤ atom → spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1 →
    ∀ k : ℕ, 1 ≤ k →
      ((s+k : ℕ) : ℝ)/((s+k-1 : ℕ) : ℝ)*rawMoment P u v rate atom k^2 ≤
        rawMoment P u v rate atom (k-1)*rawMoment P u v rate atom (k+1)

/-- The dimension-by-dimension logical implication, for all moment indices. -/
theorem matrixConjecture_implies_momentConjecture {s : ℕ} (hs : 1 ≤ s) :
    MatrixConjecture s → MomentConjecture s := by
  intro hconj P u v rate atom hP hu hv hrate hatom hρ k hk
  exact conjecture_two_implies_conjecture_one_ratio hs hconj P u v rate atom
    hP hu hv hrate hatom hρ k hk

/-- Conjecture 1's moment inequality holds in dimension two for every index. -/
theorem momentConjecture_two : MomentConjecture 2 :=
  matrixConjecture_implies_momentConjecture (by norm_num) matrixConjecture_two

/-- The all-dimension form of the implication. -/
theorem all_matrixConjectures_imply_all_momentConjectures
    (hconj : ∀ s : ℕ, 1 ≤ s → MatrixConjecture s) :
    ∀ s : ℕ, 1 ≤ s → MomentConjecture s := by
  intro s hs
  exact matrixConjecture_implies_momentConjecture hs (hconj s hs)

/-- The hierarchy in the original raw-moment notation for a uniformized law.
`hm` is only the definition of its moments, not an assumed moment inequality. -/
theorem hierarchy_for_raw_moments {s : ℕ} (hs : 1 ≤ s) (hconj : MatrixConjecture s)
    (P : Mat s) (u v : Fin s → ℝ) (rate atom : ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1)
    (m : ℕ → ℝ)
    (hm : ∀ n, m n = (∫ t in Ioi (0 : ℝ), t^n*dotProduct u
      ((NormedSpace.exp (t • (rate • (P-1)))).mulVec v)) + if n = 0 then atom else 0)
    (k : ℕ) (hk : 1 ≤ k) :
    ((s+k : ℕ) : ℝ)/((s+k-1 : ℕ) : ℝ)*(m k)^2 ≤ m (k-1)*m (k+1) := by
  have hm' : ∀ n, m n = rawMoment P u v rate atom n := by
    intro n
    simp only [rawMoment, SSP.MomentReduction.moment, density_eq_matrix_exp]
    exact hm n
  simp only [hm']
  exact conjecture_two_implies_conjecture_one_ratio hs hconj P u v rate atom
    hP hu hv hrate hatom hρ k hk

end SSP.MatrixMomentReduction
