import SSPLean.K3CyclicComplexMiddlePairingReal
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.RealDeriv

/-! # Third-order Taylor bounds for the complex-middle remainder -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

noncomputable def affinePower (c : ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  (1 + c * (t : ℂ)) ^ N

noncomputable def affinePowerD1 (c : ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  (N : ℂ) * c * (1 + c * (t : ℂ)) ^ (N - 1)

noncomputable def affinePowerD2 (c : ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  (N : ℂ) * ((N : ℂ) - 1) * c ^ 2 *
    (1 + c * (t : ℂ)) ^ (N - 2)

noncomputable def affinePowerD3 (c : ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  (N : ℂ) * ((N : ℂ) - 1) * ((N : ℂ) - 2) * c ^ 3 *
    (1 + c * (t : ℂ)) ^ (N - 3)

lemma hasDerivAt_affineBase (c : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 + c * (s : ℂ)) c t := by
  have h := HasDerivAt.const_mul c (hasDerivAt_id t).ofReal_comp
  simpa [add_comm] using h.add_const (1 : ℂ)

lemma hasDerivAt_affinePower (c : ℂ) (N : ℕ) (t : ℝ) :
    HasDerivAt (affinePower c N) (affinePowerD1 c N t) t := by
  unfold affinePower affinePowerD1
  simpa [mul_assoc, mul_comm, mul_left_comm] using!
    (hasDerivAt_affineBase c t).pow N

lemma hasDerivAt_affinePowerD1
    (c : ℂ) {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    HasDerivAt (affinePowerD1 c N) (affinePowerD2 c N t) t := by
  unfold affinePowerD1 affinePowerD2
  have hpow := (hasDerivAt_affineBase c t).pow (N - 1)
  have h := HasDerivAt.const_mul ((N : ℂ) * c) hpow
  convert! h using 1
  · rw [Nat.cast_sub hN]
    rw [show N - 1 - 1 = N - 2 by omega]
    ring

lemma hasDerivAt_affinePowerD2
    (c : ℂ) {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    HasDerivAt (affinePowerD2 c N) (affinePowerD3 c N t) t := by
  unfold affinePowerD2 affinePowerD3
  have hpow := (hasDerivAt_affineBase c t).pow (N - 2)
  have h := HasDerivAt.const_mul
    ((N : ℂ) * ((N : ℂ) - 1) * c ^ 2) hpow
  convert! h using 1
  · rw [Nat.cast_sub hN]
    rw [show N - 2 - 1 = N - 3 by omega]
    ring

lemma iteratedDeriv_three_affinePower
    (c : ℂ) {N : ℕ} (hN : 3 ≤ N) (t : ℝ) :
    iteratedDeriv 3 (affinePower c N) t = affinePowerD3 c N t := by
  have hd0 : deriv (affinePower c N) = affinePowerD1 c N := by
    funext s
    exact (hasDerivAt_affinePower c N s).deriv
  have hd1 : deriv (affinePowerD1 c N) = affinePowerD2 c N := by
    funext s
    exact (hasDerivAt_affinePowerD1 c (by omega) s).deriv
  have hd2 : deriv (affinePowerD2 c N) = affinePowerD3 c N := by
    funext s
    exact (hasDerivAt_affinePowerD2 c (by omega) s).deriv
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ',
    show 2 = 1 + 1 by norm_num, iteratedDeriv_succ',
    show 1 = 0 + 1 by norm_num, iteratedDeriv_succ',
    hd0, hd1, hd2]
  simp

lemma HasDerivAt.complex_im
    {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).im) f'.im t := by
  have hf := Complex.imCLM.hasFDerivAt.comp t h.hasFDerivAt
  convert! hf.hasDerivAt using 1
  change f'.im = Complex.imCLM
    (ContinuousLinearMap.toSpanSingleton ℝ f' 1)
  rw [ContinuousLinearMap.toSpanSingleton_apply_one]
  rfl

lemma iteratedDeriv_three_affinePower_im
    (c : ℂ) {N : ℕ} (hN : 3 ≤ N) (t : ℝ) :
    iteratedDeriv 3 (fun s => (affinePower c N s).im) t =
      (affinePowerD3 c N t).im := by
  have hd0 : deriv (fun s => (affinePower c N s).im) =
      fun s => (affinePowerD1 c N s).im := by
    funext s
    exact (HasDerivAt.complex_im
      (hasDerivAt_affinePower c N s)).deriv
  have hd1 : deriv (fun s => (affinePowerD1 c N s).im) =
      fun s => (affinePowerD2 c N s).im := by
    funext s
    exact (HasDerivAt.complex_im
      (hasDerivAt_affinePowerD1 c (N := N) (by omega) s)).deriv
  have hd2 : deriv (fun s => (affinePowerD2 c N s).im) =
      fun s => (affinePowerD3 c N s).im := by
    funext s
    exact (HasDerivAt.complex_im
      (hasDerivAt_affinePowerD2 c (N := N) (by omega) s)).deriv
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ',
    show 2 = 1 + 1 by norm_num, iteratedDeriv_succ',
    show 1 = 0 + 1 by norm_num, iteratedDeriv_succ',
    hd0, hd1, hd2]
  simp

lemma norm_one_add_I_mul_real (t : ℝ) :
    ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ = Real.sqrt (1 + t ^ 2) := by
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply]
  ring

lemma norm_affinePowerD3_I_le
    {N : ℕ} (hN : 3 ≤ N) {t omega : ℝ}
    (ht0 : 0 ≤ t) (htomega : t ≤ omega) :
    ‖affinePowerD3 Complex.I N t‖ ≤
      (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) *
        Real.sqrt (1 + omega ^ 2) ^ (N - 3) := by
  have homega0 : 0 ≤ omega := le_trans ht0 htomega
  have hsq : t ^ 2 ≤ omega ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (1 + t ^ 2) ≤ Real.sqrt (1 + omega ^ 2) := by
    exact Real.sqrt_le_sqrt (by linarith)
  have hpow := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt (N - 3)
  unfold affinePowerD3
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow,
    norm_pow, norm_one_add_I_mul_real]
  norm_num
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : 0 ≤ (N : ℝ) - 1 := by linarith
  have hN2 : 0 ≤ (N : ℝ) - 2 := by linarith
  have hnorm1 : ‖(N : ℂ) - 1‖ = (N : ℝ) - 1 := by
    rw [show (N : ℂ) - 1 = (((N : ℝ) - 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN1]
  have hnorm2 : ‖(N : ℂ) - 2‖ = (N : ℝ) - 2 := by
    rw [show (N : ℂ) - 2 = (((N : ℝ) - 2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN2]
  rw [hnorm1, hnorm2]
  exact mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (mul_nonneg (by positivity) hN1) hN2)

lemma affinePower_I_im_lagrange
    {N : ℕ} (hN : 3 ≤ N) {omega : ℝ} (homega : 0 < omega) :
    ∃ t ∈ Set.Ioo (0 : ℝ) omega,
      (affinePower Complex.I N omega).im -
          taylorWithinEval (fun s => (affinePower Complex.I N s).im) 2
            (Set.uIcc 0 omega) 0 omega =
        (affinePowerD3 Complex.I N t).im * omega ^ 3 / 6 := by
  have hcont : ContDiffOn ℝ 3
      (fun s => (affinePower Complex.I N s).im) (Set.uIcc 0 omega) := by
    have hinner : ContDiff ℝ 3 (affinePower Complex.I N) := by
      unfold affinePower
      have hcoe : ContDiff ℝ 3 (fun t : ℝ => (t : ℂ)) :=
        Complex.ofRealCLM.contDiff
      exact (contDiff_const.add (contDiff_const.mul hcoe)).pow N
    exact (Complex.imCLM.contDiff.comp hinner).contDiffOn
  obtain ⟨t, ht, heq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := fun s => (affinePower Complex.I N s).im)
      (n := 2) (x₀ := 0) (x := omega) (by linarith) hcont
  refine ⟨t, ?_, ?_⟩
  · simpa [Set.uIoo_of_le homega.le] using ht
  · rw [iteratedDeriv_three_affinePower_im Complex.I hN] at heq
    norm_num at heq ⊢
    simpa [mul_assoc] using heq

lemma affinePower_I_im_remainder_bound
    {N : ℕ} (hN : 3 ≤ N) {omega : ℝ} (homega : 0 < omega) :
    |(affinePower Complex.I N omega).im -
        taylorWithinEval (fun s => (affinePower Complex.I N s).im) 2
          (Set.uIcc 0 omega) 0 omega| ≤
      (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) *
        Real.sqrt (1 + omega ^ 2) ^ (N - 3) * omega ^ 3 / 6 := by
  obtain ⟨t, ht, heq⟩ := affinePower_I_im_lagrange hN homega
  rw [heq, abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ omega ^ 3),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
  have him : |(affinePowerD3 Complex.I N t).im| ≤
      ‖affinePowerD3 Complex.I N t‖ := Complex.abs_im_le_norm _
  have hnorm := norm_affinePowerD3_I_le hN ht.1.le ht.2.le
  have hscale : 0 ≤ omega ^ 3 / 6 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (him.trans hnorm) hscale]

end SSP.K3CyclicComplex.MiddleCoeff
