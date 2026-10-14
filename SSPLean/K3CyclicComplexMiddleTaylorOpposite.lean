import SSPLean.K3CyclicComplexMiddleTaylor

/-! # Taylor bound for the opposite-sign middle product -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

noncomputable def oppositeProduct (N : ℕ) (t : ℝ) : ℂ :=
  affinePower (-Complex.I) 2 t * affinePower Complex.I (N - 2) t

noncomputable def oppositeProductD1 (N : ℕ) (t : ℝ) : ℂ :=
  affinePowerD1 (-Complex.I) 2 t * affinePower Complex.I (N - 2) t +
    affinePower (-Complex.I) 2 t * affinePowerD1 Complex.I (N - 2) t

noncomputable def oppositeProductD2 (N : ℕ) (t : ℝ) : ℂ :=
  affinePowerD2 (-Complex.I) 2 t * affinePower Complex.I (N - 2) t +
    2 * affinePowerD1 (-Complex.I) 2 t * affinePowerD1 Complex.I (N - 2) t +
    affinePower (-Complex.I) 2 t * affinePowerD2 Complex.I (N - 2) t

noncomputable def oppositeProductD3 (N : ℕ) (t : ℝ) : ℂ :=
  affinePower (-Complex.I) 2 t * affinePowerD3 Complex.I (N - 2) t +
    3 * affinePowerD1 (-Complex.I) 2 t * affinePowerD2 Complex.I (N - 2) t +
    3 * affinePowerD2 (-Complex.I) 2 t * affinePowerD1 Complex.I (N - 2) t

lemma hasDerivAt_oppositeProduct {N : ℕ} (t : ℝ) :
    HasDerivAt (oppositeProduct N) (oppositeProductD1 N t) t := by
  exact (hasDerivAt_affinePower (-Complex.I) 2 t).mul
    (hasDerivAt_affinePower Complex.I (N - 2) t)

lemma hasDerivAt_oppositeProductD1
    {N : ℕ} (hN : 3 ≤ N) (t : ℝ) :
    HasDerivAt (oppositeProductD1 N) (oppositeProductD2 N t) t := by
  have h :=
    ((hasDerivAt_affinePowerD1 (-Complex.I) (N := 2) (by omega) t).mul
      (hasDerivAt_affinePower Complex.I (N - 2) t)).add
    ((hasDerivAt_affinePower (-Complex.I) 2 t).mul
      (hasDerivAt_affinePowerD1 Complex.I (N := N - 2) (by omega) t))
  unfold oppositeProductD1
  convert h using 1
  · rfl
  · rfl
  · unfold oppositeProductD2
    ring

lemma hasDerivAt_oppositeProductD2
    {N : ℕ} (hN : 5 ≤ N) (t : ℝ) :
    HasDerivAt (oppositeProductD2 N) (oppositeProductD3 N t) t := by
  have h0 :=
    (hasDerivAt_affinePowerD2 (-Complex.I) (N := 2) (by omega) t).mul
      (hasDerivAt_affinePower Complex.I (N - 2) t)
  have h1 := (HasDerivAt.const_mul 2
    ((hasDerivAt_affinePowerD1 (-Complex.I) (N := 2) (by omega) t).mul
      (hasDerivAt_affinePowerD1 Complex.I (N := N - 2) (by omega) t)))
  have h2 :=
    (hasDerivAt_affinePower (-Complex.I) 2 t).mul
      (hasDerivAt_affinePowerD2 Complex.I (N := N - 2) (by omega) t)
  have h := h0.add (h1.add h2)
  unfold oppositeProductD2
  convert h using 1
  · rfl
  · funext s
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  · unfold oppositeProductD3 affinePowerD3
    push_cast
    ring

lemma iteratedDeriv_three_oppositeProduct
    {N : ℕ} (hN : 5 ≤ N) (t : ℝ) :
    iteratedDeriv 3 (oppositeProduct N) t = oppositeProductD3 N t := by
  have hd0 : deriv (oppositeProduct N) = oppositeProductD1 N := by
    funext s
    exact (hasDerivAt_oppositeProduct s).deriv
  have hd1 : deriv (oppositeProductD1 N) = oppositeProductD2 N := by
    funext s
    exact (hasDerivAt_oppositeProductD1 (by omega) s).deriv
  have hd2 : deriv (oppositeProductD2 N) = oppositeProductD3 N := by
    funext s
    exact (hasDerivAt_oppositeProductD2 hN s).deriv
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ',
    show 2 = 1 + 1 by norm_num, iteratedDeriv_succ',
    show 1 = 0 + 1 by norm_num, iteratedDeriv_succ',
    hd0, hd1, hd2]
  simp

lemma iteratedDeriv_three_oppositeProduct_im
    {N : ℕ} (hN : 5 ≤ N) (t : ℝ) :
    iteratedDeriv 3 (fun s => (oppositeProduct N s).im) t =
      (oppositeProductD3 N t).im := by
  have hd0 : deriv (fun s => (oppositeProduct N s).im) =
      fun s => (oppositeProductD1 N s).im := by
    funext s
    exact (HasDerivAt.complex_im (hasDerivAt_oppositeProduct s)).deriv
  have hd1 : deriv (fun s => (oppositeProductD1 N s).im) =
      fun s => (oppositeProductD2 N s).im := by
    funext s
    exact (HasDerivAt.complex_im
      (hasDerivAt_oppositeProductD1 (by omega) s)).deriv
  have hd2 : deriv (fun s => (oppositeProductD2 N s).im) =
      fun s => (oppositeProductD3 N s).im := by
    funext s
    exact (HasDerivAt.complex_im
      (hasDerivAt_oppositeProductD2 hN s)).deriv
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ',
    show 2 = 1 + 1 by norm_num, iteratedDeriv_succ',
    show 1 = 0 + 1 by norm_num, iteratedDeriv_succ',
    hd0, hd1, hd2]
  simp

lemma norm_one_sub_I_mul_real (t : ℝ) :
    ‖(1 : ℂ) - Complex.I * (t : ℂ)‖ = Real.sqrt (1 + t ^ 2) := by
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply]
  ring

lemma norm_affinePower_I (K : ℕ) (t : ℝ) :
    ‖affinePower Complex.I K t‖ =
      Real.sqrt (1 + t ^ 2) ^ K := by
  unfold affinePower
  rw [norm_pow, norm_one_add_I_mul_real]

lemma norm_affinePowerD1_I (K : ℕ) (t : ℝ) :
    ‖affinePowerD1 Complex.I K t‖ =
      (K : ℝ) * Real.sqrt (1 + t ^ 2) ^ (K - 1) := by
  unfold affinePowerD1
  rw [norm_mul, norm_mul, norm_pow, norm_one_add_I_mul_real]
  norm_num

lemma norm_affinePowerD2_I {K : ℕ} (hK : 1 ≤ K) (t : ℝ) :
    ‖affinePowerD2 Complex.I K t‖ =
      (K : ℝ) * ((K : ℝ) - 1) *
        Real.sqrt (1 + t ^ 2) ^ (K - 2) := by
  have hK1 : 0 ≤ (K : ℝ) - 1 := by
    have hk' : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hnorm1 : ‖(K : ℂ) - 1‖ = (K : ℝ) - 1 := by
    rw [show (K : ℂ) - 1 = (((K : ℝ) - 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK1]
  unfold affinePowerD2
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
    norm_one_add_I_mul_real, hnorm1]
  norm_num

lemma norm_affinePowerD3_I {K : ℕ} (hK : 2 ≤ K) (t : ℝ) :
    ‖affinePowerD3 Complex.I K t‖ =
      (K : ℝ) * ((K : ℝ) - 1) * ((K : ℝ) - 2) *
        Real.sqrt (1 + t ^ 2) ^ (K - 3) := by
  have hK1 : 0 ≤ (K : ℝ) - 1 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) hK)
    linarith
  have hK2 : 0 ≤ (K : ℝ) - 2 := by
    have hk' : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hnorm1 : ‖(K : ℂ) - 1‖ = (K : ℝ) - 1 := by
        rw [show (K : ℂ) - 1 = (((K : ℝ) - 1 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK1]
  have hnorm2 : ‖(K : ℂ) - 2‖ = (K : ℝ) - 2 := by
        rw [show (K : ℂ) - 2 = (((K : ℝ) - 2 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK2]
  unfold affinePowerD3
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
    norm_one_add_I_mul_real, hnorm1, hnorm2]
  norm_num

lemma norm_affinePower_negI_two (t : ℝ) :
    ‖affinePower (-Complex.I) 2 t‖ = (1 + t ^ 2) := by
  unfold affinePower
  rw [norm_pow]
  rw [show (1 : ℂ) + -Complex.I * (t : ℂ) =
      1 - Complex.I * (t : ℂ) by ring,
    norm_one_sub_I_mul_real, Real.sq_sqrt (by positivity)]

lemma norm_affinePowerD1_negI_two (t : ℝ) :
    ‖affinePowerD1 (-Complex.I) 2 t‖ =
      2 * Real.sqrt (1 + t ^ 2) := by
  unfold affinePowerD1
  rw [norm_mul, norm_mul, norm_pow]
  rw [show (1 : ℂ) + -Complex.I * (t : ℂ) =
      1 - Complex.I * (t : ℂ) by ring,
    norm_one_sub_I_mul_real]
  norm_num

lemma norm_affinePowerD2_negI_two (t : ℝ) :
    ‖affinePowerD2 (-Complex.I) 2 t‖ = 2 := by
  unfold affinePowerD2
  norm_num

lemma norm_oppositeProductD3_le
    {N : ℕ} (hN : 5 ≤ N) {t omega : ℝ}
    (ht0 : 0 ≤ t) (htomega : t ≤ omega) :
    ‖oppositeProductD3 N t‖ ≤
      (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) *
        Real.sqrt (1 + omega ^ 2) ^ (N - 3) := by
  let s := Real.sqrt (1 + t ^ 2)
  let r := Real.sqrt (1 + omega ^ 2)
  have hsq : t ^ 2 ≤ omega ^ 2 := by nlinarith
  have hsr : s ≤ r := by
    apply Real.sqrt_le_sqrt
    linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hspow : s ^ (N - 3) ≤ r ^ (N - 3) :=
    pow_le_pow_left₀ hs0 hsr _
  have hc : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have he0 :
      ‖affinePower (-Complex.I) 2 t *
          affinePowerD3 Complex.I (N - 2) t‖ =
        ((N : ℝ) - 2) * ((N : ℝ) - 3) * ((N : ℝ) - 4) *
          s ^ (N - 3) := by
    rw [norm_mul, norm_affinePower_negI_two,
      norm_affinePowerD3_I (K := N - 2) (by omega)]
    rw [hc, show N - 2 - 3 = N - 5 by omega]
    change (1 + t ^ 2) *
      (((N : ℝ) - 2) * (((N : ℝ) - 2) - 1) *
        (((N : ℝ) - 2) - 2) * s ^ (N - 5)) = _
    have hssq : s ^ 2 = 1 + t ^ 2 := by
      dsimp [s]
      rw [Real.sq_sqrt (by positivity)]
    conv_lhs => lhs; rw [← hssq]
    calc
      s ^ 2 *
          (((N : ℝ) - 2) * (((N : ℝ) - 2) - 1) *
            (((N : ℝ) - 2) - 2) * s ^ (N - 5)) =
          ((N : ℝ) - 2) * ((N : ℝ) - 3) * ((N : ℝ) - 4) *
            (s ^ 2 * s ^ (N - 5)) := by ring
      _ = ((N : ℝ) - 2) * ((N : ℝ) - 3) * ((N : ℝ) - 4) *
            s ^ (N - 3) := by
        rw [← pow_add]
        congr 2
        omega
  have he1 :
      ‖3 * affinePowerD1 (-Complex.I) 2 t *
          affinePowerD2 Complex.I (N - 2) t‖ =
        6 * ((N : ℝ) - 2) * ((N : ℝ) - 3) * s ^ (N - 3) := by
    rw [norm_mul, norm_mul, norm_affinePowerD1_negI_two,
      norm_affinePowerD2_I (K := N - 2) (by omega)]
    norm_num
    rw [hc, show N - 2 - 2 = N - 4 by omega]
    calc
      3 * (2 * s) *
          (((N : ℝ) - 2) * (((N : ℝ) - 2) - 1) * s ^ (N - 4)) =
          6 * ((N : ℝ) - 2) * ((N : ℝ) - 3) *
            (s ^ 1 * s ^ (N - 4)) := by ring
      _ = 6 * ((N : ℝ) - 2) * ((N : ℝ) - 3) * s ^ (N - 3) := by
        rw [← pow_add]
        congr 2
        omega
  have he2 :
      ‖3 * affinePowerD2 (-Complex.I) 2 t *
          affinePowerD1 Complex.I (N - 2) t‖ =
        6 * ((N : ℝ) - 2) * s ^ (N - 3) := by
    rw [norm_mul, norm_mul, norm_affinePowerD2_negI_two,
      norm_affinePowerD1_I]
    norm_num
    rw [hc, show N - 2 - 1 = N - 3 by omega]
    ring
  have hc0 : 0 ≤ ((N : ℝ) - 2) * ((N : ℝ) - 3) * ((N : ℝ) - 4) := by
    have hn : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : 0 ≤ (N : ℝ) - 2 := by linarith
    have h3 : 0 ≤ (N : ℝ) - 3 := by linarith
    have h4 : 0 ≤ (N : ℝ) - 4 := by linarith
    exact mul_nonneg (mul_nonneg h2 h3) h4
  have hc1 : 0 ≤ 6 * ((N : ℝ) - 2) * ((N : ℝ) - 3) := by
    have hn : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : 0 ≤ (N : ℝ) - 2 := by linarith
    have h3 : 0 ≤ (N : ℝ) - 3 := by linarith
    positivity
  have hc2 : 0 ≤ 6 * ((N : ℝ) - 2) := by
    have hn : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : 0 ≤ (N : ℝ) - 2 := by linarith
    positivity
  have hb0 := mul_le_mul_of_nonneg_left hspow hc0
  have hb1 := mul_le_mul_of_nonneg_left hspow hc1
  have hb2 := mul_le_mul_of_nonneg_left hspow hc2
  unfold oppositeProductD3
  calc
    ‖affinePower (-Complex.I) 2 t * affinePowerD3 Complex.I (N - 2) t +
        3 * affinePowerD1 (-Complex.I) 2 t * affinePowerD2 Complex.I (N - 2) t +
        3 * affinePowerD2 (-Complex.I) 2 t * affinePowerD1 Complex.I (N - 2) t‖ ≤
      ‖affinePower (-Complex.I) 2 t * affinePowerD3 Complex.I (N - 2) t‖ +
        ‖3 * affinePowerD1 (-Complex.I) 2 t * affinePowerD2 Complex.I (N - 2) t‖ +
        ‖3 * affinePowerD2 (-Complex.I) 2 t * affinePowerD1 Complex.I (N - 2) t‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ (((N : ℝ) - 2) * ((N : ℝ) - 3) * ((N : ℝ) - 4) +
          6 * ((N : ℝ) - 2) * ((N : ℝ) - 3) +
          6 * ((N : ℝ) - 2)) * r ^ (N - 3) := by
      rw [he0, he1, he2]
      nlinarith
    _ = (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) *
          Real.sqrt (1 + omega ^ 2) ^ (N - 3) := by
      dsimp [r]
      ring

lemma oppositeProduct_im_lagrange
    {N : ℕ} (hN : 5 ≤ N) {omega : ℝ} (homega : 0 < omega) :
    ∃ t ∈ Set.Ioo (0 : ℝ) omega,
      (oppositeProduct N omega).im -
          taylorWithinEval (fun s => (oppositeProduct N s).im) 2
            (Set.uIcc 0 omega) 0 omega =
        (oppositeProductD3 N t).im * omega ^ 3 / 6 := by
  have hcont : ContDiffOn ℝ 3
      (fun s => (oppositeProduct N s).im) (Set.uIcc 0 omega) := by
    have hcoe : ContDiff ℝ 3 (fun t : ℝ => (t : ℂ)) :=
      Complex.ofRealCLM.contDiff
    have hp (c : ℂ) (K : ℕ) : ContDiff ℝ 3 (affinePower c K) := by
      unfold affinePower
      exact (contDiff_const.add (contDiff_const.mul hcoe)).pow K
    have hprod : ContDiff ℝ 3 (oppositeProduct N) := by
      exact (hp (-Complex.I) 2).mul (hp Complex.I (N - 2))
    exact (Complex.imCLM.contDiff.comp hprod).contDiffOn
  obtain ⟨t, ht, heq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := fun s => (oppositeProduct N s).im)
      (n := 2) (x₀ := 0) (x := omega) (by linarith) hcont
  refine ⟨t, ?_, ?_⟩
  · simpa [Set.uIoo_of_le homega.le] using ht
  · rw [iteratedDeriv_three_oppositeProduct_im hN] at heq
    norm_num at heq ⊢
    simpa [mul_assoc] using heq

lemma oppositeProduct_im_remainder_bound
    {N : ℕ} (hN : 5 ≤ N) {omega : ℝ} (homega : 0 < omega) :
    |(oppositeProduct N omega).im -
        taylorWithinEval (fun s => (oppositeProduct N s).im) 2
          (Set.uIcc 0 omega) 0 omega| ≤
      (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) *
        Real.sqrt (1 + omega ^ 2) ^ (N - 3) * omega ^ 3 / 6 := by
  obtain ⟨t, ht, heq⟩ := oppositeProduct_im_lagrange hN homega
  rw [heq, abs_div, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ omega ^ 3),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
  have him : |(oppositeProductD3 N t).im| ≤
      ‖oppositeProductD3 N t‖ := Complex.abs_im_le_norm _
  have hnorm := norm_oppositeProductD3_le hN ht.1.le ht.2.le
  have hscale : 0 ≤ omega ^ 3 / 6 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (him.trans hnorm) hscale]

end SSP.K3CyclicComplex.MiddleCoeff
