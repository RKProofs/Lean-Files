import SSPLean.K3CyclicComplexMiddleTaylorOpposite

/-! # The lower Taylor bound for the complex-middle quantity `middleJ` -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

lemma taylorWithinEval_two_eq
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {omega : ℝ} (homega : 0 < omega) :
    taylorWithinEval f 2 (Set.uIcc 0 omega) 0 omega =
      f 0 + omega * iteratedDeriv 1 f 0 +
        omega ^ 2 / 2 * iteratedDeriv 2 f 0 := by
  have hu : UniqueDiffOn ℝ (Set.uIcc 0 omega) :=
    uniqueDiffOn_Icc (by
      rw [min_eq_left homega.le, max_eq_right homega.le]
      exact homega)
  have hmem : (0 : ℝ) ∈ Set.uIcc 0 omega := by
    simp [Set.uIcc_of_le homega.le, homega.le]
  have h02 : (↑(0 : ℕ) : WithTop ℕ∞) ≤ 2 := by norm_num
  have h12 : (↑(1 : ℕ) : WithTop ℕ∞) ≤ 2 := by norm_num
  have hd0 : iteratedDerivWithin 0 f (Set.uIcc 0 omega) 0 =
      iteratedDeriv 0 f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hf.of_le h02).contDiffAt hmem
  have hd1 : iteratedDerivWithin 1 f (Set.uIcc 0 omega) 0 =
      iteratedDeriv 1 f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hf.of_le h12).contDiffAt hmem
  have hd2 : iteratedDerivWithin 2 f (Set.uIcc 0 omega) 0 =
      iteratedDeriv 2 f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu hf.contDiffAt hmem
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ, hd0, hd1, hd2]
  ring <;> simp

lemma contDiff_affinePower_im_two (K : ℕ) :
    ContDiff ℝ 2 (fun t => (affinePower Complex.I K t).im) := by
  have hcoe : ContDiff ℝ 2 (fun t : ℝ => (t : ℂ)) :=
    Complex.ofRealCLM.contDiff
  have hp : ContDiff ℝ 2 (affinePower Complex.I K) := by
    unfold affinePower
    exact (contDiff_const.add (contDiff_const.mul hcoe)).pow K
  exact Complex.imCLM.contDiff.comp hp

lemma iteratedDeriv_one_affinePower_im (K : ℕ) (t : ℝ) :
    iteratedDeriv 1 (fun s => (affinePower Complex.I K s).im) t =
      (affinePowerD1 Complex.I K t).im := by
  rw [show 1 = 0 + 1 by norm_num, iteratedDeriv_succ']
  simp only [iteratedDeriv_zero]
  exact (HasDerivAt.complex_im (hasDerivAt_affinePower Complex.I K t)).deriv

lemma iteratedDeriv_two_affinePower_im
    {K : ℕ} (hK : 1 ≤ K) (t : ℝ) :
    iteratedDeriv 2 (fun s => (affinePower Complex.I K s).im) t =
      (affinePowerD2 Complex.I K t).im := by
  have hd0 : deriv (fun s => (affinePower Complex.I K s).im) =
      fun s => (affinePowerD1 Complex.I K s).im := by
    funext s
    exact (HasDerivAt.complex_im
      (hasDerivAt_affinePower Complex.I K s)).deriv
  have hd1 : deriv (fun s => (affinePowerD1 Complex.I K s).im) =
      fun s => (affinePowerD2 Complex.I K s).im := by
    funext s
    exact (HasDerivAt.complex_im
      (hasDerivAt_affinePowerD1 Complex.I hK s)).deriv
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ',
    show 1 = 0 + 1 by norm_num, iteratedDeriv_succ', hd0, hd1]
  simp

lemma affinePower_I_im_taylor_two
    {N : ℕ} (hN : 1 ≤ N) {omega : ℝ} (homega : 0 < omega) :
    taylorWithinEval (fun s => (affinePower Complex.I N s).im) 2
      (Set.uIcc 0 omega) 0 omega = (N : ℝ) * omega := by
  rw [taylorWithinEval_two_eq (contDiff_affinePower_im_two N) homega,
    iteratedDeriv_one_affinePower_im,
    iteratedDeriv_two_affinePower_im hN]
  unfold affinePower affinePowerD1 affinePowerD2
  simp
  ring

lemma contDiff_oppositeProduct_im_two (N : ℕ) :
    ContDiff ℝ 2 (fun t => (oppositeProduct N t).im) := by
  have hcoe : ContDiff ℝ 2 (fun t : ℝ => (t : ℂ)) :=
    Complex.ofRealCLM.contDiff
  have hp (c : ℂ) (K : ℕ) : ContDiff ℝ 2 (affinePower c K) := by
    unfold affinePower
    exact (contDiff_const.add (contDiff_const.mul hcoe)).pow K
  exact Complex.imCLM.contDiff.comp
    ((hp (-Complex.I) 2).mul (hp Complex.I (N - 2)))

lemma iteratedDeriv_one_oppositeProduct (N : ℕ) (t : ℝ) :
    iteratedDeriv 1 (fun s => (oppositeProduct N s).im) t =
      (oppositeProductD1 N t).im := by
  rw [show 1 = 0 + 1 by norm_num, iteratedDeriv_succ']
  simp only [iteratedDeriv_zero]
  exact (HasDerivAt.complex_im (hasDerivAt_oppositeProduct t)).deriv

lemma iteratedDeriv_two_oppositeProduct
    {N : ℕ} (hN : 3 ≤ N) (t : ℝ) :
    iteratedDeriv 2 (fun s => (oppositeProduct N s).im) t =
      (oppositeProductD2 N t).im := by
  have hd0 : deriv (fun s => (oppositeProduct N s).im) =
      fun s => (oppositeProductD1 N s).im := by
    funext s
    exact (HasDerivAt.complex_im (hasDerivAt_oppositeProduct s)).deriv
  have hd1 : deriv (fun s => (oppositeProductD1 N s).im) =
      fun s => (oppositeProductD2 N s).im := by
    funext s
    exact (HasDerivAt.complex_im
      (hasDerivAt_oppositeProductD1 hN s)).deriv
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ',
    show 1 = 0 + 1 by norm_num, iteratedDeriv_succ', hd0, hd1]
  simp

lemma oppositeProduct_im_taylor_two
    {N : ℕ} (hN : 3 ≤ N) {omega : ℝ} (homega : 0 < omega) :
    taylorWithinEval (fun s => (oppositeProduct N s).im) 2
      (Set.uIcc 0 omega) 0 omega = ((N : ℝ) - 4) * omega := by
  rw [taylorWithinEval_two_eq (contDiff_oppositeProduct_im_two N) homega,
    iteratedDeriv_one_oppositeProduct,
    iteratedDeriv_two_oppositeProduct hN]
  unfold oppositeProduct oppositeProductD1 oppositeProductD2
  unfold affinePower affinePowerD1 affinePowerD2
  rw [Nat.cast_sub (by omega : 2 ≤ N)]
  norm_num
  ring

lemma middleR_eq_affine_products (N : ℕ) (omega : ℝ) :
    middleR N omega =
      affinePower Complex.I N omega +
        (((N : ℝ) * ((N : ℝ) - 1) / 2 : ℝ) : ℂ) *
          oppositeProduct N omega := by
  unfold middleR geometricPairClosed middleFrequency
  unfold oppositeProduct affinePower
  push_cast
  ring

lemma middleR_im_eq_affine_products (N : ℕ) (omega : ℝ) :
    (middleR N omega).im =
      (affinePower Complex.I N omega).im +
        ((N : ℝ) * ((N : ℝ) - 1) / 2) *
          (oppositeProduct N omega).im := by
  rw [middleR_eq_affine_products]
  simp

theorem middleJ_taylor_lower
    {N : ℕ} (hN : 5 ≤ N) {omega : ℝ} (homega : 0 < omega) :
    middleJ N omega ≥
      (N : ℝ) + ((N : ℝ) * ((N : ℝ) - 1) / 2) * ((N : ℝ) - 4) -
        omega ^ 2 / 6 *
          (1 + (N : ℝ) * ((N : ℝ) - 1) / 2) *
          ((N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2)) *
          Real.sqrt (1 + omega ^ 2) ^ (N - 3) := by
  set M : ℝ := (N : ℝ) * ((N : ℝ) - 1) / 2
  set P : ℝ := (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2)
  set R : ℝ := Real.sqrt (1 + omega ^ 2) ^ (N - 3)
  set L : ℝ := P * R * omega ^ 3 / 6
  have hrem1 := affinePower_I_im_remainder_bound (N := N) (by omega) homega
  rw [affinePower_I_im_taylor_two (by omega) homega] at hrem1
  change |(affinePower Complex.I N omega).im - (N : ℝ) * omega| ≤ L at hrem1
  have hlower1 : (N : ℝ) * omega - L ≤
      (affinePower Complex.I N omega).im := by
    have h := (abs_le.mp hrem1).1
    linarith
  have hrem2 := oppositeProduct_im_remainder_bound hN homega
  rw [oppositeProduct_im_taylor_two (by omega) homega] at hrem2
  change |(oppositeProduct N omega).im - ((N : ℝ) - 4) * omega| ≤ L at hrem2
  have hlower2 : ((N : ℝ) - 4) * omega - L ≤
      (oppositeProduct N omega).im := by
    have h := (abs_le.mp hrem2).1
    linarith
  have hM : 0 ≤ M := by
    have hn : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    dsimp [M]
    have hn0 : 0 ≤ (N : ℝ) := by positivity
    have hn1 : 0 ≤ (N : ℝ) - 1 := by linarith
    exact div_nonneg (mul_nonneg hn0 hn1) (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hlower2 hM
  have herror :
      omega ^ 2 / 6 * (1 + M) * P * R * omega = (1 + M) * L := by
    dsimp [L]
    ring
  unfold middleJ
  apply (le_div_iff₀ homega).2
  rw [middleR_im_eq_affine_products,
    show (N : ℝ) * ((N : ℝ) - 1) / 2 = M by rfl]
  nlinarith

end SSP.K3CyclicComplex.MiddleCoeff
