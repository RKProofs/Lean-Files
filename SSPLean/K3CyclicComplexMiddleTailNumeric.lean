import SSPLean.K3CyclicComplexMiddleBounds

/-! # The uniform numerical domination used in the complex-middle tail -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

noncomputable def tailA (N : ℕ) : ℝ :=
  (N : ℝ) * ((N : ℝ) - 1) + 16

noncomputable def tailM (N : ℕ) : ℝ :=
  1 + (N : ℝ) * ((N : ℝ) - 1) / 2

noncomputable def tailQ (N : ℕ) : ℝ :=
  tailM N * (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2)

noncomputable def tailP (N : ℕ) : ℝ :=
  tailA N + Real.sqrt 3 / 8 * tailQ N

theorem sqrt_three_gt_four_thirds : (4 / 3 : ℝ) < Real.sqrt 3 := by
  have hsqrt0 := Real.sqrt_nonneg 3
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith

theorem tailA_nonneg (N : ℕ) : 0 ≤ tailA N := by
  unfold tailA
  by_cases hN : N = 0
  · subst N
    norm_num
  · have hcast : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN)
    positivity

theorem tailQ_nonneg {N : ℕ} (hN : 2 ≤ N) : 0 ≤ tailQ N := by
  unfold tailQ tailM
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hN1 : 0 ≤ (N : ℝ) - 1 := by linarith
  have hN2 : 0 ≤ (N : ℝ) - 2 := by linarith
  have hM : 0 ≤ 1 + (N : ℝ) * ((N : ℝ) - 1) / 2 :=
    add_nonneg (by norm_num)
      (div_nonneg (mul_nonneg hN0 hN1) (by norm_num))
  positivity

theorem tailP_nonneg {N : ℕ} (hN : 2 ≤ N) : 0 ≤ tailP N := by
  unfold tailP
  exact add_nonneg (tailA_nonneg N)
    (mul_nonneg (div_nonneg (Real.sqrt_nonneg 3) (by norm_num))
      (tailQ_nonneg hN))

theorem tailA_growth {N : ℕ} (hN : 25 ≤ N) :
    3 * tailA (N + 1) ≤ 4 * tailA N := by
  let y : ℝ := (N : ℝ) - 25
  have hy : 0 ≤ y := by
    have hNR : (25 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [y]
    linarith
  have hpoly : 0 ≤ y ^ 2 + 43 * y + 466 := by positivity
  unfold tailA
  push_cast
  dsimp [y] at hpoly
  nlinarith

theorem tailQ_growth {N : ℕ} (hN : 25 ≤ N) :
    3 * tailQ (N + 1) ≤ 4 * tailQ N := by
  let y : ℝ := (N : ℝ) - 25
  have hy : 0 ≤ y := by
    have hNR : (25 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [y]
    linarith
  have hpoly : 0 ≤
      ((N : ℝ) - 1) * (N : ℝ) *
        (y ^ 3 + 57 * y ^ 2 + 982 * y + 4528) / 2 := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans (by omega : 1 ≤ 25) hN)
    positivity
  have hid : 4 * tailQ N - 3 * tailQ (N + 1) =
      ((N : ℝ) - 1) * (N : ℝ) *
        (y ^ 3 + 57 * y ^ 2 + 982 * y + 4528) / 2 := by
    unfold tailQ tailM
    push_cast
    dsimp [y]
    ring
  linarith

theorem tailP_growth {N : ℕ} (hN : 25 ≤ N) :
    tailP (N + 1) ≤ (4 / 3 : ℝ) * tailP N := by
  have hA := tailA_growth hN
  have hQ := tailQ_growth hN
  have hsqrt := Real.sqrt_nonneg 3
  have hc : 0 ≤ Real.sqrt 3 / 8 := div_nonneg hsqrt (by norm_num)
  have hQscaled := mul_le_mul_of_nonneg_left hQ hc
  unfold tailP
  nlinarith

theorem tailP_twenty_five_lt :
    tailP 25 < Real.sqrt 3 ^ 25 := by
  have hsqrt0 := Real.sqrt_nonneg 3
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt1 : (1 : ℝ) < Real.sqrt 3 := by nlinarith
  have hpow : Real.sqrt 3 ^ 25 = 531441 * Real.sqrt 3 := by
    rw [show 25 = 2 * 12 + 1 by norm_num, pow_add, pow_mul, hsqrtSq]
    norm_num
  rw [hpow]
  norm_num [tailP, tailA, tailQ, tailM]
  nlinarith

theorem tailP_lt_sqrt_three_pow {N : ℕ} (hN : 25 ≤ N) :
    tailP N < Real.sqrt 3 ^ N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero => simpa using tailP_twenty_five_lt
  | succ k ih =>
      have ih' := ih (by omega : 25 ≤ 25 + k)
      have hindex : 25 ≤ 25 + k := by omega
      have hgrowth := tailP_growth hindex
      have hpowpos : 0 < Real.sqrt 3 ^ (25 + k) :=
        pow_pos (by positivity) _
      calc
        tailP (25 + (k + 1)) = tailP ((25 + k) + 1) := by congr 1
        _ ≤ (4 / 3 : ℝ) * tailP (25 + k) := hgrowth
        _ < (4 / 3 : ℝ) * Real.sqrt 3 ^ (25 + k) := by
          nlinarith
        _ < Real.sqrt 3 * Real.sqrt 3 ^ (25 + k) := by
          exact mul_lt_mul_of_pos_right sqrt_three_gt_four_thirds hpowpos
        _ = Real.sqrt 3 ^ (25 + (k + 1)) := by
          rw [show 25 + (k + 1) = (25 + k) + 1 by omega, pow_succ]
          ring

end SSP.K3CyclicComplex.MiddleCoeff
