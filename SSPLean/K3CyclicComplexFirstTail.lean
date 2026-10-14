import SSPLean.K3CyclicComplexFirst

/-! # Analytic tail estimates for the complex first start -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex

open Finset Real SSP.K3Cyclic

theorem firstU_lower_bound {m ω x : ℝ}
    (hdom : FirstDomain m ω) (hx : 0 ≤ x) :
    1 - (x * Real.sqrt (firstA m ω)) ^ 2 / 2 -
        (3 / 2) * (x * Real.sqrt (firstA m ω)) ≤ firstU m ω x := by
  rcases hdom.bounds with ⟨hA0, _hz1, _hA1, hgap, hmplus, _hcoef⟩
  have hmpos : 0 < m + 1 := by linarith
  have hsqrt0 : 0 ≤ Real.sqrt (firstA m ω) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (firstA m ω) ^ 2 = firstA m ω :=
    Real.sq_sqrt hA0
  have habsgap : |ω ^ 2 - m| ≤ Real.sqrt (firstA m ω) := by
    nlinarith [sq_abs (ω ^ 2 - m)]
  have hratio : |(ω ^ 2 - m) / (m + 1)| ≤
      (3 / 2) * Real.sqrt (firstA m ω) := by
    rw [abs_div, abs_of_pos hmpos, div_le_iff₀ hmpos]
    have hp := mul_le_mul_of_nonneg_left hmplus hsqrt0
    nlinarith
  have hsinc := abs_sinc_le_abs ω x
  rw [abs_of_nonneg hx] at hsinc
  have hprod :
      |(ω ^ 2 - m) / (m + 1)| * |sinc ω x| ≤
        (3 / 2) * Real.sqrt (firstA m ω) * x :=
    mul_le_mul hratio hsinc (abs_nonneg _) (by positivity)
  have hlower :
      -((3 / 2) * Real.sqrt (firstA m ω) * x) ≤
        (ω ^ 2 - m) / (m + 1) * sinc ω x := by
    have habs := neg_abs_le
      ((ω ^ 2 - m) / (m + 1) * sinc ω x)
    rw [abs_mul] at habs
    linarith
  have hcos : 1 - (ω * x) ^ 2 / 2 ≤ Real.cos (ω * x) :=
    Real.one_sub_sq_div_two_le_cos
  rw [firstU]
  have hzA : ω ^ 2 ≤ firstA m ω := by
    unfold firstA
    nlinarith [sq_nonneg m]
  have hzx : (ω * x) ^ 2 ≤
      (x * Real.sqrt (firstA m ω)) ^ 2 := by
    have hp := mul_le_mul_of_nonneg_left hzA (sq_nonneg x)
    nlinarith
  nlinarith

private noncomputable def expTailPoly (y : ℝ) : ℝ :=
  4867444783 / 5108103 +
  (20752810261 / 1702701) * y +
  (4047830123 / 486486) * y ^ 2 +
  (28840781 / 10206) * y ^ 3 +
  (95423081 / 149688) * y ^ 4 +
  (7281587 / 68040) * y ^ 5 +
  (5719087 / 408240) * y ^ 6 +
  (461843 / 317520) * y ^ 7 +
  (305593 / 2540160) * y ^ 8 +
  (25799 / 3265920) * y ^ 9 +
  (4433 / 10886400) * y ^ 10 +
  (1933 / 119750400) * y ^ 11 +
  (683 / 1437004800) * y ^ 12 +
  (61 / 6227020800) * y ^ 13 +
  (1 / 7925299200) * y ^ 14 +
  (1 / 1307674368000) * y ^ 15

private theorem expTailPoly_nonneg {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ expTailPoly y := by
  unfold expTailPoly
  positivity

/-- A rational Taylor lower bound tailored to the tail threshold. -/
theorem two_mul_pow_four_le_exp {x : ℝ} (hx : 10 ≤ x) :
    2 * x ^ 4 ≤ Real.exp x := by
  have hx0 : 0 ≤ x := by linarith
  have hseries := Real.sum_le_exp_of_nonneg hx0 16
  apply le_trans ?_ hseries
  have hp := expTailPoly_nonneg (y := x - 10) (by linarith)
  have hdiff : 0 ≤ (∑ i ∈ Finset.range 16, x ^ i / i.factorial) - 2 * x ^ 4 := by
    convert hp using 1
    · norm_num [Finset.sum_range_succ, Nat.factorial]
      unfold expTailPoly
      ring
  exact sub_nonneg.mp hdiff

theorem exp_neg_lt_one_eighth {x : ℝ} (hx : 10 ≤ x) :
    Real.exp (-x) < 1 / 8 := by
  have hE := two_mul_pow_four_le_exp hx
  have hx4 : 10000 ≤ x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 100)]
  have hE8 : 8 < Real.exp x := by nlinarith
  rw [Real.exp_neg]
  rw [one_div]
  exact (inv_lt_inv₀ (Real.exp_pos x) (by norm_num)).2 hE8

theorem firstU_small_forces_scaledA {m ω x : ℝ}
    (hdom : FirstDomain m ω) (hx : 10 ≤ x)
    (hU : firstU m ω x < Real.exp (-x)) :
    1 / 2 < x * Real.sqrt (firstA m ω) := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ x * Real.sqrt (firstA m ω) :=
    mul_nonneg hx0 (Real.sqrt_nonneg _)
  have hlower := firstU_lower_bound hdom hx0
  have hexp := exp_neg_lt_one_eighth hx
  nlinarith [sq_nonneg (x * Real.sqrt (firstA m ω) - 1 / 2)]

theorem firstH_lower_bound {m ω x : ℝ}
    (hdom : FirstDomain m ω) (hx : 10 ≤ x) :
    (9 / 10) * firstA m ω * Real.exp x ≤ firstH m ω x := by
  rcases hdom with ⟨hm0, hm1, hz0, hzlower, hzupper⟩
  have hdom' : FirstDomain m ω := ⟨hm0, hm1, hz0, hzlower, hzupper⟩
  rcases hdom'.bounds with ⟨hA0, _hz1, _hA1, _hgap, hmplus, _hcoef⟩
  have hmne : m + 1 ≠ 0 := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hmcoef0 : 0 ≤ 1 - m ^ 2 := by nlinarith
  have hmcoef1 : 1 - m ^ 2 ≤ 1 := by nlinarith [sq_nonneg m]
  have hsincAbs := abs_sinc_le_abs ω x
  rw [abs_of_nonneg hx0] at hsincAbs
  have hsincUpper : sinc ω x ≤ x := le_trans (le_abs_self _) hsincAbs
  have hTidentity := firstT_eq_U (m := m) (ω := ω) (x := x) hmne
  have hE := two_mul_pow_four_le_exp hx
  have hx2 : (10 : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) hx 2
  have hx3 : (10 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
  have hx2mul := mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)
  have hx3mul := mul_le_mul_of_nonneg_right hx3 hx0
  have hbudget :
      10 * ((17 / 16) * x ^ 2 + 2 * x) ≤ Real.exp x := by
    nlinarith [hx2mul, hx3mul]
  rw [firstH]
  by_cases hU : 0 ≤ firstU m ω x
  · have hpositive : 0 ≤ (1 - m ^ 2) * firstU m ω x :=
      mul_nonneg hmcoef0 hU
    have hsincTerm : -2 * firstA m ω * x ≤
        -2 * firstA m ω * sinc ω x :=
      mul_le_mul_of_nonpos_left hsincUpper (by nlinarith)
    rw [hTidentity]
    nlinarith
  · have hUneg : firstU m ω x < 0 := lt_of_not_ge hU
    have hUlower := firstU_lower_bound hdom' hx0
    let y := x * Real.sqrt (firstA m ω)
    have hy0 : 0 ≤ y := by
      dsimp [y]
      positivity
    have hG : -(17 / 16) * y ^ 2 ≤ firstU m ω x := by
      dsimp [y] at hUlower ⊢
      nlinarith [sq_nonneg (3 * (x * Real.sqrt (firstA m ω)) - 4)]
    have hcoefU : firstU m ω x ≤
        (1 - m ^ 2) * firstU m ω x := by
      have hmul := mul_le_mul_of_nonpos_right hmcoef1 hUneg.le
      simpa using hmul
    have hySq : y ^ 2 = x ^ 2 * firstA m ω := by
      dsimp [y]
      rw [mul_pow, Real.sq_sqrt hA0]
    have hsincTerm : -2 * firstA m ω * x ≤
        -2 * firstA m ω * sinc ω x :=
      mul_le_mul_of_nonpos_left hsincUpper (by nlinarith)
    have hGU : -(17 / 16) * y ^ 2 ≤
        (1 - m ^ 2) * firstU m ω x := le_trans hG hcoefU
    rw [hySq] at hGU
    have hTlower :
        -firstA m ω * ((17 / 16) * x ^ 2 + 2 * x) ≤
          (1 - m ^ 2) * firstU m ω x -
            2 * firstA m ω * sinc ω x := by
      nlinarith
    have hbudgetA := mul_le_mul_of_nonneg_left hbudget hA0
    have hsmall :
        firstA m ω * ((17 / 16) * x ^ 2 + 2 * x) ≤
          (1 / 10) * (firstA m ω * Real.exp x) := by
      calc
        firstA m ω * ((17 / 16) * x ^ 2 + 2 * x) =
            (1 / 10) * (firstA m ω *
              (10 * ((17 / 16) * x ^ 2 + 2 * x))) := by ring
        _ ≤ (1 / 10) * (firstA m ω * Real.exp x) :=
          mul_le_mul_of_nonneg_left hbudgetA (by norm_num)
    rw [hTidentity]
    calc
      (9 / 10) * firstA m ω * Real.exp x =
          firstA m ω * Real.exp x -
            (1 / 10) * (firstA m ω * Real.exp x) := by ring
      _ ≤ firstA m ω * Real.exp x -
          firstA m ω * ((17 / 16) * x ^ 2 + 2 * x) :=
        sub_le_sub_left hsmall _
      _ = firstA m ω * Real.exp x +
          (-firstA m ω * ((17 / 16) * x ^ 2 + 2 * x)) := by ring
      _ ≤ firstA m ω * Real.exp x +
          ((1 - m ^ 2) * firstU m ω x -
            2 * firstA m ω * sinc ω x) := by
        simpa only [add_comm] using
          add_le_add_left hTlower (firstA m ω * Real.exp x)

/-- The scalar bracket occurring in the `U < 0` part of the analytic tail
is already positive under the preceding exponential lower bound. -/
theorem negativeU_scalar_bracket_pos {x : ℝ} (hx : 10 ≤ x) :
    0 < 3 * Real.exp (2 * x) / (2 * x ^ 4) -
      (68 / 27) * Real.exp x - 256 / 27 := by
  have hx0 : 0 < x := by linarith
  have hx4 : 0 < x ^ 4 := pow_pos hx0 _
  have hE0 : 0 < Real.exp x := Real.exp_pos _
  have hE := two_mul_pow_four_le_exp hx
  have hE2 : 2 * x ^ 4 * Real.exp x ≤ Real.exp x ^ 2 := by
    nlinarith
  have hx4large : 10000 ≤ x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 100)]
  have hElarge : 20000 ≤ Real.exp x := by nlinarith
  rw [show (2 * x : ℝ) = x + x by ring, Real.exp_add]
  rw [sub_sub, sub_pos, lt_div_iff₀ (mul_pos (by norm_num) hx4)]
  nlinarith

/-- The scalar estimate used when the oscillator companion is nonnegative. -/
theorem nonnegativeU_scalar_pos {A x : ℝ}
    (hA : 0 ≤ A) (hx : 10 ≤ x) (hy : 1 / 4 < x ^ 2 * A) :
    0 < (3 / 2) * A ^ 2 * Real.exp (2 * x) -
      (64 / 27) * x ^ 2 * A := by
  have hx0 : 0 < x := by linarith
  have hx2 : 100 ≤ x ^ 2 := by nlinarith
  have hApos : 0 < A := by
    by_contra h
    have : A ≤ 0 := le_of_not_gt h
    nlinarith [mul_nonneg (sq_nonneg x) hA]
  have hE := two_mul_pow_four_le_exp hx
  have hEpow0 := mul_self_le_mul_self (by positivity : 0 ≤ 2 * x ^ 4) hE
  have hEpow : 4 * x ^ 8 ≤ Real.exp x ^ 2 := by
    nlinarith [hEpow0]
  have hmul := mul_le_mul_of_nonneg_left hEpow hA
  have hcore : 0 < (3 / 2) * A * Real.exp x ^ 2 - (64 / 27) * x ^ 2 := by
    have hx6 : 0 < x ^ 6 := pow_pos hx0 _
    have hq := mul_lt_mul_of_pos_right hy hx6
    have hAE : x ^ 6 < A * Real.exp x ^ 2 := by
      nlinarith [hq, hmul]
    have hx4 : 10000 ≤ x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 100)]
    have hx6large := mul_le_mul_of_nonneg_left hx4 (sq_nonneg x)
    nlinarith [hx6large]
  rw [show (2 * x : ℝ) = x + x by ring, Real.exp_add]
  have hfactor :
      (3 / 2) * A ^ 2 * (Real.exp x * Real.exp x) -
          (64 / 27) * x ^ 2 * A =
        A * ((3 / 2) * A * Real.exp x ^ 2 - (64 / 27) * x ^ 2) := by ring
  rw [hfactor]
  exact mul_pos hApos hcore

/-- Complete analytic tail of the complex-pair first-start certificate. -/
theorem firstH_correctedCurvature3_nonneg_tail
    {m ω x : ℝ} (hdom : FirstDomain m ω) (hx : 10 ≤ x) (hω : ω ≠ 0) :
    0 ≤ correctedCurvature3 x
      (firstH m ω x) (firstH1 m ω x) (firstH2 m ω x) := by
  rcases hdom.bounds with ⟨hA0, _hz1, _hA1, _hgap, hmplus, hCupper⟩
  have hmpos : 0 < m + 1 := by linarith
  have hmne : m + 1 ≠ 0 := hmpos.ne'
  have hx0 : 0 < x := by linarith
  have hC0 : 0 ≤ (m + 1) ^ 2 * (1 + ω ^ 2) := by positivity
  have hP0 : 0 ≤ x ^ 2 * firstA m ω := mul_nonneg (sq_nonneg x) hA0
  have hE0 : 0 < Real.exp x := Real.exp_pos _
  have hH := firstH_lower_bound hdom hx
  have hbase0 : 0 ≤ (9 / 10) * firstA m ω * Real.exp x := by positivity
  have hH0 : 0 ≤ firstH m ω x := le_trans hbase0 hH
  have hHsq := mul_self_le_mul_self hbase0 hH
  rw [firstH_correctedCurvature3_eq hω, firstCompanion_eq_U hmne]
  rw [show
      2 * firstH m ω x ^ 2 +
          x ^ 2 * firstA m ω * (m + 1) * (1 + ω ^ 2) *
            (Real.exp x * ((m + 1) * firstU m ω x) - (m + 1)) =
        2 * firstH m ω x ^ 2 +
          (x ^ 2 * firstA m ω) * ((m + 1) ^ 2 * (1 + ω ^ 2)) *
            (Real.exp x * firstU m ω x - 1) by ring]
  by_cases hbracket : 0 ≤ Real.exp x * firstU m ω x - 1
  · positivity
  have hbracketNeg : Real.exp x * firstU m ω x - 1 < 0 :=
    lt_of_not_ge hbracket
  have hUsmall : firstU m ω x < Real.exp (-x) := by
    have hdiv : firstU m ω x < 1 / Real.exp x := by
      rw [lt_div_iff₀ hE0]
      linarith
    rw [Real.exp_neg]
    simpa only [one_div] using hdiv
  have hy := firstU_small_forces_scaledA hdom hx hUsmall
  have hsqrtSq : Real.sqrt (firstA m ω) ^ 2 = firstA m ω :=
    Real.sq_sqrt hA0
  have hP : 1 / 4 < x ^ 2 * firstA m ω := by
    have hsquare := mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hy
    nlinarith
  by_cases hU : 0 ≤ firstU m ω x
  · have hBLower : -(1 : ℝ) ≤ Real.exp x * firstU m ω x - 1 := by
      have : 0 ≤ Real.exp x * firstU m ω x := mul_nonneg hE0.le hU
      linarith
    have hCB := mul_le_mul_of_nonneg_left hBLower hC0
    have hPCB := mul_le_mul_of_nonneg_left hCB hP0
    have hPCupper := mul_le_mul_of_nonneg_left hCupper hP0
    have hneg :
        -(64 / 27) * (x ^ 2 * firstA m ω) ≤
          (x ^ 2 * firstA m ω) * ((m + 1) ^ 2 * (1 + ω ^ 2)) *
            (Real.exp x * firstU m ω x - 1) := by
      nlinarith
    have hscalar := nonnegativeU_scalar_pos hA0 hx hP
    rw [show (2 * x : ℝ) = x + x by ring, Real.exp_add] at hscalar
    nlinarith
  · have hUneg : firstU m ω x < 0 := lt_of_not_ge hU
    have hUlower := firstU_lower_bound hdom hx0.le
    have hUcoarse :
        -(17 / 16) * (x ^ 2 * firstA m ω) ≤ firstU m ω x := by
      nlinarith [sq_nonneg (3 * (x * Real.sqrt (firstA m ω)) - 4)]
    have hBLower :
        -(1 + (17 / 16) * Real.exp x * (x ^ 2 * firstA m ω)) ≤
          Real.exp x * firstU m ω x - 1 := by
      have hmul := mul_le_mul_of_nonneg_left hUcoarse hE0.le
      nlinarith
    let P := x ^ 2 * firstA m ω
    let C := (m + 1) ^ 2 * (1 + ω ^ 2)
    let B := Real.exp x * firstU m ω x - 1
    have hLnonpos :
        -(1 + (17 / 16) * Real.exp x * P) ≤ 0 := by
      have : 0 ≤ 1 + (17 / 16) * Real.exp x * P := by
        dsimp [P]
        positivity
      linarith
    have hCL := mul_le_mul_of_nonpos_right hCupper hLnonpos
    have hCB : C * (-(1 + (17 / 16) * Real.exp x * P)) ≤ C * B := by
      apply mul_le_mul_of_nonneg_left
      · simpa [P, B] using hBLower
      · dsimp [C]
        positivity
    have hLower :
        P * ((64 / 27) * (-(1 + (17 / 16) * Real.exp x * P))) ≤
          P * C * B := by
      have hchain :
          (64 / 27) * (-(1 + (17 / 16) * Real.exp x * P)) ≤ C * B :=
        le_trans hCL hCB
      have hP0' : 0 ≤ P := by simpa [P] using hP0
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hchain hP0'
    have hPfour : P ≤ 4 * P ^ 2 := by
      have hP0' : 0 ≤ P := by simpa [P] using hP0
      have hPquarter : 1 ≤ 4 * P := by
        have : 1 / 4 < P := by simpa [P] using hP
        linarith
      calc
        P = P * 1 := by ring
        _ ≤ P * (4 * P) := mul_le_mul_of_nonneg_left hPquarter hP0'
        _ = 4 * P ^ 2 := by ring
    have hscalar := negativeU_scalar_bracket_pos hx
    have hPpos : 0 < P := by
      have : 1 / 4 < P := by simpa [P] using hP
      linarith
    have hP2pos : 0 < P ^ 2 := sq_pos_of_pos hPpos
    have hscaled := mul_pos hP2pos hscalar
    have hscaleEq :
        P ^ 2 * (3 * Real.exp (2 * x) / (2 * x ^ 4) -
          (68 / 27) * Real.exp x - 256 / 27) =
        (3 / 2) * firstA m ω ^ 2 * Real.exp (2 * x) -
          (68 / 27) * Real.exp x * P ^ 2 - (256 / 27) * P ^ 2 := by
      dsimp [P]
      field_simp [hx0.ne']
    have hscaled' :
        0 < (3 / 2) * firstA m ω ^ 2 * Real.exp (2 * x) -
          (68 / 27) * Real.exp x * P ^ 2 - (256 / 27) * P ^ 2 := by
      rw [← hscaleEq]
      exact hscaled
    rw [show (2 * x : ℝ) = x + x by ring, Real.exp_add] at hscaled'
    have hrawEq :
        P * ((64 / 27) * (-(1 + (17 / 16) * Real.exp x * P))) =
          -(68 / 27) * Real.exp x * P ^ 2 - (64 / 27) * P := by ring
    rw [hrawEq] at hLower
    have hLower2 :
        -(68 / 27) * Real.exp x * P ^ 2 - (256 / 27) * P ^ 2 ≤
          P * C * B := by
      have hpScaled := mul_le_mul_of_nonneg_left hPfour
        (by norm_num : (0 : ℝ) ≤ 64 / 27)
      have hnegScaled : -(256 / 27) * P ^ 2 ≤ -(64 / 27) * P := by
        calc
          -(256 / 27) * P ^ 2 = -((64 / 27) * (4 * P ^ 2)) := by ring
          _ ≤ -((64 / 27) * P) := neg_le_neg hpScaled
          _ = -(64 / 27) * P := by ring
      calc
        -(68 / 27) * Real.exp x * P ^ 2 - (256 / 27) * P ^ 2 =
            (-(256 / 27) * P ^ 2) +
              (-(68 / 27) * Real.exp x * P ^ 2) := by ring
        _ ≤ (-(64 / 27) * P) +
            (-(68 / 27) * Real.exp x * P ^ 2) :=
          add_le_add hnegScaled (le_refl _)
        _ = -(68 / 27) * Real.exp x * P ^ 2 - (64 / 27) * P := by ring
        _ ≤ P * C * B := hLower
    have hHmain :
        (3 / 2) * firstA m ω ^ 2 * (Real.exp x * Real.exp x) ≤
          2 * firstH m ω x ^ 2 := by
      have htwice := mul_le_mul_of_nonneg_left hHsq (by norm_num : (0 : ℝ) ≤ 2)
      calc
        (3 / 2) * firstA m ω ^ 2 * (Real.exp x * Real.exp x) ≤
            2 * ((9 / 10) * firstA m ω * Real.exp x *
              ((9 / 10) * firstA m ω * Real.exp x)) := by
          calc
            (3 / 2) * firstA m ω ^ 2 * (Real.exp x * Real.exp x) ≤
                (3 / 2) * firstA m ω ^ 2 * (Real.exp x * Real.exp x) +
                  (3 / 25) * firstA m ω ^ 2 *
                    (Real.exp x * Real.exp x) := le_add_of_nonneg_right (by positivity)
            _ = 2 * ((9 / 10) * firstA m ω * Real.exp x *
                  ((9 / 10) * firstA m ω * Real.exp x)) := by ring
        _ ≤ 2 * (firstH m ω x * firstH m ω x) := htwice
        _ = 2 * firstH m ω x ^ 2 := by ring
    change 0 ≤ 2 * firstH m ω x ^ 2 + P * C * B
    linarith

end SSP.K3CyclicComplex
