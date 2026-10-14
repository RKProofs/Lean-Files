import SSPLean.K3CyclicRealTailLowComplete

/-!
# Analytic assembly of the three-state real-spectrum tail

This file joins the exact finite certificate for `M = 0, ..., 10` to the
termwise-positive tail.  Summability is kept as an explicit hypothesis at
first, so the order-theoretic assembly is independent of later analytic
bounds.
-/

set_option autoImplicit false

namespace SSP.K3CyclicRealTail

open scoped BigOperators

/-- A nonnegative finite prefix and a termwise nonnegative shifted tail have
nonnegative total sum. -/
theorem tsum_nonneg_of_prefix_tail_nonneg
    {f : ℕ → ℝ} (hf : Summable f) (k : ℕ)
    (hprefix : 0 ≤ ∑ i ∈ Finset.range k, f i)
    (htail : ∀ n, 0 ≤ f (n + k)) :
    0 ≤ ∑' n, f n := by
  rw [← hf.sum_add_tsum_nat_add k]
  exact add_nonneg hprefix (tsum_nonneg htail)

/-- The summand whose index `M` corresponds to Taylor degree `M + 6`. -/
noncomputable def varianceSeriesTerm (u v t : ℝ) (M : ℕ) : ℝ :=
  varianceCoefficient u v M * t ^ (M + 6) /
    (Nat.factorial (M + 6) : ℝ)

/-- Cancellation of the two normalizing denominators in the coefficient.
This is the form that appears directly in the Cauchy product of the original
complete-homogeneous Taylor series. -/
theorem varianceCoefficient_eq_complete3 (u v : ℝ) (M : ℕ) :
    varianceCoefficient u v M =
      ∑ i ∈ Finset.range (M + 1),
        (Nat.choose (M + 6) (i + 3) : ℝ) * complete3 u v i *
          complete3 u v (M - i) * splitKappa (M + 6) (i + 3) := by
  unfold varianceCoefficient splitWeight symmetricProduct normalizedComplete
  apply Finset.sum_congr rfl
  intro i hi
  have hiM : i ≤ M := by
    have := Finset.mem_range.mp hi
    omega
  push_cast
  field_simp

theorem complete3_comm (u v : ℝ) (n : ℕ) :
    complete3 u v n = complete3 v u n := by
  unfold complete3
  apply Finset.sum_congr rfl
  intro m hm
  exact diagonal_comm u v m

theorem normalizedComplete_comm (u v : ℝ) (n : ℕ) :
    normalizedComplete u v n = normalizedComplete v u n := by
  unfold normalizedComplete
  rw [complete3_comm]

theorem varianceCoefficient_comm (u v : ℝ) (M : ℕ) :
    varianceCoefficient u v M = varianceCoefficient v u M := by
  unfold varianceCoefficient symmetricProduct
  apply Finset.sum_congr rfl
  intro i hi
  rw [normalizedComplete_comm u v i, normalizedComplete_comm u v (M - i)]

theorem varianceSeriesTerm_comm (u v t : ℝ) (M : ℕ) :
    varianceSeriesTerm u v t M = varianceSeriesTerm v u t M := by
  unfold varianceSeriesTerm
  rw [varianceCoefficient_comm]

theorem diagonal_le_nat
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (n : ℕ) :
    diagonal u v n ≤ (n + 1 : ℝ) := by
  unfold diagonal
  calc
    ∑ i ∈ Finset.range (n + 1), u ^ i * v ^ (n - i) ≤
        ∑ _i ∈ Finset.range (n + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_one₀ (pow_le_one₀ hu0 hu1) (pow_nonneg hv0 _)
        (pow_le_one₀ hv0 hv1)
    _ = (n + 1 : ℝ) := by simp

theorem normalizedComplete_le_sq
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (n : ℕ) :
    normalizedComplete u v n ≤ (n + 1 : ℝ) ^ 2 := by
  have hdiag : ∀ m ∈ Finset.range (n + 1),
      diagonal u v m ≤ (n + 1 : ℝ) := by
    intro m hm
    have hmn : m + 1 ≤ n + 1 := by
      have := Finset.mem_range.mp hm
      omega
    exact (diagonal_le_nat hu0 hu1 hv0 hv1 m).trans (by exact_mod_cast hmn)
  have hcomplete : complete3 u v n ≤ (n + 1 : ℝ) ^ 2 := by
    unfold complete3
    calc
      ∑ m ∈ Finset.range (n + 1), diagonal u v m ≤
          ∑ _m ∈ Finset.range (n + 1), (n + 1 : ℝ) :=
        Finset.sum_le_sum hdiag
      _ = (n + 1 : ℝ) ^ 2 := by simp [pow_two]; ring
  unfold normalizedComplete
  have hn : (1 : ℝ) ≤ n + 1 := by norm_num
  calc
    complete3 u v n / (n + 1 : ℝ) ≤ complete3 u v n := by
      exact div_le_self (complete3_pos hu0 hv0 n).le hn
    _ ≤ (n + 1 : ℝ) ^ 2 := hcomplete

theorem splitKappa_abs_le_sq {M i : ℕ} (hi : i ≤ M) :
    |splitKappa (M + 6) (i + 3)| ≤ (M + 8 : ℝ) ^ 2 := by
  have hlower : -(M + 6 : ℝ) ≤
      (M + 6 : ℝ) - 2 * (i + 3 : ℝ) := by
    exact_mod_cast (show -(M + 6 : ℤ) ≤
      (M + 6 : ℤ) - 2 * (i + 3 : ℤ) by omega)
  have hupper : (M + 6 : ℝ) - 2 * (i + 3 : ℝ) ≤
      (M + 6 : ℝ) := by
    have : 0 ≤ (i + 3 : ℝ) := by positivity
    linarith
  have hsq : ((M + 6 : ℝ) - 2 * (i + 3 : ℝ)) ^ 2 ≤
      (M + 6 : ℝ) ^ 2 := by
    have hprod : 0 ≤
        ((M + 6 : ℝ) - ((M + 6 : ℝ) - 2 * (i + 3 : ℝ))) *
          ((M + 6 : ℝ) + ((M + 6 : ℝ) - 2 * (i + 3 : ℝ))) :=
      mul_nonneg (sub_nonneg.mpr hupper) (by linarith)
    nlinarith
  apply abs_le.mpr
  unfold splitKappa
  push_cast
  constructor <;> nlinarith [sq_nonneg (M + 8 : ℝ)]

theorem symmetricProduct_abs_le_fourth
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    {M i : ℕ} (hi : i ≤ M) :
    |symmetricProduct (normalizedComplete u v) M i| ≤
      (M + 8 : ℝ) ^ 4 := by
  have hi' : (i + 1 : ℝ) ≤ M + 8 := by exact_mod_cast (by omega : i + 1 ≤ M + 8)
  have hsub' : (M - i + 1 : ℝ) ≤ M + 8 := by
    exact_mod_cast (by omega : M - i + 1 ≤ M + 8)
  have hqi0 := (normalizedComplete_pos hu0 hv0 i).le
  have hqj0 := (normalizedComplete_pos hu0 hv0 (M - i)).le
  have hqi : normalizedComplete u v i ≤ (M + 8 : ℝ) ^ 2 :=
    (normalizedComplete_le_sq hu0 hu1 hv0 hv1 i).trans (by nlinarith)
  have hqj : normalizedComplete u v (M - i) ≤ (M + 8 : ℝ) ^ 2 :=
    (normalizedComplete_le_sq hu0 hu1 hv0 hv1 (M - i)).trans (by
      rw [Nat.cast_sub hi]
      have hA : 0 ≤ (M : ℝ) - i + 1 := by
        have : (i : ℝ) ≤ M := by exact_mod_cast hi
        linarith
      have hp := mul_le_mul hsub' hsub' hA (by positivity : (0 : ℝ) ≤ M + 8)
      nlinarith)
  unfold symmetricProduct
  rw [abs_of_nonneg (mul_nonneg hqi0 hqj0)]
  calc
    normalizedComplete u v i * normalizedComplete u v (M - i) ≤
        (M + 8 : ℝ) ^ 2 * (M + 8 : ℝ) ^ 2 :=
      mul_le_mul hqi hqj hqj0 (sq_nonneg _)
    _ = (M + 8 : ℝ) ^ 4 := by ring

theorem splitWeight_le
    {M i : ℕ} (hi : i ≤ M) :
    splitWeight M i ≤ (2 : ℝ) ^ (M + 6) * (M + 8 : ℝ) ^ 2 := by
  have hchoose := Nat.choose_le_two_pow (M + 6) (i + 3)
  have hi' : i + 1 ≤ M + 8 := by omega
  have hsub' : M - i + 1 ≤ M + 8 := by omega
  have hnat : Nat.choose (M + 6) (i + 3) * (i + 1) * (M - i + 1) ≤
      2 ^ (M + 6) * (M + 8) ^ 2 := by
    calc
      Nat.choose (M + 6) (i + 3) * (i + 1) * (M - i + 1) ≤
          2 ^ (M + 6) * (M + 8) * (M + 8) := by gcongr
      _ = 2 ^ (M + 6) * (M + 8) ^ 2 := by ring
  unfold splitWeight
  exact_mod_cast hnat

theorem varianceCoefficient_abs_le
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (M : ℕ) :
    |varianceCoefficient u v M| ≤
      (2 : ℝ) ^ (M + 6) * (M + 8 : ℝ) ^ 9 := by
  unfold varianceCoefficient
  rw [← Real.norm_eq_abs]
  calc
    ‖∑ i ∈ Finset.range (M + 1), splitWeight M i *
        symmetricProduct (normalizedComplete u v) M i *
          splitKappa (M + 6) (i + 3)‖ ≤
        ∑ i ∈ Finset.range (M + 1),
          ‖splitWeight M i * symmetricProduct (normalizedComplete u v) M i *
            splitKappa (M + 6) (i + 3)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (M + 1),
        (2 : ℝ) ^ (M + 6) * (M + 8 : ℝ) ^ 8 := by
      apply Finset.sum_le_sum
      intro i hiRange
      have hi : i ≤ M := by
        have := Finset.mem_range.mp hiRange
        omega
      rw [norm_mul, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (splitWeight_nonneg M i)]
      calc
        splitWeight M i *
              |symmetricProduct (normalizedComplete u v) M i| *
            |splitKappa (M + 6) (i + 3)| ≤
            ((2 : ℝ) ^ (M + 6) * (M + 8 : ℝ) ^ 2) *
              (M + 8 : ℝ) ^ 4 * (M + 8 : ℝ) ^ 2 := by
          gcongr
          · exact splitWeight_le hi
          · exact symmetricProduct_abs_le_fourth hu0 hu1 hv0 hv1 hi
          · exact splitKappa_abs_le_sq hi
        _ = (2 : ℝ) ^ (M + 6) * (M + 8 : ℝ) ^ 8 := by ring
    _ ≤ (2 : ℝ) ^ (M + 6) * (M + 8 : ℝ) ^ 9 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hM : ((M + 1 : ℕ) : ℝ) ≤ M + 8 := by norm_num
      calc
        ((M + 1 : ℕ) : ℝ) *
              ((2 : ℝ) ^ (M + 6) * (M + 8 : ℝ) ^ 8) ≤
            (M + 8 : ℝ) *
              ((2 : ℝ) ^ (M + 6) * (M + 8 : ℝ) ^ 8) :=
          mul_le_mul_of_nonneg_right hM (by positivity)
        _ = (2 : ℝ) ^ (M + 6) * (M + 8 : ℝ) ^ 9 := by ring

/-- A deliberately coarse exponential majorant.  Its only purpose is to
make convergence immediate from the exponential series. -/
theorem varianceSeriesTerm_norm_le_majorant
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (M : ℕ) :
    ‖varianceSeriesTerm u v t M‖ ≤
      (1024 * max 1 |t|) ^ (M + 8) / (Nat.factorial M : ℝ) := by
  have hbaseNat : M + 8 ≤ 2 ^ (M + 8) :=
    (Nat.lt_two_pow_self : M + 8 < 2 ^ (M + 8)).le
  have hbase : (M + 8 : ℝ) ≤ (2 : ℝ) ^ (M + 8) := by
    exact_mod_cast hbaseNat
  have htwo : (2 : ℝ) ^ (M + 6) ≤ 2 ^ (M + 8) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hpoly : (M + 8 : ℝ) ^ 9 ≤
      ((2 : ℝ) ^ (M + 8)) ^ 9 :=
    pow_le_pow_left₀ (by positivity) hbase 9
  have htbase : |t| ≤ max 1 |t| := le_max_right _ _
  have htpow : |t| ^ (M + 6) ≤ (max 1 |t|) ^ (M + 8) := by
    exact (pow_le_pow_left₀ (abs_nonneg t) htbase (M + 6)).trans
      (pow_le_pow_right₀ (le_max_left _ _) (by omega))
  have hpowIdentity :
      (2 : ℝ) ^ (M + 8) * ((2 : ℝ) ^ (M + 8)) ^ 9 *
          (max 1 |t|) ^ (M + 8) =
        (1024 * max 1 |t|) ^ (M + 8) := by
    have htwoIdentity :
        (2 : ℝ) ^ (M + 8) * ((2 : ℝ) ^ (M + 8)) ^ 9 =
          (1024 : ℝ) ^ (M + 8) := by
      rw [← pow_succ']
      rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [htwoIdentity, ← mul_pow]
  have hnumer :
      |varianceCoefficient u v M| * |t| ^ (M + 6) ≤
        (1024 * max 1 |t|) ^ (M + 8) := by
    calc
      |varianceCoefficient u v M| * |t| ^ (M + 6) ≤
          ((2 : ℝ) ^ (M + 6) * (M + 8 : ℝ) ^ 9) *
            |t| ^ (M + 6) :=
        mul_le_mul_of_nonneg_right
          (varianceCoefficient_abs_le hu0 hu1 hv0 hv1 M) (pow_nonneg (abs_nonneg t) _)
      _ ≤ (2 : ℝ) ^ (M + 8) * ((2 : ℝ) ^ (M + 8)) ^ 9 *
          (max 1 |t|) ^ (M + 8) := by gcongr
      _ = (1024 * max 1 |t|) ^ (M + 8) := hpowIdentity
  have hfactNat : Nat.factorial M ≤ Nat.factorial (M + 6) := by
    gcongr
    omega
  have hfact : (Nat.factorial M : ℝ) ≤ Nat.factorial (M + 6) := by
    exact_mod_cast hfactNat
  unfold varianceSeriesTerm
  rw [norm_div, norm_mul, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs,
    Real.norm_natCast]
  exact (div_le_div_of_nonneg_right hnumer (by positivity)).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hfact)

theorem varianceSeriesTerm_summable
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Summable (varianceSeriesTerm u v t) := by
  let x : ℝ := 1024 * max 1 |t|
  have hexp : Summable (fun M : ℕ => x ^ M / (Nat.factorial M : ℝ)) :=
    Real.summable_pow_div_factorial x
  have hmajorant : Summable (fun M : ℕ => x ^ (M + 8) /
      (Nat.factorial M : ℝ)) := by
    refine (hexp.mul_left (x ^ 8)).congr (fun M => ?_)
    rw [pow_add]
    ring
  apply hmajorant.of_norm_bounded
  intro M
  simpa [x] using varianceSeriesTerm_norm_le_majorant hu0 hu1 hv0 hv1 M

/-- The real-root chart satisfies all hypotheses of the far-tail coefficient
theorem. -/
theorem realRootChart_admissible
    {s d : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    0 ≤ realRootChartU s d ∧
      realRootChartU s d ≤ realRootChartV s d ∧
      realRootChartV s d ≤ 1 ∧
      Real.sqrt (realRootChartU s d) +
        Real.sqrt (realRootChartV s d) ≤ 1 := by
  have hu : 0 ≤ realRootChartU s d := realRootChartU_nonneg s d
  have hv : 0 ≤ realRootChartV s d := realRootChartV_nonneg s d
  have huv : realRootChartU s d ≤ realRootChartV s d := by
    unfold realRootChartU realRootChartV
    nlinarith [mul_nonneg (sq_nonneg s) hd0]
  have hs_sq : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
  have hd_sq : (1 + d) ^ 2 ≤ 4 := by nlinarith [sq_nonneg (1 + d)]
  have hv1 : realRootChartV s d ≤ 1 := by
    unfold realRootChartV
    calc
      s ^ 2 * (1 + d) ^ 2 / 4 ≤ 1 * (1 + d) ^ 2 / 4 := by
        gcongr
      _ ≤ 1 := by nlinarith
  have hminus : 0 ≤ s * (1 - d) / 2 := by positivity
  have hplus : 0 ≤ s * (1 + d) / 2 := by positivity
  have hsqrtU :
      Real.sqrt (realRootChartU s d) = s * (1 - d) / 2 := by
    rw [show realRootChartU s d = (s * (1 - d) / 2) ^ 2 by
      unfold realRootChartU
      ring]
    exact Real.sqrt_sq hminus
  have hsqrtV :
      Real.sqrt (realRootChartV s d) = s * (1 + d) / 2 := by
    rw [show realRootChartV s d = (s * (1 + d) / 2) ^ 2 by
      unfold realRootChartV
      ring]
    exact Real.sqrt_sq hplus
  refine ⟨hu, huv, hv1, ?_⟩
  rw [hsqrtU, hsqrtV]
  nlinarith

/-- Conversely, every ordered admissible pair occurs in the compact
real-root chart. -/
theorem exists_realRootChart
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) :
    ∃ s d : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ d ∧ d ≤ 1 ∧
      realRootChartU s d = u ∧ realRootChartV s d = v := by
  have hv : 0 ≤ v := hu.trans huv
  let a := Real.sqrt u
  let b := Real.sqrt v
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hab : a ≤ b := by
    dsimp [a, b]
    exact Real.sqrt_le_sqrt huv
  by_cases hs0 : a + b = 0
  · have ha0 : a = 0 := by nlinarith
    have hb0 : b = 0 := by nlinarith
    have hu0 : u = 0 := by
      have := Real.sq_sqrt hu
      change a ^ 2 = u at this
      rw [ha0] at this
      norm_num at this
      exact this.symm
    have hv0 : v = 0 := by
      have := Real.sq_sqrt hv
      change b ^ 2 = v at this
      rw [hb0] at this
      norm_num at this
      exact this.symm
    refine ⟨0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · simp [realRootChartU, hu0]
    · simp [realRootChartV, hv0]
  · let s := a + b
    let d := (b - a) / s
    have hs : 0 < s := by
      dsimp [s]
      exact lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs0)
    have hs1 : s ≤ 1 := by simpa [s, a, b] using hroot
    have hd0 : 0 ≤ d := by dsimp [d]; positivity
    have hd1 : d ≤ 1 := by
      dsimp [d]
      apply (div_le_one hs).2
      dsimp [s]
      linarith
    have hU : realRootChartU s d = u := by
      have h1d : 1 - d = 2 * a / s := by
        dsimp [d, s]
        field_simp [hs.ne']
        ring
      rw [realRootChartU, h1d]
      have hau : a ^ 2 = u := by exact Real.sq_sqrt hu
      field_simp [hs.ne']
      nlinarith
    have hV : realRootChartV s d = v := by
      have h1d : 1 + d = 2 * b / s := by
        dsimp [d, s]
        field_simp [hs.ne']
        ring
      rw [realRootChartV, h1d]
      have hbv : b ^ 2 = v := by exact Real.sq_sqrt hv
      field_simp [hs.ne']
      nlinarith
    exact ⟨s, d, hs.le, hs1, hd0, hd1, hU, hV⟩

/-- Multiplying the low-block normalization by `t^16` recovers exactly the
first eleven Taylor terms. -/
theorem varianceSeries_prefix_eq
    (u v t : ℝ) (ht : t ≠ 0) :
    ∑ M ∈ Finset.range 11, varianceSeriesTerm u v t M =
      t ^ 16 * varianceLowBlock u v (10 / t) := by
  rw [varianceLowBlock, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M hM
  have hMlt : M < 11 := Finset.mem_range.mp hM
  have hMle : M ≤ 10 := by omega
  have hadd : M + 6 + (10 - M) = 16 := by omega
  unfold varianceSeriesTerm
  rw [div_pow]
  rw [show t ^ 16 = t ^ (M + 6) * t ^ (10 - M) by
    rw [← pow_add, hadd]]
  field_simp [pow_ne_zero _ ht]

/-- Every term after the certified eleven-term block is nonnegative. -/
theorem varianceSeriesTerm_tail_nonneg
    {s d t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ varianceSeriesTerm (realRootChartU s d) (realRootChartV s d)
      t (n + 11) := by
  rcases realRootChart_admissible hs0 hs1 hd0 hd1 with
    ⟨hu, huv, hv1, hroot⟩
  unfold varianceSeriesTerm
  apply div_nonneg
  · exact mul_nonneg
      (normalizedComplete_splitCoefficient_nonneg_of_baseline_formula
        hu huv hv1 hroot (by omega))
      (pow_nonneg ht _)
  · positivity

/-- Analytic assembly of the finite certificate and coefficientwise-positive
tail.  The remaining hypothesis is only convergence of the displayed Taylor
series. -/
theorem varianceSeries_tsum_nonneg_of_summable
    {s d t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (ht : 10 ≤ t)
    (hsum : Summable
      (varianceSeriesTerm (realRootChartU s d) (realRootChartV s d) t)) :
    0 ≤ ∑' M, varianceSeriesTerm
      (realRootChartU s d) (realRootChartV s d) t M := by
  apply tsum_nonneg_of_prefix_tail_nonneg hsum 11
  · rw [varianceSeries_prefix_eq _ _ _ (by linarith)]
    exact mul_nonneg (pow_nonneg (by linarith) 16)
      (varianceLowBlock_nonneg_of_t_ge_ten hs0 hs1 hd0 hd1 ht)
  · exact varianceSeriesTerm_tail_nonneg hs0 hs1 hd0 hd1 (by linarith)

/-- Completed analytic real-spectrum tail: the finite certificate, the
coefficientwise far tail, and absolute convergence are all discharged. -/
theorem varianceSeries_tsum_nonneg
    {s d t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (ht : 10 ≤ t) :
    0 ≤ ∑' M, varianceSeriesTerm
      (realRootChartU s d) (realRootChartV s d) t M := by
  rcases realRootChart_admissible hs0 hs1 hd0 hd1 with
    ⟨hu, huv, hv1, _hroot⟩
  exact varianceSeries_tsum_nonneg_of_summable hs0 hs1 hd0 hd1 ht
    (varianceSeriesTerm_summable hu (huv.trans hv1)
      (realRootChartV_nonneg s d) hv1)

/-- Coordinate-free form of the completed real-spectrum Taylor tail. -/
theorem varianceSeries_tsum_nonneg_of_admissible
    {u v t : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) (ht : 10 ≤ t) :
    0 ≤ ∑' M, varianceSeriesTerm u v t M := by
  obtain ⟨s, d, hs0, hs1, hd0, hd1, hU, hV⟩ :=
    exists_realRootChart hu huv hroot
  rw [← hU, ← hV]
  exact varianceSeries_tsum_nonneg hs0 hs1 hd0 hd1 ht

/-- Symmetric coordinate-free form: ordering the two real roots is no longer
part of the statement. -/
theorem varianceSeries_tsum_nonneg_of_root
    {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) (ht : 10 ≤ t) :
    0 ≤ ∑' M, varianceSeriesTerm u v t M := by
  rcases le_total u v with huv | hvu
  · exact varianceSeries_tsum_nonneg_of_admissible hu huv hroot ht
  · rw [tsum_congr (fun M => varianceSeriesTerm_comm u v t M)]
    apply varianceSeries_tsum_nonneg_of_admissible hv hvu
    · simpa [add_comm] using hroot
    · exact ht

/-- The curvature series after restoring the common nonnegative `(uv)^2`
factor removed in `varianceCoefficient`. -/
noncomputable def varianceCurvatureSeries (u v t : ℝ) : ℝ :=
  (u * v) ^ 2 * ∑' M, varianceSeriesTerm u v t M

theorem varianceCurvatureSeries_nonneg_of_root
    {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) (ht : 10 ≤ t) :
    0 ≤ varianceCurvatureSeries u v t := by
  unfold varianceCurvatureSeries
  exact mul_nonneg (sq_nonneg _) (varianceSeries_tsum_nonneg_of_root hu hv hroot ht)

end SSP.K3CyclicRealTail
