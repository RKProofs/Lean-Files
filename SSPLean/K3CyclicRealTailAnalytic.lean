import SSPLean.K3CyclicRealTailSeries
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Analytic realization of the three-state real-spectrum tail series

This file connects the coefficient series to an actual twice-differentiable
Taylor function.  The Cauchy-product curvature identity is kept separate from
the convergence and differentiation arguments.
-/

set_option autoImplicit false

namespace SSP.K3CyclicRealTail

open scoped BigOperators

/-- The shifted complete-homogeneous Taylor summand. -/
noncomputable def completeTaylorTerm
    (u v : ℝ) (k n : ℕ) (t : ℝ) : ℝ :=
  u * v * complete3 u v n * t ^ (n + k) /
    (Nat.factorial (n + k) : ℝ)

/-- The original first-start remainder `w = h₁ - 1`. -/
noncomputable def firstStartRemainder (u v t : ℝ) : ℝ :=
  ∑' n, completeTaylorTerm u v 3 n t

noncomputable def firstStartRemainderDeriv (u v t : ℝ) : ℝ :=
  ∑' n, completeTaylorTerm u v 2 n t

noncomputable def firstStartRemainderDeriv2 (u v t : ℝ) : ℝ :=
  ∑' n, completeTaylorTerm u v 1 n t

theorem complete3_nonneg
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (n : ℕ) :
    0 ≤ complete3 u v n := (complete3_pos hu hv n).le

theorem complete3_le_sq
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (n : ℕ) :
    complete3 u v n ≤ (n + 1 : ℝ) ^ 2 := by
  unfold complete3
  calc
    ∑ m ∈ Finset.range (n + 1), diagonal u v m ≤
        ∑ _m ∈ Finset.range (n + 1), (n + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmn : m + 1 ≤ n + 1 := by
        have := Finset.mem_range.mp hm
        omega
      exact (diagonal_le_nat hu0 hu1 hv0 hv1 m).trans (by exact_mod_cast hmn)
    _ = (n + 1 : ℝ) ^ 2 := by simp [pow_two]; ring

/-- A derivative lowers the factorial shift by one. -/
theorem completeTaylorTerm_hasDerivAt
    (u v t : ℝ) (k n : ℕ) :
    HasDerivAt (completeTaylorTerm u v (k + 1) n)
      (completeTaylorTerm u v k n t) t := by
  have hpow := (hasDerivAt_pow (n + (k + 1)) t).const_mul
    (u * v * complete3 u v n / (Nat.factorial (n + (k + 1)) : ℝ))
  have hfun : completeTaylorTerm u v (k + 1) n = fun x =>
      (u * v * complete3 u v n /
        (Nat.factorial (n + (k + 1)) : ℝ)) * x ^ (n + (k + 1)) := by
    funext x
    unfold completeTaylorTerm
    ring
  have hderiv : completeTaylorTerm u v k n t =
      (u * v * complete3 u v n /
        (Nat.factorial (n + (k + 1)) : ℝ)) *
          ((n + (k + 1) : ℕ) : ℝ) * t ^ (n + (k + 1) - 1) := by
    unfold completeTaylorTerm
    rw [show n + (k + 1) = n + k + 1 by omega,
      show n + k + 1 - 1 = n + k by omega, Nat.factorial_succ]
    push_cast
    field_simp
  rw [hfun, hderiv]
  simpa only [mul_assoc] using hpow

/-- Absolute convergence of every positive factorial shift. -/
theorem completeTaylorTerm_summable
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun n => completeTaylorTerm u v k n t) := by
  let R : ℝ := max 1 |t|
  let x : ℝ := 4 * R
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := le_max_left _ _
  have hExp : Summable (fun n : ℕ => x ^ (n + k) /
      (Nat.factorial (n + k) : ℝ)) := by
    exact (summable_nat_add_iff k).2 (Real.summable_pow_div_factorial x)
  apply hExp.of_norm_bounded
  intro n
  have huv0 : 0 ≤ u * v := mul_nonneg hu0 hv0
  have huv1 : u * v ≤ 1 := mul_le_one₀ hu1 hv0 hv1
  have hnBase : (n + 1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self : n + 1 < 2 ^ (n + 1)).le
  have hnSq : (n + 1 : ℝ) ^ 2 ≤ (4 : ℝ) ^ (n + 1) := by
    calc
      (n + 1 : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (n + 1)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hnBase 2
      _ = (4 : ℝ) ^ (n + 1) := by
        rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        congr 1
        omega
  have hnShift : (4 : ℝ) ^ (n + 1) ≤ 4 ^ (n + k) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have htPow : |t| ^ (n + k) ≤ R ^ (n + k) :=
    pow_le_pow_left₀ (abs_nonneg t) (le_max_right _ _) _
  have hcomp0 : 0 ≤ complete3 u v n := complete3_nonneg hu0 hv0 n
  have hcomp : complete3 u v n ≤ (n + 1 : ℝ) ^ 2 :=
    complete3_le_sq hu0 hu1 hv0 hv1 n
  unfold completeTaylorTerm
  rw [norm_div, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg huv0, abs_of_nonneg (complete3_nonneg hu0 hv0 n),
    norm_pow, Real.norm_eq_abs, Real.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    u * v * complete3 u v n * |t| ^ (n + k) ≤
        1 * (n + 1 : ℝ) ^ 2 * |t| ^ (n + k) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul huv1 hcomp hcomp0 (by norm_num)) (pow_nonneg (abs_nonneg t) _)
    _ ≤ (4 : ℝ) ^ (n + k) * R ^ (n + k) := by
      exact mul_le_mul (by simpa using hnSq.trans hnShift) htPow
        (pow_nonneg (abs_nonneg t) _) (pow_nonneg (by norm_num) _)
    _ = x ^ (n + k) := by simp [x, mul_pow]

theorem completeTaylorTerm_nonneg
    {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 ≤ t)
    (k n : ℕ) :
    0 ≤ completeTaylorTerm u v k n t := by
  unfold completeTaylorTerm
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg hu hv) (complete3_nonneg hu hv n))
      (pow_nonneg ht _))
    (by positivity)

theorem firstStartRemainder_nonneg
    {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 ≤ t) :
    0 ≤ firstStartRemainder u v t := by
  unfold firstStartRemainder
  exact tsum_nonneg fun n => completeTaylorTerm_nonneg hu hv ht 3 n

theorem firstStartRemainderDeriv2_nonneg
    {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 ≤ t) :
    0 ≤ firstStartRemainderDeriv2 u v t := by
  unfold firstStartRemainderDeriv2
  exact tsum_nonneg fun n => completeTaylorTerm_nonneg hu hv ht 1 n

theorem completeTaylorTerm_norm_mono
    {u v x B : ℝ} (hB : 0 ≤ B) (hx : |x| ≤ B) (k n : ℕ) :
    ‖completeTaylorTerm u v k n x‖ ≤
      ‖completeTaylorTerm u v k n B‖ := by
  unfold completeTaylorTerm
  simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_of_nonneg hB]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg x) hx _)
      (mul_nonneg (mul_nonneg (abs_nonneg u) (abs_nonneg v))
        (abs_nonneg (complete3 u v n)))) (by positivity)

private theorem abs_le_center_add_one {t y : ℝ}
    (hy : y ∈ Set.Ioo (t - 1) (t + 1)) : |y| ≤ |t| + 1 := by
  have hdiff : |y - t| < 1 := by
    rw [abs_lt]
    constructor
    · linarith [hy.1]
    · linarith [hy.2]
  calc
    |y| = |t + (y - t)| := by rw [show t + (y - t) = y by ring]
    _ ≤ |t| + |y - t| := abs_add_le _ _
    _ ≤ |t| + 1 := by linarith

theorem firstStartRemainder_hasDerivAt
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    HasDerivAt (firstStartRemainder u v)
      (firstStartRemainderDeriv u v t) t := by
  let B : ℝ := |t| + 1
  let majorant : ℕ → ℝ := fun n =>
    ‖completeTaylorTerm u v 2 n B‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmajorant : Summable majorant := by
    exact (completeTaylorTerm_summable hu0 hu1 hv0 hv1 (t := B)
      (k := 2) (by omega)).norm
  have htmem : t ∈ Set.Ioo (t - 1) (t + 1) := by constructor <;> linarith
  unfold firstStartRemainder firstStartRemainderDeriv
  apply hasDerivAt_tsum_of_isPreconnected hmajorant isOpen_Ioo
    Set.ordConnected_Ioo.isPreconnected
  · intro n y hy
    exact completeTaylorTerm_hasDerivAt u v y 2 n
  · intro n y hy
    exact completeTaylorTerm_norm_mono hB
      (by simpa [B] using abs_le_center_add_one hy) 2 n
  · exact htmem
  · exact completeTaylorTerm_summable hu0 hu1 hv0 hv1 (k := 3) (by omega)
  · exact htmem

theorem firstStartRemainderDeriv_hasDerivAt
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    HasDerivAt (firstStartRemainderDeriv u v)
      (firstStartRemainderDeriv2 u v t) t := by
  let B : ℝ := |t| + 1
  let majorant : ℕ → ℝ := fun n =>
    ‖completeTaylorTerm u v 1 n B‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmajorant : Summable majorant := by
    exact (completeTaylorTerm_summable hu0 hu1 hv0 hv1 (t := B)
      (k := 1) (by omega)).norm
  have htmem : t ∈ Set.Ioo (t - 1) (t + 1) := by constructor <;> linarith
  unfold firstStartRemainderDeriv firstStartRemainderDeriv2
  apply hasDerivAt_tsum_of_isPreconnected hmajorant isOpen_Ioo
    Set.ordConnected_Ioo.isPreconnected
  · intro n y hy
    exact completeTaylorTerm_hasDerivAt u v y 1 n
  · intro n y hy
    exact completeTaylorTerm_norm_mono hB
      (by simpa [B] using abs_le_center_add_one hy) 1 n
  · exact htmem
  · exact completeTaylorTerm_summable hu0 hu1 hv0 hv1 (k := 2) (by omega)
  · exact htmem

theorem firstStartRemainder_deriv_eq
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    deriv (firstStartRemainder u v) t = firstStartRemainderDeriv u v t :=
  (firstStartRemainder_hasDerivAt hu0 hu1 hv0 hv1).deriv

theorem firstStartRemainderDeriv_deriv_eq
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    deriv (firstStartRemainderDeriv u v) t =
      firstStartRemainderDeriv2 u v t :=
  (firstStartRemainderDeriv_hasDerivAt hu0 hu1 hv0 hv1).deriv

theorem firstStartRemainder_second_deriv_eq
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    deriv (fun x => deriv (firstStartRemainder u v) x) t =
      firstStartRemainderDeriv2 u v t := by
  have hfun : (fun x => deriv (firstStartRemainder u v) x) =
      firstStartRemainderDeriv u v := by
    funext x
    exact firstStartRemainder_deriv_eq hu0 hu1 hv0 hv1
  rw [hfun]
  exact firstStartRemainderDeriv_deriv_eq hu0 hu1 hv0 hv1

/-- The dimension-three corrected curvature of the first-start remainder. -/
noncomputable def firstStartRemainderCurvature (u v t : ℝ) : ℝ :=
  t ^ 2 *
      (firstStartRemainder u v t *
          deriv (fun x => deriv (firstStartRemainder u v) x) t -
        deriv (firstStartRemainder u v) t ^ 2) +
    2 * firstStartRemainder u v t ^ 2

theorem firstStartRemainderCurvature_eq_shiftedSeries
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    firstStartRemainderCurvature u v t =
      t ^ 2 *
          (firstStartRemainder u v t * firstStartRemainderDeriv2 u v t -
            firstStartRemainderDeriv u v t ^ 2) +
        2 * firstStartRemainder u v t ^ 2 := by
  unfold firstStartRemainderCurvature
  rw [firstStartRemainder_deriv_eq hu0 hu1 hv0 hv1,
    firstStartRemainder_second_deriv_eq hu0 hu1 hv0 hv1]

/-- Cauchy convolution of two shifted Taylor series. -/
noncomputable def completeTaylorConvolution
    (u v : ℝ) (k l : ℕ) (t : ℝ) (M : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (M + 1),
    completeTaylorTerm u v k i t * completeTaylorTerm u v l (M - i) t

theorem completeTaylorConvolution_summable
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    Summable (completeTaylorConvolution u v k l t) := by
  have hfk := (completeTaylorTerm_summable hu0 hu1 hv0 hv1
    (t := t) (k := k) hk).norm
  have hfl := (completeTaylorTerm_summable hu0 hu1 hv0 hv1
    (t := t) (k := l) hl).norm
  exact (summable_norm_sum_mul_range_of_summable_norm hfk hfl).of_norm

theorem completeTaylor_tsum_mul_tsum
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    (∑' n, completeTaylorTerm u v k n t) *
        (∑' n, completeTaylorTerm u v l n t) =
      ∑' M, completeTaylorConvolution u v k l t M := by
  have hfk := (completeTaylorTerm_summable hu0 hu1 hv0 hv1
    (t := t) (k := k) hk).norm
  have hfl := (completeTaylorTerm_summable hu0 hu1 hv0 hv1
    (t := t) (k := l) hl).norm
  simpa only [completeTaylorConvolution] using
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfk hfl

/-- The symmetrized factorial kernel is exactly `splitKappa`. -/
theorem curvatureFactorialKernel_eq {M i : ℕ} (hi : i ≤ M) :
    ((1 / ((Nat.factorial (i + 3) : ℝ) *
          (Nat.factorial (M - i + 1) : ℝ)) +
        1 / ((Nat.factorial (i + 1) : ℝ) *
          (Nat.factorial (M - i + 3) : ℝ))) / 2 -
      1 / ((Nat.factorial (i + 2) : ℝ) *
        (Nat.factorial (M - i + 2) : ℝ)) +
      2 / ((Nat.factorial (i + 3) : ℝ) *
        (Nat.factorial (M - i + 3) : ℝ))) =
      (Nat.choose (M + 6) (i + 3) : ℝ) *
        splitKappa (M + 6) (i + 3) /
          (Nat.factorial (M + 6) : ℝ) := by
  have hp : i + 3 ≤ M + 6 := by omega
  have hsub : M + 6 - (i + 3) = M - i + 3 := by omega
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial hp
  rw [hsub] at hchooseNat
  have hchoose :
      (Nat.choose (M + 6) (i + 3) : ℝ) *
          (Nat.factorial (i + 3) : ℝ) *
            (Nat.factorial (M - i + 3) : ℝ) =
        (Nat.factorial (M + 6) : ℝ) := by
    exact_mod_cast hchooseNat
  have hchooseNe : (Nat.choose (M + 6) (i + 3) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hp).ne'
  rw [← hchoose]
  unfold splitKappa
  push_cast [Nat.cast_sub hi]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hchooseNe]
  rw [Nat.cast_sub hi]
  ring

theorem completeTaylorTerm_mul_complement
    (u v t : ℝ) {M i : ℕ} (hi : i ≤ M) (k l : ℕ) :
    completeTaylorTerm u v k i t *
        completeTaylorTerm u v l (M - i) t =
      (u * v) ^ 2 * complete3 u v i * complete3 u v (M - i) *
        t ^ (M + k + l) /
          ((Nat.factorial (i + k) : ℝ) *
            (Nat.factorial (M - i + l) : ℝ)) := by
  unfold completeTaylorTerm
  have hexp : i + k + (M - i + l) = M + k + l := by omega
  rw [← hexp, pow_add]
  ring

/-- One symmetrized Cauchy-product summand of the corrected curvature. -/
noncomputable def curvatureConvolutionTerm
    (u v t : ℝ) (M i : ℕ) : ℝ :=
  t ^ 2 *
      ((completeTaylorTerm u v 3 i t *
            completeTaylorTerm u v 1 (M - i) t +
          completeTaylorTerm u v 1 i t *
            completeTaylorTerm u v 3 (M - i) t) / 2 -
        completeTaylorTerm u v 2 i t *
          completeTaylorTerm u v 2 (M - i) t) +
    2 * (completeTaylorTerm u v 3 i t *
      completeTaylorTerm u v 3 (M - i) t)

noncomputable def curvatureConvolution (u v t : ℝ) (M : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (M + 1), curvatureConvolutionTerm u v t M i

theorem curvatureConvolutionTerm_eq
    (u v t : ℝ) {M i : ℕ} (hi : i ≤ M) :
    curvatureConvolutionTerm u v t M i =
      (u * v) ^ 2 *
        ((Nat.choose (M + 6) (i + 3) : ℝ) * complete3 u v i *
          complete3 u v (M - i) * splitKappa (M + 6) (i + 3) *
            t ^ (M + 6) / (Nat.factorial (M + 6) : ℝ)) := by
  unfold curvatureConvolutionTerm
  rw [completeTaylorTerm_mul_complement u v t hi 3 1,
    completeTaylorTerm_mul_complement u v t hi 1 3,
    completeTaylorTerm_mul_complement u v t hi 2 2,
    completeTaylorTerm_mul_complement u v t hi 3 3]
  rw [show M + 3 + 1 = M + 4 by omega, show M + 1 + 3 = M + 4 by omega,
    show M + 2 + 2 = M + 4 by omega, show M + 3 + 3 = M + 6 by omega]
  let A : ℝ := (u * v) ^ 2 * complete3 u v i * complete3 u v (M - i)
  let K : ℝ :=
    ((1 / ((Nat.factorial (i + 3) : ℝ) *
          (Nat.factorial (M - i + 1) : ℝ)) +
        1 / ((Nat.factorial (i + 1) : ℝ) *
          (Nat.factorial (M - i + 3) : ℝ))) / 2 -
      1 / ((Nat.factorial (i + 2) : ℝ) *
        (Nat.factorial (M - i + 2) : ℝ)) +
      2 / ((Nat.factorial (i + 3) : ℝ) *
        (Nat.factorial (M - i + 3) : ℝ)))
  have hrearrange :
      t ^ 2 *
          ((A * t ^ (M + 4) /
                ((Nat.factorial (i + 3) : ℝ) *
                  (Nat.factorial (M - i + 1) : ℝ)) +
              A * t ^ (M + 4) /
                ((Nat.factorial (i + 1) : ℝ) *
                  (Nat.factorial (M - i + 3) : ℝ))) / 2 -
            A * t ^ (M + 4) /
              ((Nat.factorial (i + 2) : ℝ) *
                (Nat.factorial (M - i + 2) : ℝ))) +
        2 * (A * t ^ (M + 6) /
          ((Nat.factorial (i + 3) : ℝ) *
            (Nat.factorial (M - i + 3) : ℝ))) =
        A * (t ^ 2 * t ^ (M + 4)) * K := by
    dsimp [K]
    ring
  change
    t ^ 2 *
          ((A * t ^ (M + 4) /
                ((Nat.factorial (i + 3) : ℝ) *
                  (Nat.factorial (M - i + 1) : ℝ)) +
              A * t ^ (M + 4) /
                ((Nat.factorial (i + 1) : ℝ) *
                  (Nat.factorial (M - i + 3) : ℝ))) / 2 -
            A * t ^ (M + 4) /
              ((Nat.factorial (i + 2) : ℝ) *
                (Nat.factorial (M - i + 2) : ℝ))) +
        2 * (A * t ^ (M + 6) /
          ((Nat.factorial (i + 3) : ℝ) *
            (Nat.factorial (M - i + 3) : ℝ))) = _
  rw [hrearrange]
  rw [show t ^ 2 * t ^ (M + 4) = t ^ (M + 6) by
    rw [← pow_add]
    congr 1
    omega]
  have hK := curvatureFactorialKernel_eq hi
  change _ = _ at hK
  rw [show K =
      (Nat.choose (M + 6) (i + 3) : ℝ) *
        splitKappa (M + 6) (i + 3) /
          (Nat.factorial (M + 6) : ℝ) by
    exact hK]
  dsimp [A]
  ring

theorem curvatureConvolution_eq_varianceSeriesTerm (u v t : ℝ) (M : ℕ) :
    curvatureConvolution u v t M =
      (u * v) ^ 2 * varianceSeriesTerm u v t M := by
  rw [curvatureConvolution, varianceSeriesTerm, varianceCoefficient_eq_complete3]
  let b : ℕ → ℝ := fun i =>
    (Nat.choose (M + 6) (i + 3) : ℝ) * complete3 u v i *
      complete3 u v (M - i) * splitKappa (M + 6) (i + 3)
  calc
    ∑ i ∈ Finset.range (M + 1), curvatureConvolutionTerm u v t M i =
        ∑ i ∈ Finset.range (M + 1),
          (u * v) ^ 2 * (b i * t ^ (M + 6) /
            (Nat.factorial (M + 6) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hiRange
      have hi : i ≤ M := by
        have := Finset.mem_range.mp hiRange
        omega
      rw [curvatureConvolutionTerm_eq u v t hi]
    _ = (u * v) ^ 2 *
        (∑ i ∈ Finset.range (M + 1),
          b i * t ^ (M + 6) / (Nat.factorial (M + 6) : ℝ)) := by
      rw [Finset.mul_sum]
    _ = (u * v) ^ 2 *
        ((∑ i ∈ Finset.range (M + 1), b i) * t ^ (M + 6) /
          (Nat.factorial (M + 6) : ℝ)) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = (u * v) ^ 2 *
        ((∑ i ∈ Finset.range (M + 1),
          (Nat.choose (M + 6) (i + 3) : ℝ) * complete3 u v i *
            complete3 u v (M - i) * splitKappa (M + 6) (i + 3)) *
          t ^ (M + 6) / (Nat.factorial (M + 6) : ℝ)) := by rfl

theorem curvatureConvolution_eq_linear (u v t : ℝ) (M : ℕ) :
    curvatureConvolution u v t M =
      (t ^ 2 / 2) * completeTaylorConvolution u v 3 1 t M +
      (t ^ 2 / 2) * completeTaylorConvolution u v 1 3 t M -
      t ^ 2 * completeTaylorConvolution u v 2 2 t M +
      2 * completeTaylorConvolution u v 3 3 t M := by
  let a : ℕ → ℝ := fun i =>
    completeTaylorTerm u v 3 i t * completeTaylorTerm u v 1 (M - i) t
  let b : ℕ → ℝ := fun i =>
    completeTaylorTerm u v 1 i t * completeTaylorTerm u v 3 (M - i) t
  let c : ℕ → ℝ := fun i =>
    completeTaylorTerm u v 2 i t * completeTaylorTerm u v 2 (M - i) t
  let d : ℕ → ℝ := fun i =>
    completeTaylorTerm u v 3 i t * completeTaylorTerm u v 3 (M - i) t
  unfold curvatureConvolution completeTaylorConvolution
  change (∑ i ∈ Finset.range (M + 1),
      (t ^ 2 * ((a i + b i) / 2 - c i) + 2 * d i)) = _
  have hlinear :
      (t ^ 2 / 2) * (∑ i ∈ Finset.range (M + 1), a i) +
          (t ^ 2 / 2) * (∑ i ∈ Finset.range (M + 1), b i) -
          t ^ 2 * (∑ i ∈ Finset.range (M + 1), c i) +
          2 * (∑ i ∈ Finset.range (M + 1), d i) =
        ∑ i ∈ Finset.range (M + 1),
          (t ^ 2 * ((a i + b i) / 2 - c i) + 2 * d i) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  exact hlinear.symm

/-- The differentiated first-start curvature is exactly the coefficient
series assembled in `K3CyclicRealTailSeries`. -/
theorem firstStartRemainderCurvature_eq_varianceCurvatureSeries
    {u v t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    firstStartRemainderCurvature u v t = varianceCurvatureSeries u v t := by
  let c31 := completeTaylorConvolution u v 3 1 t
  let c13 := completeTaylorConvolution u v 1 3 t
  let c22 := completeTaylorConvolution u v 2 2 t
  let c33 := completeTaylorConvolution u v 3 3 t
  have hs31 : Summable c31 :=
    completeTaylorConvolution_summable hu0 hu1 hv0 hv1 (by omega) (by omega)
  have hs13 : Summable c13 :=
    completeTaylorConvolution_summable hu0 hu1 hv0 hv1 (by omega) (by omega)
  have hs22 : Summable c22 :=
    completeTaylorConvolution_summable hu0 hu1 hv0 hv1 (by omega) (by omega)
  have hs33 : Summable c33 :=
    completeTaylorConvolution_summable hu0 hu1 hv0 hv1 (by omega) (by omega)
  let g : ℕ → ℝ := fun M =>
    (t ^ 2 / 2) * c31 M + (t ^ 2 / 2) * c13 M -
      t ^ 2 * c22 M + 2 * c33 M
  have hg : HasSum g
      ((t ^ 2 / 2) * (∑' M, c31 M) +
        (t ^ 2 / 2) * (∑' M, c13 M) -
        t ^ 2 * (∑' M, c22 M) +
        2 * (∑' M, c33 M)) := by
    simpa [g] using (((hs31.hasSum.mul_left (t ^ 2 / 2)).add
      (hs13.hasSum.mul_left (t ^ 2 / 2))).sub
        (hs22.hasSum.mul_left (t ^ 2))).add
          (hs33.hasSum.mul_left 2)
  have hcurvPoint : ∀ M, curvatureConvolution u v t M = g M := by
    intro M
    exact curvatureConvolution_eq_linear u v t M
  have hcurvTsum :
      (∑' M, curvatureConvolution u v t M) =
        ((t ^ 2 / 2) * (∑' M, c31 M) +
          (t ^ 2 / 2) * (∑' M, c13 M) -
          t ^ 2 * (∑' M, c22 M) +
          2 * (∑' M, c33 M)) := by
    rw [tsum_congr hcurvPoint]
    exact hg.tsum_eq
  have hsym : (∑' M, c31 M) = ∑' M, c13 M := by
    rw [← completeTaylor_tsum_mul_tsum hu0 hu1 hv0 hv1
          (k := 3) (l := 1) (by omega) (by omega),
      ← completeTaylor_tsum_mul_tsum hu0 hu1 hv0 hv1
          (k := 1) (l := 3) (by omega) (by omega)]
    ring
  calc
    firstStartRemainderCurvature u v t =
        t ^ 2 * (((∑' M, c31 M) + (∑' M, c13 M)) / 2 -
          (∑' M, c22 M)) + 2 * (∑' M, c33 M) := by
      rw [firstStartRemainderCurvature_eq_shiftedSeries hu0 hu1 hv0 hv1]
      unfold firstStartRemainder firstStartRemainderDeriv
        firstStartRemainderDeriv2
      simp only [pow_two]
      rw [completeTaylor_tsum_mul_tsum hu0 hu1 hv0 hv1
          (k := 3) (l := 1) (by omega) (by omega),
        completeTaylor_tsum_mul_tsum hu0 hu1 hv0 hv1
          (k := 2) (l := 2) (by omega) (by omega),
        completeTaylor_tsum_mul_tsum hu0 hu1 hv0 hv1
          (k := 3) (l := 3) (by omega) (by omega)]
      rw [hsym]
      ring
    _ = ((t ^ 2 / 2) * (∑' M, c31 M) +
          (t ^ 2 / 2) * (∑' M, c13 M) -
          t ^ 2 * (∑' M, c22 M) +
          2 * (∑' M, c33 M)) := by ring
    _ = ∑' M, curvatureConvolution u v t M := hcurvTsum.symm
    _ = ∑' M, (u * v) ^ 2 * varianceSeriesTerm u v t M := by
      apply tsum_congr
      exact curvatureConvolution_eq_varianceSeriesTerm u v t
    _ = varianceCurvatureSeries u v t := by
      unfold varianceCurvatureSeries
      rw [tsum_mul_left]

/-- On the admissible real-root chart, the first-start remainder has
nonnegative dimension-three corrected curvature for `t ≥ 10`. -/
theorem firstStartRemainderCurvature_nonneg_of_root
    {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) (ht : 10 ≤ t) :
    0 ≤ firstStartRemainderCurvature u v t := by
  have hsu : Real.sqrt u ≤ 1 := by
    nlinarith [Real.sqrt_nonneg v]
  have hsv : Real.sqrt v ≤ 1 := by
    nlinarith [Real.sqrt_nonneg u]
  have hu1 : u ≤ 1 := by
    nlinarith [Real.sq_sqrt hu, Real.sqrt_nonneg u]
  have hv1 : v ≤ 1 := by
    nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v]
  rw [firstStartRemainderCurvature_eq_varianceCurvatureSeries
    hu hu1 hv hv1]
  exact varianceCurvatureSeries_nonneg_of_root hu hv hroot ht

/-- Restoring the constant term `h₁ = 1 + w`, the original first-start
dimension-three corrected curvature is nonnegative on the real-root tail. -/
theorem firstStartCurvature_nonneg_of_root
    {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) (ht : 10 ≤ t) :
    0 ≤ t ^ 2 *
        ((1 + firstStartRemainder u v t) *
            deriv (fun x => deriv (firstStartRemainder u v) x) t -
          deriv (firstStartRemainder u v) t ^ 2) +
      2 * (1 + firstStartRemainder u v t) ^ 2 := by
  have ht0 : 0 ≤ t := by linarith
  have hsu : Real.sqrt u ≤ 1 := by
    nlinarith [Real.sqrt_nonneg v]
  have hsv : Real.sqrt v ≤ 1 := by
    nlinarith [Real.sqrt_nonneg u]
  have hu1 : u ≤ 1 := by
    nlinarith [Real.sq_sqrt hu, Real.sqrt_nonneg u]
  have hv1 : v ≤ 1 := by
    nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v]
  have hw := firstStartRemainder_nonneg hu hv ht0
  have hw2 := firstStartRemainderDeriv2_nonneg hu hv ht0
  have htw2 : 0 ≤ t ^ 2 * firstStartRemainderDeriv2 u v t :=
    mul_nonneg (sq_nonneg t) hw2
  have hcurv := firstStartRemainderCurvature_nonneg_of_root hu hv hroot ht
  rw [firstStartRemainderCurvature_eq_shiftedSeries hu hu1 hv hv1] at hcurv
  rw [firstStartRemainder_deriv_eq hu hu1 hv hv1,
    firstStartRemainder_second_deriv_eq hu hu1 hv hv1]
  nlinarith

end SSP.K3CyclicRealTail
