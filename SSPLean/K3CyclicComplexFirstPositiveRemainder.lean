import SSPLean.K3CyclicComplexFirstPositiveCurvatureSeries
import SSPLean.K3CyclicComplexFirstPositiveCertificateBridge

/-! # Uniform degree-70 remainder bound for the positive complex-first chart -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.PositiveCoeff

open scoped BigOperators

theorem abs_kernel_le
    {N j : ℕ} (hj : j ≤ N) :
    |(ComplexCoeff.kernel N j : ℝ)| ≤
      (Nat.choose N j : ℝ) * (N + 2 : ℝ) ^ 2 := by
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hprod : 0 ≤ (j : ℝ) * ((N : ℝ) - j) := mul_nonneg hj0 (by linarith)
  have hsq : ((N : ℝ) - 2 * j) ^ 2 ≤ (N : ℝ) ^ 2 := by
    nlinarith
  have hinside :
      |(4 : ℝ) - N + ((N : ℝ) - 2 * j) ^ 2| / 2 ≤ (N + 2 : ℝ) ^ 2 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ((N : ℝ) + 2)]
  unfold ComplexCoeff.kernel
  push_cast
  rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Nat.choose N j)]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_right hinside
      (show (0 : ℝ) ≤ Nat.choose N j by positivity)

theorem abs_scalarCurvatureCoefficient_le
    {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (N : ℕ) :
    |SSP.K3CyclicComplex.scalarCurvatureCoefficient
        (scalarDerivative r τ) N| ≤
      4 * (N + 2 : ℝ) ^ 2 * 2 ^ N := by
  unfold SSP.K3CyclicComplex.scalarCurvatureCoefficient
  calc
    |∑ j ∈ Finset.range (N + 1),
        (ComplexCoeff.kernel N j : ℝ) * scalarDerivative r τ j *
          scalarDerivative r τ (N - j)| ≤
      ∑ j ∈ Finset.range (N + 1),
        |(ComplexCoeff.kernel N j : ℝ) * scalarDerivative r τ j *
          scalarDerivative r τ (N - j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (N + 1),
        (Nat.choose N j : ℝ) * (N + 2 : ℝ) ^ 2 * 4 := by
      apply Finset.sum_le_sum
      intro j hjmem
      have hj : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hjmem)
      rw [abs_mul, abs_mul]
      have hk := abs_kernel_le hj
      have hdj := abs_scalarDerivative_le_two hr0 hr1 hτ0 hτ1 j
      have hdsub := abs_scalarDerivative_le_two hr0 hr1 hτ0 hτ1 (N - j)
      nlinarith [mul_le_mul hk
        (mul_le_mul hdj hdsub (abs_nonneg _) (by norm_num))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg (by positivity) (by positivity))]
    _ = (∑ j ∈ Finset.range (N + 1), (Nat.choose N j : ℝ)) *
        ((N + 2 : ℝ) ^ 2 * 4) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = 4 * (N + 2 : ℝ) ^ 2 * 2 ^ N := by
      have hsum : (∑ j ∈ Finset.range (N + 1), (Nat.choose N j : ℝ)) =
          (2 ^ N : ℕ) := by exact_mod_cast Nat.sum_range_choose N
      rw [hsum]
      push_cast
      ring

noncomputable def remainderMajorant (N : ℕ) : ℝ :=
  4 * (N + 2 : ℝ) ^ 2 * 20 ^ N / (Nat.factorial N : ℝ)

theorem norm_curvatureSeriesTerm_le_majorant
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hx : |x| ≤ 10) (N : ℕ) :
    ‖curvatureSeriesTerm r τ x N‖ ≤ remainderMajorant N := by
  unfold curvatureSeriesTerm remainderMajorant
  simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : 0 ≤ (Nat.factorial N : ℝ))]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hc := abs_scalarCurvatureCoefficient_le hr0 hr1 hτ0 hτ1 N
  have hxpow : |x| ^ N ≤ (10 : ℝ) ^ N :=
    pow_le_pow_left₀ (abs_nonneg x) hx N
  calc
    |SSP.K3CyclicComplex.scalarCurvatureCoefficient
        (scalarDerivative r τ) N| * |x| ^ N ≤
      (4 * (N + 2 : ℝ) ^ 2 * 2 ^ N) * 10 ^ N :=
        mul_le_mul hc hxpow (pow_nonneg (abs_nonneg x) _)
          (by positivity)
    _ = 4 * (N + 2 : ℝ) ^ 2 * 20 ^ N := by
      rw [show (20 : ℝ) = 2 * 10 by norm_num, mul_pow]
      ring

theorem remainderMajorant_nonneg (N : ℕ) : 0 ≤ remainderMajorant N := by
  unfold remainderMajorant
  positivity

theorem remainderMajorant_ratio {N : ℕ} (hN : 71 ≤ N) :
    remainderMajorant (N + 1) ≤ (1 / 2 : ℝ) * remainderMajorant N := by
  unfold remainderMajorant
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have hfac : (0 : ℝ) < Nat.factorial N := by positivity
  let y : ℝ := (N : ℝ) - 71
  have hNR : (71 : ℝ) ≤ N := by exact_mod_cast hN
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hpoly : 0 ≤ y ^ 3 + 178 * y ^ 2 + 9921 * y + 164648 := by
    positivity
  have hcoef : 40 * ((N : ℝ) + 3) ^ 2 ≤
      ((N : ℝ) + 1) * ((N : ℝ) + 2) ^ 2 := by
    dsimp [y] at hpoly
    nlinarith
  field_simp
  have hpow : (0 : ℝ) < 20 ^ N := pow_pos (by norm_num) _
  have hscaled := mul_le_mul_of_nonneg_right hcoef hpow.le
  norm_num [pow_succ] at hscaled ⊢
  nlinarith

theorem remainderMajorant_seventy_one_lt_half :
    remainderMajorant 71 < (1 / 2 : ℝ) := by
  norm_num [remainderMajorant, Nat.factorial]

theorem remainderMajorant_shift_le_geometric (k : ℕ) :
    remainderMajorant (71 + k) ≤
      remainderMajorant 71 * (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        remainderMajorant (71 + (k + 1)) =
            remainderMajorant ((71 + k) + 1) := by congr 1
        _ ≤ (1 / 2 : ℝ) * remainderMajorant (71 + k) :=
          remainderMajorant_ratio (by omega)
        _ ≤ (1 / 2 : ℝ) *
            (remainderMajorant 71 * (1 / 2 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = remainderMajorant 71 * (1 / 2 : ℝ) ^ (k + 1) := by
          rw [pow_succ]
          ring

theorem remainderMajorant_tail_summable :
    Summable (fun k => remainderMajorant (71 + k)) := by
  have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  exact Summable.of_nonneg_of_le
    (fun k => remainderMajorant_nonneg (71 + k))
    remainderMajorant_shift_le_geometric
    (hgeom.mul_left (remainderMajorant 71))

theorem remainderMajorant_tail_lt_one :
    (∑' k, remainderMajorant (71 + k)) < 1 := by
  have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hscaled := hgeom.mul_left (remainderMajorant 71)
  have hrem := remainderMajorant_tail_summable
  have hle := hrem.tsum_le_tsum remainderMajorant_shift_le_geometric hscaled
  have hgeomSum : (∑' k : ℕ, (1 / 2 : ℝ) ^ k) = 2 := by
    rw [tsum_geometric_of_norm_lt_one (by norm_num)]
    norm_num
  have hscaledSum :
      (∑' k : ℕ, remainderMajorant 71 * (1 / 2 : ℝ) ^ k) =
        remainderMajorant 71 * 2 := by
    rw [tsum_mul_left, hgeomSum]
  rw [hscaledSum] at hle
  nlinarith [remainderMajorant_seventy_one_lt_half]

set_option maxHeartbeats 600000 in
theorem curvatureSeries_tail_norm_lt_one
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hx : |x| ≤ 10) :
    ‖∑' k, curvatureSeriesTerm r τ x (71 + k)‖ < 1 := by
  have hfull := curvatureSeriesTerm_summable (x := x) hr0 hr1 hτ0 hτ1
  have htail : Summable (fun k => curvatureSeriesTerm r τ x (71 + k)) :=
    by simpa [Nat.add_comm] using (summable_nat_add_iff 71).2 hfull
  have hnorm := norm_tsum_le_tsum_norm htail.norm
  have hmajorant := remainderMajorant_tail_summable
  have hcompare := htail.norm.tsum_le_tsum
    (fun k => norm_curvatureSeriesTerm_le_majorant
      hr0 hr1 hτ0 hτ1 hx (71 + k)) hmajorant
  linarith [remainderMajorant_tail_lt_one]

theorem compactTaylorFrom_eq_curvatureSeries_prefix
    (r τ u : ℝ) :
    compactTaylorFrom (powerTableUpTo (order + 1)) r τ u =
      ∑ N ∈ Finset.range 71, curvatureSeriesTerm r τ (10 * u) N := by
  unfold compactTaylorFrom
  rw [show order + 1 = 71 by rfl]
  apply Finset.sum_congr rfl
  intro N hN
  rw [powerTableUpTo_eval (Finset.mem_range.mp hN)]
  have hderivative : derivativeValue r τ = scalarDerivative r τ := by
    funext n
    exact derivativeValue_eq r τ n
  rw [hderivative]
  unfold curvatureSeriesTerm
  rw [mul_pow]
  ring

theorem coefficientSeries_pos_on_positive_compact
    {r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hx0 : 0 ≤ x) (hx10 : x ≤ 10) :
    0 < ∑' N, curvatureSeriesTerm r τ x N := by
  let u : ℝ := x / 10
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hxu : x = 10 * u := by dsimp [u]; ring
  have hprefix :
      1 ≤ ∑ N ∈ Finset.range 71, curvatureSeriesTerm r τ x N := by
    rw [hxu, ← compactTaylorFrom_eq_curvatureSeries_prefix]
    exact compactTaylor_ge_one hr0 hr1 hτ0 hτ1 hu0 hu1
  have hxabs : |x| ≤ 10 := by rw [abs_of_nonneg hx0]; exact hx10
  have htailNorm := curvatureSeries_tail_norm_lt_one
    hr0 hr1 hτ0 hτ1 hxabs
  have htailLower :
      -1 < ∑' k, curvatureSeriesTerm r τ x (71 + k) := by
    rw [Real.norm_eq_abs, abs_lt] at htailNorm
    exact htailNorm.1
  have hsum := curvatureSeriesTerm_summable (x := x) hr0 hr1 hτ0 hτ1
  have hsplit := hsum.sum_add_tsum_nat_add 71
  rw [show (∑' k, curvatureSeriesTerm r τ x (k + 71)) =
      ∑' k, curvatureSeriesTerm r τ x (71 + k) by
        congr 1
        funext k
        rw [Nat.add_comm]] at hsplit
  linarith

theorem firstFCurvature_pos_on_positive_compact
    {m₀ ω r τ x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hr : r = 3 * m₀) (hz : scalarZ r τ = ω ^ 2) (hω : ω ≠ 0)
    (hx0 : 0 ≤ x) (hx10 : x ≤ 10) :
    0 < x ^ 2 * (firstF m₀ ω x * firstF2 m₀ ω x -
        firstF1 m₀ ω x ^ 2) + 2 * firstF m₀ ω x ^ 2 := by
  rw [firstFCurvature_eq_coefficientSeries hr0 hr1 hτ0 hτ1 hr hz hω]
  exact coefficientSeries_pos_on_positive_compact
    hr0 hr1 hτ0 hτ1 hx0 hx10

end SSP.K3CyclicComplex.PositiveCoeff
