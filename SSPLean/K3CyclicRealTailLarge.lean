import SSPLean.K3CyclicRealTail
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum

/-!
# Large-index estimates for the three-state real-spectrum tail

This file isolates the `n ≥ 6` part of normalized complete-homogeneous
log-convexity.  The finite coefficient-cone certificates live in
`K3CyclicRealTail`; keeping the analytic tail separate avoids renormalizing
those larger polynomials during development.
-/

set_option autoImplicit false

namespace SSP.K3CyclicRealTail

open scoped BigOperators

/-- The palindromic polynomial occurring in the exact uniform-moment
determinant formula. -/
noncomputable def palindromicP (n : ℕ) (v : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (n - 1),
      (Nat.choose (k + 3) 3 : ℝ) * (v ^ k + v ^ (2 * n - 2 - k))) +
    (Nat.choose (n + 2) 3 : ℝ) * v ^ (n - 1)

theorem palindromicP_nonneg {n : ℕ} {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ palindromicP n v := by
  unfold palindromicP
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro k hk
    positivity
  · positivity

/-- The endpoint term alone gives the first lower bound used for small `v`. -/
theorem one_le_palindromicP {n : ℕ} {v : ℝ} (hn : 2 ≤ n) (hv : 0 ≤ v) :
    1 ≤ palindromicP n v := by
  let f : ℕ → ℝ := fun k =>
    (Nat.choose (k + 3) 3 : ℝ) * (v ^ k + v ^ (2 * n - 2 - k))
  have hf : ∀ k ∈ Finset.range (n - 1), 0 ≤ f k := by
    intro k hk
    dsimp [f]
    positivity
  have hmem : 0 ∈ Finset.range (n - 1) := by
    simp
    omega
  have hsingle : f 0 ≤ ∑ k ∈ Finset.range (n - 1), f k :=
    Finset.single_le_sum hf hmem
  have hf0 : 1 ≤ f 0 := by
    dsimp [f]
    norm_num
    positivity
  have hcentral :
      0 ≤ (Nat.choose (n + 2) 3 : ℝ) * v ^ (n - 1) := by positivity
  unfold palindromicP
  change 1 ≤ (∑ k ∈ Finset.range (n - 1), f k) +
    (Nat.choose (n + 2) 3 : ℝ) * v ^ (n - 1)
  linarith

/-- AM--GM for each symmetric pair in the palindromic polynomial. -/
theorem two_mul_pow_mid_le_pair {n k : ℕ} {v : ℝ} (hk : k ≤ n - 1) (hv : 0 ≤ v) :
    2 * v ^ (n - 1) ≤ v ^ k + v ^ (2 * n - 2 - k) := by
  have hk' : k ≤ 2 * n - 2 := by omega
  have hadd : k + (2 * n - 2 - k) = 2 * n - 2 := Nat.add_sub_of_le hk'
  have hdouble : 2 * n - 2 = (n - 1) + (n - 1) := by omega
  have hprod : v ^ k * v ^ (2 * n - 2 - k) = (v ^ (n - 1)) ^ 2 := by
    rw [← pow_add, hadd, hdouble, pow_add, pow_two]
  have ha : 0 ≤ v ^ k := pow_nonneg hv k
  have hb : 0 ≤ v ^ (2 * n - 2 - k) := pow_nonneg hv _
  have hc : 0 ≤ v ^ (n - 1) := pow_nonneg hv _
  nlinarith [hprod, sq_nonneg (v ^ k - v ^ (2 * n - 2 - k)),
    sq_nonneg (v ^ k + v ^ (2 * n - 2 - k) - 2 * v ^ (n - 1))]

/-- Summing the pairwise AM--GM estimates gives the central lower bound
before evaluation of the hockey-stick binomial sum. -/
theorem palindromicP_pair_lower {n : ℕ} {v : ℝ} (_hn : 2 ≤ n) (hv : 0 ≤ v) :
    (∑ k ∈ Finset.range (n - 1),
        (Nat.choose (k + 3) 3 : ℝ) * (2 * v ^ (n - 1))) +
        (Nat.choose (n + 2) 3 : ℝ) * v ^ (n - 1) ≤ palindromicP n v := by
  unfold palindromicP
  gcongr with k hk
  have hk' : k ≤ n - 1 := by
    have := Finset.mem_range.mp hk
    omega
  exact two_mul_pow_mid_le_pair hk' hv

/-- Hockey-stick evaluation of the paired lower bound. -/
theorem palindromicP_central_lower_choose {n : ℕ} {v : ℝ}
    (hn : 2 ≤ n) (hv : 0 ≤ v) :
    ((2 * Nat.choose (n + 2) 4 + Nat.choose (n + 2) 3 : ℕ) : ℝ) *
        v ^ (n - 1) ≤ palindromicP n v := by
  have hnrange : n - 1 = (n - 2) + 1 := by omega
  have hsumNat :
      (∑ k ∈ Finset.range (n - 1), Nat.choose (k + 3) 3) =
        Nat.choose (n + 2) 4 := by
    rw [hnrange]
    have h := Nat.sum_range_add_choose (n - 2) 3
    have harg : n - 2 + 3 + 1 = n + 2 := by omega
    rw [harg] at h
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hsumReal :
      (∑ k ∈ Finset.range (n - 1), (Nat.choose (k + 3) 3 : ℝ)) =
        (Nat.choose (n + 2) 4 : ℝ) := by
    exact_mod_cast hsumNat
  have hlower := palindromicP_pair_lower hn hv
  calc
    ((2 * Nat.choose (n + 2) 4 + Nat.choose (n + 2) 3 : ℕ) : ℝ) *
          v ^ (n - 1) =
        (∑ k ∈ Finset.range (n - 1),
          (Nat.choose (k + 3) 3 : ℝ) * (2 * v ^ (n - 1))) +
          (Nat.choose (n + 2) 3 : ℝ) * v ^ (n - 1) := by
            rw [← Finset.sum_mul, hsumReal]
            push_cast
            ring
    _ ≤ palindromicP n v := hlower

/-- The elementary second-difference identity for the binomial coefficients
appearing in `palindromicP`. -/
theorem cast_choose_three_add_two (m : ℕ) :
    (Nat.choose (m + 3) 3 : ℝ) =
      (Nat.choose (m + 1) 3 : ℝ) + (m + 1 : ℝ) ^ 2 := by
  have h₁ : Nat.choose (m + 3) 3 =
      Nat.choose (m + 2) 2 + Nat.choose (m + 2) 3 := by
    simpa using Nat.choose_succ_succ' (m + 2) 2
  have h₂ : Nat.choose (m + 2) 3 =
      Nat.choose (m + 1) 2 + Nat.choose (m + 1) 3 := by
    simpa using Nat.choose_succ_succ' (m + 1) 2
  rw [h₁, h₂]
  push_cast
  rw [Nat.cast_choose_two ℝ, Nat.cast_choose_two ℝ]
  push_cast
  field_simp
  ring

/-- The low-degree half of `palindromicP`. -/
noncomputable def chooseSeries (n : ℕ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose (k + 3) 3 : ℝ) * v ^ k

/-- The square-coefficient series produced by the second binomial
difference. -/
noncomputable def squareSeries (n : ℕ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (((k + 1) ^ 2 : ℕ) : ℝ) * v ^ k

theorem chooseSeries_succ (n : ℕ) (v : ℝ) :
    chooseSeries (n + 1) v = chooseSeries n v +
      (Nat.choose (n + 4) 3 : ℝ) * v ^ (n + 1) := by
  simp [chooseSeries, Finset.sum_range_succ]

theorem squareSeries_succ (n : ℕ) (v : ℝ) :
  squareSeries (n + 1) v = squareSeries n v +
      (((n + 2) ^ 2 : ℕ) : ℝ) * v ^ (n + 1) := by
  rw [squareSeries, squareSeries, Finset.sum_range_succ]

/-- Removing the first two terms of the binomial series leaves the series of
squares. -/
theorem chooseSeries_add_two (m : ℕ) (v : ℝ) :
    chooseSeries (m + 2) v = v ^ 2 * chooseSeries m v + squareSeries (m + 2) v := by
  induction m with
  | zero =>
      norm_num [chooseSeries, squareSeries, Finset.sum_range_succ, Nat.choose]
      ring
  | succ m ih =>
      rw [show m + 1 + 2 = (m + 2) + 1 by omega,
        chooseSeries_succ, squareSeries_succ, ih, chooseSeries_succ]
      have hc := cast_choose_three_add_two (m + 3)
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at hc ⊢
      rw [hc]
      ring

/-- The high-degree, reversed half of the palindromic polynomial. -/
noncomputable def reverseSeries (n : ℕ) (v : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n - 1),
    (Nat.choose (k + 3) 3 : ℝ) * v ^ (2 * n - 2 - k)

/-- Split `palindromicP` into its low/central series and reversed series. -/
theorem palindromicP_eq_chooseSeries_add_reverseSeries
    {n : ℕ} (hn : 2 ≤ n) (v : ℝ) :
    palindromicP n v = chooseSeries (n - 1) v + reverseSeries n v := by
  unfold palindromicP chooseSeries reverseSeries
  rw [Finset.sum_range_succ]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hcoeff : n - 1 + 3 = n + 2 := by omega
  rw [hcoeff]
  ring

/-- Multiplication by `v²` shifts the reversed series; only its new central
endpoint remains. -/
theorem reverseSeries_succ {n : ℕ} (hn : 2 ≤ n) (v : ℝ) :
    reverseSeries (n + 1) v = v ^ 2 * reverseSeries n v +
      (Nat.choose (n + 2) 3 : ℝ) * v ^ (n + 1) := by
  have hsum :
      (∑ k ∈ Finset.range (n - 1),
          (Nat.choose (k + 3) 3 : ℝ) * v ^ (2 * (n + 1) - 2 - k)) =
        v ^ 2 * reverseSeries n v := by
    rw [reverseSeries, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < n - 1 := Finset.mem_range.mp hk
    have hexp : 2 * (n + 1) - 2 - k = 2 + (2 * n - 2 - k) := by omega
    rw [hexp, pow_add]
    ring
  have hlast :
      (Nat.choose (n - 1 + 3) 3 : ℝ) *
          v ^ (2 * (n + 1) - 2 - (n - 1)) =
        (Nat.choose (n + 2) 3 : ℝ) * v ^ (n + 1) := by
    have hcoeff : n - 1 + 3 = n + 2 := by omega
    have hexp : 2 * (n + 1) - 2 - (n - 1) = n + 1 := by omega
    rw [hcoeff, hexp]
  have hrange : Finset.range n = Finset.range ((n - 1) + 1) := by
    congr 1
    omega
  have hsplit :
      (∑ k ∈ Finset.range n,
          (Nat.choose (k + 3) 3 : ℝ) * v ^ (2 * (n + 1) - 2 - k)) =
        (∑ k ∈ Finset.range (n - 1),
          (Nat.choose (k + 3) 3 : ℝ) * v ^ (2 * (n + 1) - 2 - k)) +
          (Nat.choose (n - 1 + 3) 3 : ℝ) *
            v ^ (2 * (n + 1) - 2 - (n - 1)) := by
    rw [hrange, Finset.sum_range_succ]
  change (∑ k ∈ Finset.range n,
      (Nat.choose (k + 3) 3 : ℝ) * v ^ (2 * (n + 1) - 2 - k)) =
    v ^ 2 * reverseSeries n v + (Nat.choose (n + 2) 3 : ℝ) * v ^ (n + 1)
  rw [hsplit, hsum, hlast]

/-- The matching boundary correction for the low-degree series. -/
theorem chooseSeries_boundary_recurrence {n : ℕ} (hn : 1 ≤ n) (v : ℝ) :
    chooseSeries n v + (Nat.choose (n + 2) 3 : ℝ) * v ^ (n + 1) =
      v ^ 2 * chooseSeries (n - 1) v + squareSeries n v := by
  have hidx : n - 1 + 2 = n + 1 := by omega
  have h := chooseSeries_add_two (n - 1) v
  rw [hidx, chooseSeries_succ, squareSeries_succ] at h
  have hc := cast_choose_three_add_two (n + 1)
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at hc h ⊢
  rw [hc] at h
  linear_combination h

/-- The palindromic polynomial satisfies the `v²` recurrence required by the
determinant induction. -/
theorem palindromicP_succ_vsq {n : ℕ} (hn : 2 ≤ n) (v : ℝ) :
    palindromicP (n + 1) v =
      v ^ 2 * palindromicP n v + squareSeries n v := by
  rw [palindromicP_eq_chooseSeries_add_reverseSeries (by omega) v,
    palindromicP_eq_chooseSeries_add_reverseSeries hn v,
    show n + 1 - 1 = n by omega, reverseSeries_succ hn v]
  have hlow := chooseSeries_boundary_recurrence (by omega : 1 ≤ n) v
  linear_combination hlow

/-- Closed form for the truncated square-weighted geometric series. -/
theorem squareSeries_closed (n : ℕ) (v : ℝ) :
    (1 - v) ^ 2 * squareSeries n v =
      (1 + v) * diagonal 1 v n + v ^ (n + 1) *
        (((n + 1 : ℝ) ^ 2) * v - (n + 1 : ℝ) * (n + 3 : ℝ)) := by
  induction n with
  | zero =>
      norm_num [squareSeries, diagonal, Finset.sum_range_succ]
      ring
  | succ n ih =>
      rw [squareSeries_succ, diagonal_succ]
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at ih ⊢
      rw [pow_succ]
      linear_combination ih

/-- Geometric-sum identity for `diagonal 1 v n`. -/
theorem one_sub_mul_diagonal_add_pow (n : ℕ) (v : ℝ) :
    (1 - v) * diagonal 1 v n + v ^ (n + 1) = 1 := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      rw [diagonal_succ, pow_succ]
      ring_nf at ih ⊢
      linear_combination ih

/-- The denominator-cleared uniform Hankel determinant. -/
noncomputable def scaledUniformDet (n : ℕ) (v : ℝ) : ℝ :=
  (n + 1 : ℝ) ^ 2 * diagonal 1 v (n - 1) * diagonal 1 v (n + 1) -
    (n : ℝ) * (n + 2 : ℝ) * diagonal 1 v n ^ 2

/-- The denominator-cleared determinant satisfies the same `v²` recurrence
as the palindromic polynomial. -/
theorem scaledUniformDet_succ_vsq {n : ℕ} (hn : 1 ≤ n) (v : ℝ) :
    scaledUniformDet (n + 1) v =
      v ^ 2 * scaledUniformDet n v + (1 - v) ^ 2 * squareSeries n v := by
  have hprev := diagonal_succ (1 : ℝ) v (n - 1)
  rw [show n - 1 + 1 = n by omega] at hprev
  have hprev' : diagonal 1 v (n - 1) = diagonal 1 v n - v ^ n := by
    linarith
  have hsquare := squareSeries_closed n v
  have hgeom := one_sub_mul_diagonal_add_pow n v
  unfold scaledUniformDet
  simp only [Nat.add_sub_cancel]
  rw [hprev', diagonal_succ (1 : ℝ) v (n + 1),
    diagonal_succ (1 : ℝ) v n, hsquare]
  simp only [one_mul]
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at hgeom ⊢
  rw [pow_succ]
  ring_nf at hgeom ⊢
  linear_combination
    ((n : ℝ) ^ 2 * v ^ n * v ^ 2 - (n : ℝ) ^ 2 * v ^ n * v +
      2 * (n : ℝ) * v ^ n * v ^ 2 - 4 * (n : ℝ) * v ^ n * v +
      diagonal 1 v n * v + diagonal 1 v n + v ^ n * v ^ 2 -
      3 * v ^ n * v) * hgeom

/-- Clearing the three moment normalizations produces `scaledUniformDet`. -/
theorem uniformDet_mul_denominator {n : ℕ} (hn : 1 ≤ n) (v : ℝ) :
    uniformDet 1 v n * ((n : ℝ) * (n + 1 : ℝ) ^ 2 * (n + 2 : ℝ)) =
      scaledUniformDet n v := by
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hpredR : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast hpred
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
  have hn2' : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
  unfold uniformDet uniformMoment scaledUniformDet
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [hpredR]
  field_simp [hn0, hn1, hn2, hn2']
  ring

/-- The desired polynomial identity, isolated from the harmless denominator
arithmetic. -/
def UniformDetPolynomialIdentity (n : ℕ) (v : ℝ) : Prop :=
  scaledUniformDet n v = (1 - v) ^ 2 * palindromicP n v

theorem uniformDetPolynomialIdentity_two (v : ℝ) :
    UniformDetPolynomialIdentity 2 v := by
  unfold UniformDetPolynomialIdentity scaledUniformDet palindromicP diagonal
  norm_num [Finset.sum_range_succ]
  ring

/-- The common positive increment suggested by the palindromic recurrence. -/
noncomputable def squareIncrement (n : ℕ) (v : ℝ) : ℝ :=
  v ^ n * ∑ k ∈ Finset.range (n + 1),
    (((n + 1 - k) ^ 2 : ℕ) : ℝ) * v ^ k

theorem squareIncrement_nonneg {n : ℕ} {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ squareIncrement n v := by
  unfold squareIncrement
  apply mul_nonneg (pow_nonneg hv n)
  apply Finset.sum_nonneg
  intro k hk
  positivity

/-- If the scaled determinant and `P_n` satisfy their matching recurrences,
the polynomial identity propagates by induction. -/
theorem uniformDetPolynomialIdentity_succ_of_recurrences
    {n : ℕ} {v : ℝ} (hid : UniformDetPolynomialIdentity n v)
    (hdet : scaledUniformDet (n + 1) v =
      scaledUniformDet n v + (1 - v) ^ 2 * squareIncrement n v)
    (hP : palindromicP (n + 1) v = palindromicP n v + squareIncrement n v) :
    UniformDetPolynomialIdentity (n + 1) v := by
  unfold UniformDetPolynomialIdentity at hid ⊢
  rw [hdet, hid, hP]
  ring

/-- Equivalent induction interface using the simpler `v²` recurrence. -/
theorem uniformDetPolynomialIdentity_succ_of_vsq_recurrences
    {n : ℕ} {v : ℝ} (hid : UniformDetPolynomialIdentity n v)
    (hdet : scaledUniformDet (n + 1) v =
      v ^ 2 * scaledUniformDet n v + (1 - v) ^ 2 * squareSeries n v)
    (hP : palindromicP (n + 1) v =
      v ^ 2 * palindromicP n v + squareSeries n v) :
    UniformDetPolynomialIdentity (n + 1) v := by
  unfold UniformDetPolynomialIdentity at hid ⊢
  rw [hdet, hid, hP]
  ring

/-- Exact polynomial identity for every index in the tail range. -/
theorem uniformDetPolynomialIdentity {n : ℕ} (hn : 2 ≤ n) (v : ℝ) :
    UniformDetPolynomialIdentity n v := by
  induction n, hn using Nat.le_induction with
  | base => exact uniformDetPolynomialIdentity_two v
  | succ n hn ih =>
      exact uniformDetPolynomialIdentity_succ_of_vsq_recurrences ih
        (scaledUniformDet_succ_vsq (by omega) v) (palindromicP_succ_vsq hn v)

/-- The exact right side of the uniform-moment determinant identity. -/
noncomputable def uniformDetClosed (n : ℕ) (v : ℝ) : ℝ :=
  (1 - v) ^ 2 * palindromicP n v /
    ((n : ℝ) * (n + 1 : ℝ) ^ 2 * (n + 2 : ℝ))

theorem uniformDetClosed_nonneg {n : ℕ} {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ uniformDetClosed n v := by
  unfold uniformDetClosed
  apply div_nonneg
  · exact mul_nonneg (sq_nonneg (1 - v)) (palindromicP_nonneg hv)
  · positivity

/-- Once the polynomial identity is known, the exact determinant formula
follows by division by its positive normalization. -/
theorem uniformDet_eq_closed_of_polynomialIdentity {n : ℕ} (hn : 1 ≤ n) (v : ℝ)
    (hid : UniformDetPolynomialIdentity n v) :
    uniformDet 1 v n = uniformDetClosed n v := by
  have hden : 0 < (n : ℝ) * (n + 1 : ℝ) ^ 2 * (n + 2 : ℝ) := by positivity
  have hmul := uniformDet_mul_denominator hn v
  unfold UniformDetPolynomialIdentity at hid
  unfold uniformDetClosed
  rw [eq_div_iff hden.ne']
  rw [hmul, hid]

/-- Exact uniform-moment determinant formula from the manuscript. -/
theorem uniformDet_eq_closed {n : ℕ} (hn : 2 ≤ n) (v : ℝ) :
    uniformDet 1 v n = uniformDetClosed n v :=
  uniformDet_eq_closed_of_polynomialIdentity (by omega) v
    (uniformDetPolynomialIdentity hn v)

/-- Lower bound obtained from the constant endpoint term `P_n(v) ≥ 1`. -/
theorem uniformDet_lower_one {n : ℕ} (hn : 2 ≤ n) {v : ℝ} (hv : 0 ≤ v) :
    (1 - v) ^ 2 /
        ((n : ℝ) * (n + 1 : ℝ) ^ 2 * (n + 2 : ℝ)) ≤ uniformDet 1 v n := by
  rw [uniformDet_eq_closed hn v]
  unfold uniformDetClosed
  have hden : 0 < (n : ℝ) * (n + 1 : ℝ) ^ 2 * (n + 2 : ℝ) := by positivity
  apply (div_le_div_iff_of_pos_right hden).mpr
  simpa using
    mul_le_mul_of_nonneg_left (one_le_palindromicP hn hv) (sq_nonneg (1 - v))

/-- Central lower bound before simplifying its binomial coefficient. -/
theorem uniformDet_lower_central_choose {n : ℕ} (hn : 2 ≤ n) {v : ℝ}
    (hv : 0 ≤ v) :
    (1 - v) ^ 2 *
          (((2 * Nat.choose (n + 2) 4 + Nat.choose (n + 2) 3 : ℕ) : ℝ) *
            v ^ (n - 1)) /
        ((n : ℝ) * (n + 1 : ℝ) ^ 2 * (n + 2 : ℝ)) ≤ uniformDet 1 v n := by
  rw [uniformDet_eq_closed hn v]
  unfold uniformDetClosed
  have hden : 0 < (n : ℝ) * (n + 1 : ℝ) ^ 2 * (n + 2 : ℝ) := by positivity
  apply (div_le_div_iff_of_pos_right hden).mpr
  exact mul_le_mul_of_nonneg_left (palindromicP_central_lower_choose hn hv)
    (sq_nonneg (1 - v))

/-- Closed form for the cubic binomial coefficient used in the central
coefficient.  The shifted statement avoids subtraction on naturals. -/
theorem cast_choose_add_two_three (n : ℕ) :
    (Nat.choose (n + 2) 3 : ℝ) =
      (n : ℝ) * (n + 1 : ℝ) * (n + 2 : ℝ) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hpascal := Nat.choose_succ_succ' (n + 2) 2
      norm_num only [Nat.cast_add, Nat.cast_one] at ih ⊢
      rw [hpascal, Nat.cast_add, Nat.cast_choose_two, ih]
      norm_num only [Nat.cast_add, Nat.cast_one]
      ring

/-- Closed form for the quartic binomial coefficient in the range in which
it is used below. -/
theorem cast_choose_add_two_four {n : ℕ} (hn : 2 ≤ n) :
    (Nat.choose (n + 2) 4 : ℝ) =
      ((n : ℝ) - 1) * n * (n + 1 : ℝ) * (n + 2 : ℝ) / 24 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hpascal := Nat.choose_succ_succ' (n + 2) 3
      norm_num only [Nat.cast_add, Nat.cast_one] at ih ⊢
      rw [hpascal, Nat.cast_add, cast_choose_add_two_three, ih]
      ring

/-- Evaluation of the coefficient produced by pairing the palindromic
terms. -/
theorem centralCoefficient_closed {n : ℕ} (hn : 2 ≤ n) :
    ((2 * Nat.choose (n + 2) 4 + Nat.choose (n + 2) 3 : ℕ) : ℝ) =
      (n : ℝ) * (n + 1 : ℝ) ^ 2 * (n + 2 : ℝ) / 12 := by
  push_cast
  rw [cast_choose_add_two_four hn, cast_choose_add_two_three]
  ring

/-- The central AM--GM estimate in its cancellation-ready form. -/
theorem uniformDet_lower_central {n : ℕ} (hn : 2 ≤ n) {v : ℝ}
    (hv : 0 ≤ v) :
    (1 - v) ^ 2 / 12 * v ^ (n - 1) ≤ uniformDet 1 v n := by
  have h := uniformDet_lower_central_choose hn hv
  rw [centralCoefficient_closed hn] at h
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
  field_simp [hn0, hn1, hn2] at h ⊢
  nlinarith

/-- The pointwise-maximization constant
`4 (n-1)^(n-1) / (n+1)^(n+1)`. -/
noncomputable def crossCoefficient (n : ℕ) : ℝ :=
  4 * ((n - 1 : ℕ) : ℝ) ^ (n - 1) / (n + 1 : ℝ) ^ (n + 1)

theorem crossCoefficient_nonneg (n : ℕ) : 0 ≤ crossCoefficient n := by
  unfold crossCoefficient
  apply div_nonneg <;> positivity

/-- The root-simplex cap on the smaller root. -/
noncomputable def rootCap (v : ℝ) : ℝ :=
  min v ((1 - Real.sqrt v) ^ 2)

theorem rootCap_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ rootCap v := by
  unfold rootCap
  exact le_min hv (sq_nonneg (1 - Real.sqrt v))

theorem smallerRoot_le_rootCap {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u ≤ v) (hroot : Real.sqrt u + Real.sqrt v ≤ 1) :
    u ≤ rootCap v := by
  exact le_min_root_bounds hu hv huv hroot

/-- A geometric-sum upper bound for the uniform moment on `[v,1]`. -/
theorem uniformMoment_one_upper {m : ℕ} {v : ℝ} (hv : 0 ≤ v) (hv1 : v < 1) :
    uniformMoment 1 v m ≤ 1 / ((m + 1 : ℝ) * (1 - v)) := by
  have hsub : 0 < 1 - v := sub_pos.mpr hv1
  have hgeom := one_sub_mul_diagonal_add_pow m v
  have hdiag : diagonal 1 v m ≤ 1 / (1 - v) := by
    apply (le_div_iff₀ hsub).mpr
    nlinarith [pow_nonneg hv (m + 1)]
  unfold uniformMoment
  calc
    diagonal 1 v m / (m + 1 : ℝ) ≤
        (1 / (1 - v)) / (m + 1 : ℝ) := by
          exact div_le_div_of_nonneg_right hdiag (by positivity)
    _ = 1 / ((m + 1 : ℝ) * (1 - v)) := by
          field_simp

/-- The numerical sequence needed in the small-`v` region is already
decreasing from index six onward. -/
theorem largeIndex_quarter_bound {n : ℕ} (hn : 6 ≤ n) :
    (n : ℝ) * (n + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ n ≤
      (3 / 4 : ℝ) ^ 3 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hcoef :
          (n + 1 : ℝ) * (n + 2 : ℝ) ^ 2 * (1 / 4 : ℝ) ≤
            (n : ℝ) * (n + 1 : ℝ) ^ 2 := by
        norm_num only [Nat.cast_add, Nat.cast_one]
        have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith [sq_nonneg ((n : ℝ) - 1)]
      calc
        ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) + 1 : ℝ) ^ 2 *
              (1 / 4 : ℝ) ^ (n + 1) =
            ((n + 1 : ℝ) * (n + 2 : ℝ) ^ 2 * (1 / 4 : ℝ)) *
              (1 / 4 : ℝ) ^ n := by
                rw [pow_succ]
                norm_num only [Nat.cast_add, Nat.cast_one]
                ring
        _ ≤ ((n : ℝ) * (n + 1 : ℝ) ^ 2) * (1 / 4 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (by norm_num) n)
        _ ≤ (3 / 4 : ℝ) ^ 3 := ih

/-- Polynomial estimate that closes the `0 ≤ v ≤ 1/4` region. -/
theorem largeIndex_small_v_polynomial_bound {n : ℕ} (hn : 6 ≤ n)
    {v : ℝ} (hv : 0 ≤ v) (hvq : v ≤ 1 / 4) :
    (n : ℝ) * (n + 1 : ℝ) ^ 2 * v ^ n ≤ (1 - v) ^ 3 := by
  have hvpow : v ^ n ≤ (1 / 4 : ℝ) ^ n := by
    exact pow_le_pow_left₀ hv hvq n
  have hcoeff : 0 ≤ (n : ℝ) * (n + 1 : ℝ) ^ 2 := by positivity
  calc
    (n : ℝ) * (n + 1 : ℝ) ^ 2 * v ^ n ≤
        (n : ℝ) * (n + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left hvpow hcoeff
    _ ≤ (3 / 4 : ℝ) ^ 3 := largeIndex_quarter_bound hn
    _ ≤ (1 - v) ^ 3 := by
      have hbase : (3 / 4 : ℝ) ≤ 1 - v := by linarith
      exact pow_le_pow_left₀ (by norm_num) hbase 3

/-- The one-variable cross-term estimate on the small-`v` half of the
large-index range. -/
theorem oneVariableMomentBound_small_v {n : ℕ} (hn : 6 ≤ n)
    {v : ℝ} (hv : 0 ≤ v) (hvq : v ≤ 1 / 4) :
    rootCap v * min (v ^ (n - 1)) (crossCoefficient n) *
        uniformMoment 1 v (n + 1) ≤ uniformDet 1 v n := by
  have hn2 : 2 ≤ n := by omega
  have hv1 : v < 1 := by linarith
  have hA := uniformMoment_one_upper (m := n + 1) hv hv1
  have hA' :
      uniformMoment 1 v (n + 1) ≤ 1 / ((n + 2 : ℝ) * (1 - v)) := by
    convert hA using 1
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  have hAnonneg : 0 ≤ uniformMoment 1 v (n + 1) :=
    uniformMoment_nonneg (by norm_num) hv _
  have hcap : rootCap v ≤ v := min_le_left _ _
  have hcap0 : 0 ≤ rootCap v := rootCap_nonneg hv
  have hmin : min (v ^ (n - 1)) (crossCoefficient n) ≤ v ^ (n - 1) :=
    min_le_left _ _
  have hmin0 : 0 ≤ min (v ^ (n - 1)) (crossCoefficient n) :=
    le_min (pow_nonneg hv _) (crossCoefficient_nonneg n)
  have hpoly := largeIndex_small_v_polynomial_bound hn hv hvq
  have hsub : 0 < 1 - v := sub_pos.mpr hv1
  have hden : 0 <
      (n : ℝ) * (n + 1 : ℝ) ^ 2 * (n + 2 : ℝ) := by positivity
  have hbridge :
      v ^ n / ((n + 2 : ℝ) * (1 - v)) ≤
        (1 - v) ^ 2 /
          ((n : ℝ) * (n + 1 : ℝ) ^ 2 * (n + 2 : ℝ)) := by
    apply (div_le_div_iff₀ (mul_pos (by positivity) hsub) hden).mpr
    nlinarith
  have hvpowmul : v * v ^ (n - 1) = v ^ n := by
    calc
      v * v ^ (n - 1) = v ^ (n - 1) * v := by ring
      _ = v ^ ((n - 1) + 1) := (pow_succ v (n - 1)).symm
      _ = v ^ n := by congr 1; omega
  calc
    rootCap v * min (v ^ (n - 1)) (crossCoefficient n) *
          uniformMoment 1 v (n + 1) ≤
        v * v ^ (n - 1) * uniformMoment 1 v (n + 1) := by
          gcongr
    _ = v ^ n * uniformMoment 1 v (n + 1) := by
      rw [hvpowmul]
    _ ≤ v ^ n * (1 / ((n + 2 : ℝ) * (1 - v))) :=
      mul_le_mul_of_nonneg_left hA' (pow_nonneg hv n)
    _ = v ^ n / ((n + 2 : ℝ) * (1 - v)) := by ring
    _ ≤ (1 - v) ^ 2 /
        ((n : ℝ) * (n + 1 : ℝ) ^ 2 * (n + 2 : ℝ)) := hbridge
    _ ≤ uniformDet 1 v n := uniformDet_lower_one hn2 hv

/-- On `1/2 ≤ b ≤ 2/3`, the elementary factor in the transition
estimate is bounded uniformly away from twelve. -/
theorem middleTransitionFactor {n : ℕ} (hn : 6 ≤ n) {b : ℝ}
    (hb₁ : 1 / 2 ≤ b) (hb₂ : b ≤ 2 / 3) :
    12 ≤ (n + 2 : ℝ) * (1 - b) * (1 + b) ^ 3 := by
  have hb2sq : (1 / 2 : ℝ) ^ 2 ≤ b ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hb₁ 2
  have hb2cube : (1 / 2 : ℝ) ^ 3 ≤ b ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hb₁ 3
  have hq : 0 ≤ 27 * b ^ 3 + 72 * b ^ 2 + 48 * b - 22 := by
    nlinarith
  have hfactor :
      (1 - 2 / 3) * (1 + 2 / 3) ^ 3 ≤ (1 - b) * (1 + b) ^ 3 := by
    have hprod : 0 ≤ (2 - 3 * b) *
        (27 * b ^ 3 + 72 * b ^ 2 + 48 * b - 22) :=
      mul_nonneg (by linarith) hq
    nlinarith
  have hnR : (8 : ℝ) ≤ n + 2 := by exact_mod_cast (show 8 ≤ n + 2 by omega)
  have hf0 : 0 ≤ (1 - b) * (1 + b) ^ 3 := by
    have hb0 : 0 ≤ b := by linarith
    positivity
  nlinarith

/-- The one-variable cross-term estimate on the fixed middle interval
`1/4 ≤ v ≤ 4/9`.  This avoids introducing the moving transition
point until it is genuinely needed. -/
theorem oneVariableMomentBound_middle_v {n : ℕ} (hn : 6 ≤ n)
    {v : ℝ} (hvq : 1 / 4 ≤ v) (hv49 : v ≤ 4 / 9) :
    rootCap v * min (v ^ (n - 1)) (crossCoefficient n) *
        uniformMoment 1 v (n + 1) ≤ uniformDet 1 v n := by
  have hv : 0 ≤ v := by linarith
  have hv1 : v < 1 := by linarith
  let b : ℝ := Real.sqrt v
  have hb0 : 0 ≤ b := Real.sqrt_nonneg v
  have hb2 : b ^ 2 = v := by
    dsimp [b]
    exact Real.sq_sqrt hv
  have hbhalf : 1 / 2 ≤ b := by nlinarith
  have hb23 : b ≤ 2 / 3 := by nlinarith
  have htransition := middleTransitionFactor hn hbhalf hb23
  have hA := uniformMoment_one_upper (m := n + 1) hv hv1
  have hA' :
      uniformMoment 1 v (n + 1) ≤ 1 / ((n + 2 : ℝ) * (1 - v)) := by
    convert hA using 1
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  have hden : 0 < (n + 2 : ℝ) * (1 - v) := by positivity
  have hAcentral : uniformMoment 1 v (n + 1) ≤ (1 + b) ^ 2 / 12 := by
    calc
      uniformMoment 1 v (n + 1) ≤
          1 / ((n + 2 : ℝ) * (1 - v)) := hA'
      _ ≤ (1 + b) ^ 2 / 12 := by
        apply (div_le_iff₀ hden).mpr
        rw [← hb2]
        nlinarith [htransition]
  have hAnonneg : 0 ≤ uniformMoment 1 v (n + 1) :=
    uniformMoment_nonneg (by norm_num) hv _
  have hcap : rootCap v ≤ (1 - b) ^ 2 := min_le_right _ _
  have hcap0 : 0 ≤ rootCap v := rootCap_nonneg hv
  have hmin : min (v ^ (n - 1)) (crossCoefficient n) ≤ v ^ (n - 1) :=
    min_le_left _ _
  have hmin0 : 0 ≤ min (v ^ (n - 1)) (crossCoefficient n) :=
    le_min (pow_nonneg hv _) (crossCoefficient_nonneg n)
  calc
    rootCap v * min (v ^ (n - 1)) (crossCoefficient n) *
          uniformMoment 1 v (n + 1) ≤
        (1 - b) ^ 2 * v ^ (n - 1) * uniformMoment 1 v (n + 1) := by
          gcongr
    _ ≤ (1 - b) ^ 2 * v ^ (n - 1) * ((1 + b) ^ 2 / 12) := by
      gcongr
    _ = (1 - v) ^ 2 / 12 * v ^ (n - 1) := by
      rw [← hb2]
      ring
    _ ≤ uniformDet 1 v n := uniformDet_lower_central (by omega) hv

/-- Combined result for the portion of the large-index range that does not
need the moving transition point. -/
theorem oneVariableMomentBound_le_four_ninths {n : ℕ} (hn : 6 ≤ n)
    {v : ℝ} (hv : 0 ≤ v) (hv49 : v ≤ 4 / 9) :
    rootCap v * min (v ^ (n - 1)) (crossCoefficient n) *
        uniformMoment 1 v (n + 1) ≤ uniformDet 1 v n := by
  by_cases hvq : v ≤ 1 / 4
  · exact oneVariableMomentBound_small_v hn hv hvq
  · exact oneVariableMomentBound_middle_v hn (by linarith) hv49

/-- The remaining scalar inequality after writing `v = b²`. -/
def LargeTransitionInequality (n : ℕ) (b : ℝ) : Prop :=
  12 * uniformMoment 1 (b ^ 2) (n + 1) / (1 + b) ^ 2 *
      min 1 (crossCoefficient n / b ^ (2 * n - 2)) ≤ 1

theorem min_eq_mul_min_div {x c : ℝ} (hx : 0 < x) :
    min x c = x * min 1 (c / x) := by
  by_cases hcx : c ≤ x
  · have hdiv : c / x ≤ 1 := (div_le_one hx).mpr hcx
    rw [min_eq_right hcx, min_eq_right hdiv]
    field_simp
  · have hxc : x ≤ c := le_of_not_ge hcx
    have hdiv : 1 ≤ c / x := (le_div_iff₀ hx).mpr (by simpa using hxc)
    rw [min_eq_left hxc, min_eq_left hdiv]
    ring

/-- The manuscript's transition inequality implies the one-variable moment
bound on the remaining interval. -/
theorem oneVariableMomentBound_high_of_transition {n : ℕ} (hn : 6 ≤ n)
    {v : ℝ} (hv49 : 4 / 9 ≤ v) (hv1 : v ≤ 1)
    (htransition : LargeTransitionInequality n (Real.sqrt v)) :
    rootCap v * min (v ^ (n - 1)) (crossCoefficient n) *
        uniformMoment 1 v (n + 1) ≤ uniformDet 1 v n := by
  have hv : 0 ≤ v := by linarith
  let b : ℝ := Real.sqrt v
  have hb0 : 0 ≤ b := Real.sqrt_nonneg v
  have hb2 : b ^ 2 = v := by
    dsimp [b]
    exact Real.sq_sqrt hv
  have hb23 : 2 / 3 ≤ b := by nlinarith
  have hb1 : b ≤ 1 := by nlinarith
  have hbpos : 0 < b := by linarith
  have hpow : b ^ (2 * n - 2) = v ^ (n - 1) := by
    rw [show 2 * n - 2 = 2 * (n - 1) by omega, pow_mul, hb2]
  have hvpowpos : 0 < v ^ (n - 1) := pow_pos (by nlinarith) _
  have hminfactor := min_eq_mul_min_div
    (x := v ^ (n - 1)) (c := crossCoefficient n) hvpowpos
  have htransition' :
      12 * uniformMoment 1 v (n + 1) / (1 + b) ^ 2 *
          min 1 (crossCoefficient n / v ^ (n - 1)) ≤ 1 := by
    simpa [LargeTransitionInequality, b, hb2, hpow] using htransition
  have hmin0 : 0 ≤ min 1 (crossCoefficient n / v ^ (n - 1)) := by
    apply le_min (by norm_num)
    exact div_nonneg (crossCoefficient_nonneg n) (le_of_lt hvpowpos)
  have hA0 : 0 ≤ uniformMoment 1 v (n + 1) :=
    uniformMoment_nonneg (by norm_num) hv _
  have hbden : 0 < (1 + b) ^ 2 := sq_pos_of_pos (by linarith)
  have hscaled :
      uniformMoment 1 v (n + 1) *
          min 1 (crossCoefficient n / v ^ (n - 1)) ≤ (1 + b) ^ 2 / 12 := by
    have hfactor : 0 ≤ (1 + b) ^ 2 / 12 := by positivity
    have hmul := mul_le_mul_of_nonneg_right htransition' hfactor
    field_simp [hbden.ne'] at hmul ⊢
    nlinarith
  have hcap : rootCap v ≤ (1 - b) ^ 2 := min_le_right _ _
  have hcap0 := rootCap_nonneg hv
  have hcentral := uniformDet_lower_central (by omega : 2 ≤ n) hv
  calc
    rootCap v * min (v ^ (n - 1)) (crossCoefficient n) *
          uniformMoment 1 v (n + 1) =
        rootCap v * v ^ (n - 1) *
          (uniformMoment 1 v (n + 1) *
            min 1 (crossCoefficient n / v ^ (n - 1))) := by
              rw [hminfactor]
              ring
    _ ≤ (1 - b) ^ 2 * v ^ (n - 1) * ((1 + b) ^ 2 / 12) := by
      gcongr
    _ = (1 - v) ^ 2 / 12 * v ^ (n - 1) := by
      rw [← hb2]
      ring
    _ ≤ uniformDet 1 v n := hcentral

/-- A coarse bound sufficient to discharge the endpoint `b = 1`. -/
theorem crossCoefficient_le_one_third {n : ℕ} (hn : 6 ≤ n) :
    crossCoefficient n ≤ 1 / 3 := by
  have hbase : ((n - 1 : ℕ) : ℝ) ≤ (n + 1 : ℝ) := by
    exact_mod_cast (show n - 1 ≤ n + 1 by omega)
  have hpow : ((n - 1 : ℕ) : ℝ) ^ (n - 1) ≤
      (n + 1 : ℝ) ^ (n - 1) := by
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hcoef : (4 : ℝ) ≤ (n + 1 : ℝ) ^ 2 / 3 := by
    have hnR : (7 : ℝ) ≤ n + 1 := by
      exact_mod_cast (show 7 ≤ n + 1 by omega)
    nlinarith
  have hp0 : 0 ≤ (n + 1 : ℝ) ^ (n - 1) := by positivity
  have hnum :
      4 * ((n - 1 : ℕ) : ℝ) ^ (n - 1) ≤
        (n + 1 : ℝ) ^ (n + 1) / 3 := by
    calc
      4 * ((n - 1 : ℕ) : ℝ) ^ (n - 1) ≤
          4 * (n + 1 : ℝ) ^ (n - 1) :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ ((n + 1 : ℝ) ^ 2 / 3) * (n + 1 : ℝ) ^ (n - 1) :=
        mul_le_mul_of_nonneg_right hcoef hp0
      _ = (n + 1 : ℝ) ^ (n + 1) / 3 := by
        rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
        ring
  unfold crossCoefficient
  have hden : 0 < (n + 1 : ℝ) ^ (n + 1) := by positivity
  apply (div_le_iff₀ hden).mpr
  nlinarith

theorem largeTransitionInequality_one {n : ℕ} (hn : 6 ≤ n) :
    LargeTransitionInequality n 1 := by
  have hc := crossCoefficient_le_one_third hn
  have hmin : min 1 (crossCoefficient n) ≤ 1 / 3 :=
    le_trans (min_le_right _ _) hc
  simp only [LargeTransitionInequality, one_pow, uniformMoment_self,
    one_add_one_eq_two]
  norm_num
  nlinarith

/-- The transition inequality on the fixed interval already handled by the
middle estimate. -/
theorem largeTransitionInequality_middle {n : ℕ} (hn : 6 ≤ n) {b : ℝ}
    (hb₁ : 1 / 2 ≤ b) (hb₂ : b ≤ 2 / 3) :
    LargeTransitionInequality n b := by
  have hb0 : 0 ≤ b := by linarith
  have hb1 : b ^ 2 < 1 := by nlinarith
  have hA := uniformMoment_one_upper (m := n + 1) (sq_nonneg b) hb1
  have hA' :
      uniformMoment 1 (b ^ 2) (n + 1) ≤
        1 / ((n + 2 : ℝ) * (1 - b ^ 2)) := by
    convert hA using 1
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  have hfactor := middleTransitionFactor hn hb₁ hb₂
  have hden : 0 < (n + 2 : ℝ) * (1 - b ^ 2) := by positivity
  have hbasic : 12 * uniformMoment 1 (b ^ 2) (n + 1) / (1 + b) ^ 2 ≤ 1 := by
    have hbplus : 0 < (1 + b) ^ 2 := by positivity
    have hAcentral : uniformMoment 1 (b ^ 2) (n + 1) ≤ (1 + b) ^ 2 / 12 := by
      calc
        uniformMoment 1 (b ^ 2) (n + 1) ≤
            1 / ((n + 2 : ℝ) * (1 - b ^ 2)) := hA'
        _ ≤ (1 + b) ^ 2 / 12 := by
          apply (div_le_iff₀ hden).mpr
          nlinarith [hfactor]
    apply (div_le_iff₀ hbplus).mpr
    nlinarith
  have hbasic0 : 0 ≤ 12 * uniformMoment 1 (b ^ 2) (n + 1) / (1 + b) ^ 2 := by
    apply div_nonneg
    · exact mul_nonneg (by norm_num) (uniformMoment_nonneg (by norm_num) (sq_nonneg b) _)
    · exact sq_nonneg (1 + b)
  have hmin0 : 0 ≤ min 1 (crossCoefficient n / b ^ (2 * n - 2)) := by
    apply le_min (by norm_num)
    exact div_nonneg (crossCoefficient_nonneg n) (pow_nonneg hb0 _)
  unfold LargeTransitionInequality
  calc
    12 * uniformMoment 1 (b ^ 2) (n + 1) / (1 + b) ^ 2 *
          min 1 (crossCoefficient n / b ^ (2 * n - 2)) ≤
        12 * uniformMoment 1 (b ^ 2) (n + 1) / (1 + b) ^ 2 * 1 := by
      gcongr
      exact min_le_left _ _
    _ ≤ 1 := by simpa using hbasic

/-- The sole remaining analytic statement for the large-index range. -/
def LargeTransitionTail (n : ℕ) : Prop :=
  ∀ b : ℝ, 2 / 3 ≤ b → b ≤ 1 → LargeTransitionInequality n b

/-- Assembly of the complete one-variable estimate from the proved lower
range and the scalar transition tail. -/
theorem oneVariableMomentBound_of_transitionTail {n : ℕ} (hn : 6 ≤ n)
    (htail : LargeTransitionTail n) {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    rootCap v * min (v ^ (n - 1)) (crossCoefficient n) *
        uniformMoment 1 v (n + 1) ≤ uniformDet 1 v n := by
  by_cases hv49 : v ≤ 4 / 9
  · exact oneVariableMomentBound_le_four_ninths hn hv hv49
  · have hb23 : 2 / 3 ≤ Real.sqrt v := by
      have hsqrt0 := Real.sqrt_nonneg v
      have hsquare := Real.sq_sqrt hv
      nlinarith
    have hb1 : Real.sqrt v ≤ 1 := by
      have hsqrt0 := Real.sqrt_nonneg v
      have hsquare := Real.sq_sqrt hv
      nlinarith
    exact oneVariableMomentBound_high_of_transition hn (by linarith) hv1
      (htail (Real.sqrt v) hb23 hb1)

/-- Scaling both endpoints factors out the expected homogeneous power from
`diagonal`. -/
theorem diagonal_scale_left {a b : ℝ} (ha : a ≠ 0) (m : ℕ) :
    diagonal a b m = a ^ m * diagonal 1 (b / a) m := by
  unfold diagonal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by
    have := Finset.mem_range.mp hk
    omega
  rw [one_pow, one_mul, div_pow]
  field_simp [pow_ne_zero k ha]
  calc
    a ^ k * b ^ (m - k) * a ^ (m - k) =
        b ^ (m - k) * (a ^ k * a ^ (m - k)) := by ring
    _ = b ^ (m - k) * a ^ (k + (m - k)) := by rw [pow_add]
    _ = b ^ (m - k) * a ^ m := by rw [Nat.add_sub_of_le hkm]

theorem uniformMoment_scale_left {a b : ℝ} (ha : a ≠ 0) (m : ℕ) :
    uniformMoment a b m = a ^ m * uniformMoment 1 (b / a) m := by
  unfold uniformMoment
  rw [diagonal_scale_left ha]
  ring

/-- Homogeneity of the uniform Hankel determinant. -/
theorem uniformDet_scale_left {a b : ℝ} (ha : a ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    uniformDet a b n = a ^ (2 * n) * uniformDet 1 (b / a) n := by
  unfold uniformDet
  rw [uniformMoment_scale_left ha, uniformMoment_scale_left ha,
    uniformMoment_scale_left ha]
  have hsum : (n - 1) + (n + 1) = 2 * n := by omega
  have hp : a ^ (n - 1) * a ^ (n + 1) = a ^ (2 * n) := by
    rw [← pow_add, hsum]
  have hsquare : (a ^ n) ^ 2 = a ^ (2 * n) := by
    rw [← pow_mul]
    congr 1
    omega
  calc
    a ^ (n - 1) * uniformMoment 1 (b / a) (n - 1) *
          (a ^ (n + 1) * uniformMoment 1 (b / a) (n + 1)) -
        (a ^ n * uniformMoment 1 (b / a) n) ^ 2 =
      (a ^ (n - 1) * a ^ (n + 1)) *
          (uniformMoment 1 (b / a) (n - 1) * uniformMoment 1 (b / a) (n + 1)) -
        (a ^ n) ^ 2 * uniformMoment 1 (b / a) n ^ 2 := by ring
    _ = a ^ (2 * n) * uniformDet 1 (b / a) n := by
      rw [hp, hsquare]
      unfold uniformDet
      ring

theorem uniformDet_comm (a b : ℝ) (n : ℕ) :
    uniformDet a b n = uniformDet b a n := by
  simp only [uniformDet, uniformMoment_comm]

theorem diagonal_zero_zero_pos {m : ℕ} (hm : 1 ≤ m) :
    diagonal 0 0 m = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show 1 + k = k + 1 by omega, diagonal_succ]
  norm_num

/-- Uniform moments on every nonnegative interval are log-convex.  This is
the scaled form of the exact determinant identity above. -/
theorem uniformDet_nonneg {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    {n : ℕ} (hn : 2 ≤ n) : 0 ≤ uniformDet a b n := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      unfold uniformDet uniformMoment
      rw [diagonal_zero_zero_pos (by omega : 1 ≤ n - 1),
        diagonal_zero_zero_pos (by omega : 1 ≤ n + 1),
        diagonal_zero_zero_pos (by omega : 1 ≤ n)]
      norm_num
    · rw [uniformDet_comm]
      rw [uniformDet_scale_left hb (by omega : 1 ≤ n)]
      apply mul_nonneg
      · rw [show 2 * n = n * 2 by omega, pow_mul]
        positivity
      · have hratio : 0 ≤ (0 : ℝ) / b := by positivity
        rw [uniformDet_eq_closed hn]
        exact uniformDetClosed_nonneg hratio
  · have ha_pos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
    rw [uniformDet_scale_left ha (by omega : 1 ≤ n)]
    apply mul_nonneg
    · rw [show 2 * n = n * 2 by omega, pow_mul]
      positivity
    · have hratio : 0 ≤ b / a := div_nonneg hb0 ha0
      rw [uniformDet_eq_closed hn]
      exact uniformDetClosed_nonneg hratio

/-- The mixed term in the signed uniform-moment determinant. -/
noncomputable def mixedUniformCross (u v : ℝ) (n : ℕ) : ℝ :=
  uniformMoment 1 v (n - 1) * uniformMoment u v (n + 1) +
    uniformMoment 1 v (n + 1) * uniformMoment u v (n - 1) -
    2 * uniformMoment 1 v n * uniformMoment u v n

/-- Once the pointwise estimate for the mixed term and the one-variable
moment bound are available, the signed-moment reduction closes immediately. -/
theorem normalizedComplete_logConvex_of_mixed_and_oneVariableBounds
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) {n : ℕ} (hn : 2 ≤ n)
    (hu1 : u ≠ 1)
    (hmixed0 : 0 ≤ mixedUniformCross u v n)
    (hmixed : mixedUniformCross u v n ≤
      min (v ^ (n - 1)) (crossCoefficient n) * uniformMoment 1 v (n + 1))
    (hone : rootCap v * min (v ^ (n - 1)) (crossCoefficient n) *
      uniformMoment 1 v (n + 1) ≤ uniformDet 1 v n) :
    normalizedComplete u v n ^ 2 ≤
      normalizedComplete u v (n - 1) * normalizedComplete u v (n + 1) := by
  apply normalizedComplete_logConvex_of_uniformMoment_bounds (by omega) hu1
  · simpa [uniformDet] using uniformDet_nonneg hu hv hn
  · have hucap := smallerRoot_le_rootCap hu hv huv hroot
    have hcap0 := rootCap_nonneg hv
    calc
      u * (uniformMoment 1 v (n - 1) * uniformMoment u v (n + 1) +
          uniformMoment 1 v (n + 1) * uniformMoment u v (n - 1) -
          2 * uniformMoment 1 v n * uniformMoment u v n) =
          u * mixedUniformCross u v n := by rfl
      _ ≤ rootCap v * mixedUniformCross u v n :=
        mul_le_mul_of_nonneg_right hucap hmixed0
      _ ≤ rootCap v *
          (min (v ^ (n - 1)) (crossCoefficient n) * uniformMoment 1 v (n + 1)) :=
        mul_le_mul_of_nonneg_left hmixed hcap0
      _ ≤ uniformMoment 1 v (n - 1) * uniformMoment 1 v (n + 1) -
          uniformMoment 1 v n ^ 2 := by
        simpa [uniformDet, mul_assoc] using hone

/-- Conditional closure of the complete-homogeneous inequality on
`0 ≤ v ≤ 4/9`; only the elementary mixed-term estimate remains as an
input. -/
theorem normalizedComplete_logConvex_le_four_ninths
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hv49 : v ≤ 4 / 9)
    (huv : u ≤ v) (hroot : Real.sqrt u + Real.sqrt v ≤ 1)
    {n : ℕ} (hn : 6 ≤ n) (hu1 : u ≠ 1)
    (hmixed0 : 0 ≤ mixedUniformCross u v n)
    (hmixed : mixedUniformCross u v n ≤
      min (v ^ (n - 1)) (crossCoefficient n) * uniformMoment 1 v (n + 1)) :
    normalizedComplete u v n ^ 2 ≤
      normalizedComplete u v (n - 1) * normalizedComplete u v (n + 1) := by
  exact normalizedComplete_logConvex_of_mixed_and_oneVariableBounds
    hu hv huv hroot (by omega) hu1 hmixed0 hmixed
    (oneVariableMomentBound_le_four_ninths hn hv hv49)

/-- Final large-index assembly: the scalar transition tail and the mixed
pointwise estimate are the only remaining inputs. -/
theorem normalizedComplete_logConvex_of_transitionTail
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hv1 : v ≤ 1) (huv : u ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) {n : ℕ} (hn : 6 ≤ n)
    (hu1 : u ≠ 1) (htail : LargeTransitionTail n)
    (hmixed0 : 0 ≤ mixedUniformCross u v n)
    (hmixed : mixedUniformCross u v n ≤
      min (v ^ (n - 1)) (crossCoefficient n) * uniformMoment 1 v (n + 1)) :
    normalizedComplete u v n ^ 2 ≤
      normalizedComplete u v (n - 1) * normalizedComplete u v (n + 1) := by
  exact normalizedComplete_logConvex_of_mixed_and_oneVariableBounds
    hu hv huv hroot (by omega) hu1 hmixed0 hmixed
    (oneVariableMomentBound_of_transitionTail hn htail hv hv1)

end SSP.K3CyclicRealTail
