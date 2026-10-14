import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# The real-spectrum tail in the three-state cyclic case

This file begins the formalization of the normalized complete-homogeneous
log-convexity argument used for the real-spectrum first-start tail.  It is
deliberately independent of the computationally expensive `K3AllStages`
modules.

For nonnegative `u` and `v` satisfying

    sqrt u + sqrt v ≤ 1,

the target sequence is

    q n = h_n(1, u, v) / (n + 1).

The file records its definition, the first nontrivial log-convexity case, and
the algebraic signed-moment determinant identity used in the general proof.
-/

namespace SSP.K3CyclicRealTail

open scoped BigOperators

/-- The degree-`n` two-variable complete homogeneous polynomial. -/
noncomputable def diagonal (u v : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), u ^ i * v ^ (n - i)

/-- The complete homogeneous polynomial `h_n(1, u, v)`.  The outer index is
the total degree in `u` and `v`; the missing degree is the exponent of `1`. -/
noncomputable def complete3 (u v : ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), diagonal u v m

/-- The normalization occurring in the three-state real-spectrum tail. -/
noncomputable def normalizedComplete (u v : ℝ) (n : ℕ) : ℝ :=
  complete3 u v n / (n + 1 : ℝ)

@[simp] theorem diagonal_zero (u v : ℝ) : diagonal u v 0 = 1 := by
  simp [diagonal]

/-- Adding the next diagonal exposes its `v` endpoint and shifts the
remaining diagonal by multiplication with `u`. -/
theorem diagonal_succ (u v : ℝ) (n : ℕ) :
    diagonal u v (n + 1) = v ^ (n + 1) + u * diagonal u v n := by
  rw [diagonal, Finset.sum_range_succ']
  simp only [Nat.sub_zero, pow_zero, one_mul]
  have hsum :
      (∑ i ∈ Finset.range (n + 1), u ^ (i + 1) * v ^ (n + 1 - (i + 1))) =
        u * diagonal u v n := by
    rw [diagonal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n + 1 := Finset.mem_range.mp hi
    have hsub : n + 1 - (i + 1) = n - i := by omega
    rw [hsub, pow_succ]
    ring
  rw [hsum]
  ring

/-- Successive complete polynomials differ by one diagonal. -/
theorem complete3_succ (u v : ℝ) (n : ℕ) :
    complete3 u v (n + 1) = complete3 u v n + diagonal u v (n + 1) := by
  simp [complete3, Finset.sum_range_succ]

/-- The finite telescoping identity behind the signed-uniform-moment
representation. -/
theorem complete3_signed_diagonal (u v : ℝ) (n : ℕ) :
    (1 - u) * complete3 u v n = diagonal 1 v n - u * diagonal u v n := by
  induction n with
  | zero =>
      simp [complete3]
  | succ n ih =>
      rw [complete3_succ, mul_add, ih, diagonal_succ, diagonal_succ]
      ring

/-- The `n`th moment of the uniform distribution on an interval, in its
division-free finite-geometric-sum form before normalization. -/
noncomputable def uniformMoment (a b : ℝ) (n : ℕ) : ℝ :=
  diagonal a b n / (n + 1 : ℝ)

@[simp] theorem uniformMoment_zero (a b : ℝ) : uniformMoment a b 0 = 1 := by
  norm_num [uniformMoment]

theorem uniformMoment_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    0 ≤ uniformMoment a b n := by
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (pow_nonneg ha i) (pow_nonneg hb (n - i))
  · positivity

theorem diagonal_comm (a b : ℝ) (n : ℕ) : diagonal a b n = diagonal b a n := by
  simpa [diagonal] using (Commute.all a b).geom_sum₂_comm (n + 1)

theorem uniformMoment_comm (a b : ℝ) (n : ℕ) :
    uniformMoment a b n = uniformMoment b a n := by
  rw [uniformMoment, uniformMoment, diagonal_comm]

/-- Away from coincident endpoints, the algebraic uniform moment is the usual
divided difference of the power function. -/
theorem uniformMoment_eq_dividedDifference {a b : ℝ} (hab : a ≠ b) (n : ℕ) :
    uniformMoment a b n =
      ((a ^ (n + 1) - b ^ (n + 1)) / (a - b)) / (n + 1 : ℝ) := by
  have hdiag : diagonal a b n =
      (a ^ (n + 1) - b ^ (n + 1)) / (a - b) := by
    simpa [diagonal] using geom₂_sum hab (n + 1)
  rw [uniformMoment, hdiag]

/-- Analytic interpretation of the algebraic moment when the endpoints are
distinct. -/
theorem uniformMoment_eq_intervalIntegral_div {a b : ℝ} (hab : a ≠ b) (n : ℕ) :
    uniformMoment a b n = (∫ x in a..b, x ^ n) / (b - a) := by
  rw [uniformMoment_eq_dividedDifference hab n, integral_pow]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hab' : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hba' : a - b ≠ 0 := sub_ne_zero.mpr hab
  field_simp [hn, hab', hba']
  ring

/-- At coincident endpoints the uniform moment has its continuous limiting
value. -/
@[simp] theorem uniformMoment_self (a : ℝ) (n : ℕ) : uniformMoment a a n = a ^ n := by
  have hdiag : diagonal a a n = (n + 1 : ℝ) * a ^ n := by
    simpa [diagonal] using geom_sum₂_self a (n + 1)
  rw [uniformMoment, hdiag]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hn]

/-- The adjacent Hankel determinant of the uniform-moment sequence. -/
noncomputable def uniformDet (a b : ℝ) (n : ℕ) : ℝ :=
  uniformMoment a b (n - 1) * uniformMoment a b (n + 1) -
    uniformMoment a b n ^ 2

theorem uniformDet_one_factor (a b : ℝ) :
    uniformDet a b 1 = (a - b) ^ 2 / 12 := by
  norm_num [uniformDet, uniformMoment, diagonal, Finset.sum_range_succ]
  ring

theorem uniformDet_two_factor (a b : ℝ) :
    uniformDet a b 2 =
      (a - b) ^ 2 * (a ^ 2 + 4 * a * b + b ^ 2) / 72 := by
  norm_num [uniformDet, uniformMoment, diagonal, Finset.sum_range_succ]
  ring

theorem uniformDet_three_factor (a b : ℝ) :
    uniformDet a b 3 =
      (a - b) ^ 2 *
        (a ^ 4 + 4 * a ^ 3 * b + 10 * a ^ 2 * b ^ 2 +
          4 * a * b ^ 3 + b ^ 4) / 240 := by
  norm_num [uniformDet, uniformMoment, diagonal, Finset.sum_range_succ]
  ring

theorem uniformDet_four_factor (a b : ℝ) :
    uniformDet a b 4 =
      (a - b) ^ 2 * (a ^ 2 + 3 * a * b + b ^ 2) *
        (a ^ 4 + a ^ 3 * b + 6 * a ^ 2 * b ^ 2 +
          a * b ^ 3 + b ^ 4) / 600 := by
  norm_num [uniformDet, uniformMoment, diagonal, Finset.sum_range_succ]
  ring

theorem uniformDet_five_factor (a b : ℝ) :
    uniformDet a b 5 =
      (a - b) ^ 2 *
        (a ^ 8 + 4 * a ^ 7 * b + 10 * a ^ 6 * b ^ 2 +
          20 * a ^ 5 * b ^ 3 + 35 * a ^ 4 * b ^ 4 +
          20 * a ^ 3 * b ^ 5 + 10 * a ^ 2 * b ^ 6 +
          4 * a * b ^ 7 + b ^ 8) / 1260 := by
  norm_num [uniformDet, uniformMoment, diagonal, Finset.sum_range_succ]
  ring

/-- The low-`b` half of the exceptional `n = 2` one-variable certificate.
This elementary proof uses monotonicity of even powers on `[0, 1/2]`; it is
considerably smaller than importing the full Bernstein coefficient table. -/
theorem uniformDet_two_low_bound {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) :
    b ^ 2 * (4 / 27 : ℝ) * uniformMoment 1 (b ^ 2) 3 ≤
      uniformDet 1 (b ^ 2) 2 := by
  have hb2 : b ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg b]
  have hb4 : b ^ 4 ≤ b ^ 2 / 4 := by
    nlinarith [mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hb2)]
  have hb6 : b ^ 6 ≤ b ^ 4 / 4 := by
    nlinarith [mul_nonneg (sq_nonneg (b ^ 2)) (sub_nonneg.mpr hb2)]
  have hb8 : b ^ 8 ≤ b ^ 6 / 4 := by
    nlinarith [mul_nonneg (sq_nonneg (b ^ 3)) (sub_nonneg.mpr hb2)]
  rw [uniformDet_two_factor]
  norm_num [uniformMoment, diagonal, Finset.sum_range_succ]
  nlinarith

/-- The high-`b` half of the exceptional `n = 2` one-variable certificate. -/
theorem uniformDet_two_high_bound {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hbhalf : 1 / 2 ≤ b) :
    (1 - b) ^ 2 * (4 / 27 : ℝ) * uniformMoment 1 (b ^ 2) 3 ≤
      uniformDet 1 (b ^ 2) 2 := by
  let Q := 5 * b ^ 6 - 6 * b ^ 5 - 7 * b ^ 4 - 24 * b ^ 3 -
    7 * b ^ 2 - 6 * b + 5
  let R := 160 * b ^ 5 - 112 * b ^ 4 - 280 * b ^ 3 -
    908 * b ^ 2 - 678 * b - 531
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg b, mul_nonneg hb0 (sub_nonneg.mpr hb1)]
  have hb5 : b ^ 5 ≤ b ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg hb0 3) (sub_nonneg.mpr hb2)]
  have hR : R ≤ 0 := by
    dsimp [R]
    nlinarith [pow_nonneg hb0 2, pow_nonneg hb0 3, pow_nonneg hb0 4]
  have htwo : 0 ≤ 2 * b - 1 := by linarith
  have hprod : (2 * b - 1) * R ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htwo hR
  have hQ : Q ≤ 0 := by
    have hfactor : Q - (-211 / 64 : ℝ) = (2 * b - 1) * R / 64 := by
      dsimp [Q, R]
      ring
    nlinarith
  have hdiff :
      uniformDet 1 (b ^ 2) 2 -
          (1 - b) ^ 2 * (4 / 27 : ℝ) * uniformMoment 1 (b ^ 2) 3 =
        -(b - 1) ^ 2 * Q / 216 := by
    rw [uniformDet_two_factor]
    norm_num [uniformMoment, diagonal, Finset.sum_range_succ]
    dsimp [Q]
    ring
  rw [← sub_nonneg, hdiff]
  have hmul : (b - 1) ^ 2 * Q ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (b - 1)) hQ
  have hnum : 0 ≤ -(b - 1) ^ 2 * Q := by nlinarith
  exact div_nonneg hnum (by norm_num)

/-- The complete `n = 2` exceptional certificate, with its two branches
recombined using `min`. -/
theorem uniformDet_two_min_bound {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    min (b ^ 2) ((1 - b) ^ 2) * (4 / 27 : ℝ) *
        uniformMoment 1 (b ^ 2) 3 ≤ uniformDet 1 (b ^ 2) 2 := by
  rcases le_total b (1 / 2) with hbhalf | hbhalf
  · rw [min_eq_left]
    · exact uniformDet_two_low_bound hb0 hbhalf
    · nlinarith [sq_nonneg b, sq_nonneg (1 - b)]
  · rw [min_eq_right]
    · exact uniformDet_two_high_bound hb0 hb1 hbhalf
    · nlinarith [sq_nonneg b, sq_nonneg (1 - b)]

/-- The same `n = 2` certificate in the root variable `v` used by the
one-variable moment reduction. -/
theorem uniformDet_two_rootCap_bound {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    min v ((1 - Real.sqrt v) ^ 2) * (4 / 27 : ℝ) * uniformMoment 1 v 3 ≤
      uniformDet 1 v 2 := by
  have hs0 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  have hs1 : Real.sqrt v ≤ 1 := by nlinarith [Real.sq_sqrt hv0]
  simpa [Real.sq_sqrt hv0] using uniformDet_two_min_bound hs0 hs1

/-- For the finite exceptional range in the manuscript, uniform moments have
the required nonnegative Hankel determinant. -/
theorem uniformDet_nonneg_of_one_le_of_le_five {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {n : ℕ} (hn : 1 ≤ n) (hn5 : n ≤ 5) : 0 ≤ uniformDet a b n := by
  interval_cases n <;>
    simp only [uniformDet_one_factor, uniformDet_two_factor,
      uniformDet_three_factor, uniformDet_four_factor, uniformDet_five_factor] <;>
    positivity

/-- The exact partial-fraction identity

`q_n = (A_n - u B_n) / (1-u)`,

where `A_n` and `B_n` are uniform moments on `[v,1]` and `[u,v]`.
The formula is algebraic and does not require an ordering of the endpoints. -/
theorem normalizedComplete_eq_signedUniformMoment
    (u v : ℝ) (n : ℕ) (hu1 : u ≠ 1) :
    normalizedComplete u v n =
      (uniformMoment 1 v n - u * uniformMoment u v n) / (1 - u) := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hden : 1 - u ≠ 0 := sub_ne_zero.mpr hu1.symm
  unfold normalizedComplete uniformMoment
  field_simp [hn, hden]
  simpa [mul_comm] using complete3_signed_diagonal u v n

@[simp] theorem complete3_zero (u v : ℝ) : complete3 u v 0 = 1 := by
  simp [complete3]

@[simp] theorem complete3_one (u v : ℝ) : complete3 u v 1 = 1 + u + v := by
  simp [complete3, diagonal, Finset.sum_range_succ]
  ring

@[simp] theorem complete3_two (u v : ℝ) :
    complete3 u v 2 = 1 + u + v + u ^ 2 + u * v + v ^ 2 := by
  simp [complete3, diagonal, Finset.sum_range_succ]
  ring

@[simp] theorem normalizedComplete_zero (u v : ℝ) :
    normalizedComplete u v 0 = 1 := by
  simp [normalizedComplete]

@[simp] theorem normalizedComplete_one (u v : ℝ) :
    normalizedComplete u v 1 = (1 + u + v) / 2 := by
  norm_num [normalizedComplete]

@[simp] theorem normalizedComplete_two (u v : ℝ) :
    normalizedComplete u v 2 =
      (1 + u + v + u ^ 2 + u * v + v ^ 2) / 3 := by
  norm_num [normalizedComplete]

/-- The square-root simplex condition is exactly strong enough to make the
quadratic root discriminant nonnegative. -/
theorem root_discriminant_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) :
    0 ≤ (1 - u - v) ^ 2 - 4 * u * v := by
  let a := Real.sqrt u
  let b := Real.sqrt v
  have ha : 0 ≤ a := Real.sqrt_nonneg u
  have hb : 0 ≤ b := Real.sqrt_nonneg v
  have hab : a + b ≤ 1 := hroot
  have hplus : 0 ≤ 1 - (a + b) ^ 2 := by
    nlinarith
  have hminus : 0 ≤ 1 - (a - b) ^ 2 := by
    nlinarith
  have hprod : 0 ≤ (1 - (a + b) ^ 2) * (1 - (a - b) ^ 2) :=
    mul_nonneg hplus hminus
  have hau : a ^ 2 = u := Real.sq_sqrt hu
  have hbv : b ^ 2 = v := Real.sq_sqrt hv
  nlinarith

/-- A useful consequence of the root simplex: the smaller root is bounded by
the square of the distance of the larger square root from `1`. -/
theorem le_one_sub_sqrt_sq {u v : ℝ} (hu : 0 ≤ u) (_hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) :
    u ≤ (1 - Real.sqrt v) ^ 2 := by
  have hsu : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hsv : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  have hs : Real.sqrt u ≤ 1 - Real.sqrt v := by linarith
  have hright : 0 ≤ 1 - Real.sqrt v := by linarith
  have hau : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hu
  nlinarith

/-- The one-variable reduction uses this combined form of the two bounds on
the ordered smaller root. -/
theorem le_min_root_bounds {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u ≤ v) (hroot : Real.sqrt u + Real.sqrt v ≤ 1) :
    u ≤ min v ((1 - Real.sqrt v) ^ 2) := by
  exact le_min huv (le_one_sub_sqrt_sq hu hv hroot)

/-- The `n = 1` case of normalized complete-homogeneous log-convexity. -/
theorem normalizedComplete_logConvex_one {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) :
    normalizedComplete u v 1 ^ 2 ≤
      normalizedComplete u v 0 * normalizedComplete u v 2 := by
  have hdisc := root_discriminant_nonneg hu hv hroot
  rw [normalizedComplete_zero, normalizedComplete_one, normalizedComplete_two]
  nlinarith

/-- The `n = 2` case, proved by the nonnegative coefficient cone obtained
after writing `u = x²`, `v = y²`, and `1 = (x+y)² + r`. -/
theorem normalizedComplete_logConvex_two {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) :
    normalizedComplete u v 2 ^ 2 ≤
      normalizedComplete u v 1 * normalizedComplete u v 3 := by
  let x := Real.sqrt u
  let y := Real.sqrt v
  let r := 1 - (x + y) ^ 2
  have hx : 0 ≤ x := Real.sqrt_nonneg u
  have hy : 0 ≤ y := Real.sqrt_nonneg v
  have hxy : x + y ≤ 1 := hroot
  have hr : 0 ≤ r := by
    dsimp [r]
    nlinarith
  have hxu : x ^ 2 = u := Real.sq_sqrt hu
  have hyv : y ^ 2 = v := Real.sq_sqrt hv
  let P :=
    r ^ 4 + 6 * r ^ 3 * x ^ 2 + 8 * r ^ 3 * x * y + 6 * r ^ 3 * y ^ 2 +
    6 * r ^ 2 * x ^ 4 + 36 * r ^ 2 * x ^ 3 * y +
    43 * r ^ 2 * x ^ 2 * y ^ 2 + 36 * r ^ 2 * x * y ^ 3 +
    6 * r ^ 2 * y ^ 4 + 24 * r * x ^ 5 * y + 75 * r * x ^ 4 * y ^ 2 +
    108 * r * x ^ 3 * y ^ 3 + 75 * r * x ^ 2 * y ^ 4 +
    24 * r * x * y ^ 5 + 18 * x ^ 6 * y ^ 2 + 54 * x ^ 5 * y ^ 3 +
    72 * x ^ 4 * y ^ 4 + 54 * x ^ 3 * y ^ 5 + 18 * x ^ 2 * y ^ 6
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hid :
      9 * complete3 u v 1 * complete3 u v 3 - 8 * complete3 u v 2 ^ 2 = P := by
    rw [← hxu, ← hyv]
    norm_num [complete3, diagonal, Finset.sum_range_succ]
    dsimp [P, r]
    ring
  have hdet : 0 ≤
      9 * complete3 u v 1 * complete3 u v 3 - 8 * complete3 u v 2 ^ 2 := by
    rw [hid]
    exact hP
  unfold normalizedComplete
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- The `n = 3` coefficient-cone certificate.  Grouping by powers of the
slack `r = 1 - (sqrt u + sqrt v)²` keeps the proof small enough for direct
kernel checking. -/
theorem normalizedComplete_logConvex_three {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) :
    normalizedComplete u v 3 ^ 2 ≤
      normalizedComplete u v 2 * normalizedComplete u v 4 := by
  let x := Real.sqrt u
  let y := Real.sqrt v
  let r := 1 - (x + y) ^ 2
  have hx : 0 ≤ x := Real.sqrt_nonneg u
  have hy : 0 ≤ y := Real.sqrt_nonneg v
  have hxy : x + y ≤ 1 := hroot
  have hr : 0 ≤ r := by
    dsimp [r]
    nlinarith
  have hxu : x ^ 2 = u := Real.sq_sqrt hu
  have hyv : y ^ 2 = v := Real.sq_sqrt hv
  let P :=
    r ^ 6 +
    r ^ 5 * (8 * x ^ 2 + 12 * x * y + 8 * y ^ 2) +
    r ^ 4 * (28 * x ^ 4 + 80 * x ^ 3 * y + 114 * x ^ 2 * y ^ 2 +
      80 * x * y ^ 3 + 28 * y ^ 4) +
    r ^ 3 * (40 * x ^ 6 + 224 * x ^ 5 * y + 458 * x ^ 4 * y ^ 2 +
      592 * x ^ 3 * y ^ 3 + 458 * x ^ 2 * y ^ 4 + 224 * x * y ^ 5 +
      40 * y ^ 6) +
    r ^ 2 * (20 * x ^ 8 + 240 * x ^ 7 * y + 796 * x ^ 6 * y ^ 2 +
      1468 * x ^ 5 * y ^ 3 + 1761 * x ^ 4 * y ^ 4 +
      1468 * x ^ 3 * y ^ 5 + 796 * x ^ 2 * y ^ 6 + 240 * x * y ^ 7 +
      20 * y ^ 8) +
    r * (80 * x ^ 9 * y + 500 * x ^ 8 * y ^ 2 + 1392 * x ^ 7 * y ^ 3 +
      2378 * x ^ 6 * y ^ 4 + 2820 * x ^ 5 * y ^ 5 +
      2378 * x ^ 4 * y ^ 6 + 1392 * x ^ 3 * y ^ 7 +
      500 * x ^ 2 * y ^ 8 + 80 * x * y ^ 9) +
    (72 * x ^ 10 * y ^ 2 + 360 * x ^ 9 * y ^ 3 + 921 * x ^ 8 * y ^ 4 +
      1524 * x ^ 7 * y ^ 5 + 1782 * x ^ 6 * y ^ 6 +
      1524 * x ^ 5 * y ^ 7 + 921 * x ^ 4 * y ^ 8 +
      360 * x ^ 3 * y ^ 9 + 72 * x ^ 2 * y ^ 10)
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hid :
      16 * complete3 u v 2 * complete3 u v 4 -
          15 * complete3 u v 3 ^ 2 = P := by
    rw [← hxu, ← hyv]
    norm_num [complete3, diagonal, Finset.sum_range_succ]
    dsimp [P, r]
    ring
  have hdet : 0 ≤
      16 * complete3 u v 2 * complete3 u v 4 -
        15 * complete3 u v 3 ^ 2 := by
    rw [hid]
    exact hP
  unfold normalizedComplete
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

set_option maxHeartbeats 600000 in
/-- The `n = 4` coefficient-cone certificate. -/
theorem normalizedComplete_logConvex_four {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) :
    normalizedComplete u v 4 ^ 2 ≤
      normalizedComplete u v 3 * normalizedComplete u v 5 := by
  let x := Real.sqrt u
  let y := Real.sqrt v
  let r := 1 - (x + y) ^ 2
  have hx : 0 ≤ x := Real.sqrt_nonneg u
  have hy : 0 ≤ y := Real.sqrt_nonneg v
  have hxy : x + y ≤ 1 := hroot
  have hr : 0 ≤ r := by
    dsimp [r]
    nlinarith
  have hxu : x ^ 2 = u := Real.sq_sqrt hu
  have hyv : y ^ 2 = v := Real.sq_sqrt hv
  let P :=
    r ^ 8 +
    r ^ 7 * (10 * x ^ 2 + 16 * x * y + 10 * y ^ 2) +
    r ^ 6 * (45 * x ^ 4 + 140 * x ^ 3 * y + 200 * x ^ 2 * y ^ 2 +
      140 * x * y ^ 3 + 45 * y ^ 4) +
    r ^ 5 * (120 * x ^ 6 + 540 * x ^ 5 * y + 1182 * x ^ 4 * y ^ 2 +
      1504 * x ^ 3 * y ^ 3 + 1182 * x ^ 2 * y ^ 4 + 540 * x * y ^ 5 +
      120 * y ^ 6) +
    r ^ 4 * (185 * x ^ 8 + 1200 * x ^ 7 * y + 3443 * x ^ 6 * y ^ 2 +
      6220 * x ^ 5 * y ^ 3 + 7494 * x ^ 4 * y ^ 4 +
      6220 * x ^ 3 * y ^ 5 + 3443 * x ^ 2 * y ^ 6 + 1200 * x * y ^ 7 +
      185 * y ^ 8) +
    r ^ 3 * (150 * x ^ 10 + 1480 * x ^ 9 * y + 5665 * x ^ 8 * y ^ 2 +
      13144 * x ^ 7 * y ^ 3 + 21093 * x ^ 6 * y ^ 4 +
      24624 * x ^ 5 * y ^ 5 + 21093 * x ^ 4 * y ^ 6 +
      13144 * x ^ 3 * y ^ 7 + 5665 * x ^ 2 * y ^ 8 + 1480 * x * y ^ 9 +
      150 * y ^ 10) +
    r ^ 2 * (50 * x ^ 12 + 900 * x ^ 11 * y + 4905 * x ^ 10 * y ^ 2 +
      14790 * x ^ 9 * y ^ 3 + 30065 * x ^ 8 * y ^ 4 +
      44958 * x ^ 7 * y ^ 5 + 51227 * x ^ 6 * y ^ 6 +
      44958 * x ^ 5 * y ^ 7 + 30065 * x ^ 4 * y ^ 8 +
      14790 * x ^ 3 * y ^ 9 + 4905 * x ^ 2 * y ^ 10 + 900 * x * y ^ 11 +
      50 * y ^ 12) +
    r * (200 * x ^ 13 * y + 1865 * x ^ 12 * y ^ 2 +
      7780 * x ^ 11 * y ^ 3 + 20373 * x ^ 10 * y ^ 4 +
      38148 * x ^ 9 * y ^ 5 + 54467 * x ^ 8 * y ^ 6 +
      61164 * x ^ 7 * y ^ 7 + 54467 * x ^ 6 * y ^ 8 +
      38148 * x ^ 5 * y ^ 9 + 20373 * x ^ 4 * y ^ 10 +
      7780 * x ^ 3 * y ^ 11 + 1865 * x ^ 2 * y ^ 12 + 200 * x * y ^ 13) +
    (190 * x ^ 14 * y ^ 2 + 1330 * x ^ 13 * y ^ 3 +
      4806 * x ^ 12 * y ^ 4 + 11546 * x ^ 11 * y ^ 5 +
      20522 * x ^ 10 * y ^ 6 + 28470 * x ^ 9 * y ^ 7 +
      31656 * x ^ 8 * y ^ 8 + 28470 * x ^ 7 * y ^ 9 +
      20522 * x ^ 6 * y ^ 10 + 11546 * x ^ 5 * y ^ 11 +
      4806 * x ^ 4 * y ^ 12 + 1330 * x ^ 3 * y ^ 13 + 190 * x ^ 2 * y ^ 14)
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hid :
      25 * complete3 u v 3 * complete3 u v 5 -
          24 * complete3 u v 4 ^ 2 = P := by
    rw [← hxu, ← hyv]
    norm_num [complete3, diagonal, Finset.sum_range_succ]
    dsimp [P, r]
    ring
  have hdet : 0 ≤
      25 * complete3 u v 3 * complete3 u v 5 -
        24 * complete3 u v 4 ^ 2 := by
    rw [hid]
    exact hP
  unfold normalizedComplete
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

set_option maxHeartbeats 1200000 in
/-- The `n = 5` coefficient-cone certificate. -/
theorem normalizedComplete_logConvex_five {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hroot : Real.sqrt u + Real.sqrt v ≤ 1) :
    normalizedComplete u v 5 ^ 2 ≤
      normalizedComplete u v 4 * normalizedComplete u v 6 := by
  let x := Real.sqrt u
  let y := Real.sqrt v
  let r := 1 - (x + y) ^ 2
  have hx : 0 ≤ x := Real.sqrt_nonneg u
  have hy : 0 ≤ y := Real.sqrt_nonneg v
  have hxy : x + y ≤ 1 := hroot
  have hr : 0 ≤ r := by
    dsimp [r]
    nlinarith
  have hxu : x ^ 2 = u := Real.sq_sqrt hu
  have hyv : y ^ 2 = v := Real.sq_sqrt hv
  let P :=
    r ^ 10 +
    r ^ 9 * (12 * x ^ 2 + 20 * x * y + 12 * y ^ 2) +
    r ^ 8 * (66 * x ^ 4 + 216 * x ^ 3 * y + 310 * x ^ 2 * y ^ 2 +
      216 * x * y ^ 3 + 66 * y ^ 4) +
    r ^ 7 * (220 * x ^ 6 + 1056 * x ^ 5 * y + 2366 * x ^ 4 * y ^ 2 +
      3040 * x ^ 3 * y ^ 3 + 2366 * x ^ 2 * y ^ 4 + 1056 * x * y ^ 5 +
      220 * y ^ 6) +
    r ^ 6 * (495 * x ^ 8 + 3080 * x ^ 7 * y + 9262 * x ^ 6 * y ^ 2 +
      16996 * x ^ 5 * y ^ 3 + 20673 * x ^ 4 * y ^ 4 +
      16996 * x ^ 3 * y ^ 5 + 9262 * x ^ 2 * y ^ 6 + 3080 * x * y ^ 7 +
      495 * y ^ 8) +
    r ^ 5 * (756 * x ^ 10 + 5940 * x ^ 9 * y + 22074 * x ^ 8 * y ^ 2 +
      52008 * x ^ 7 * y ^ 3 + 84708 * x ^ 6 * y ^ 4 +
      99340 * x ^ 5 * y ^ 5 + 84708 * x ^ 4 * y ^ 6 +
      52008 * x ^ 3 * y ^ 7 + 22074 * x ^ 2 * y ^ 8 + 5940 * x * y ^ 9 +
      756 * y ^ 10) +
    r ^ 4 * (742 * x ^ 12 + 7560 * x ^ 11 * y + 34186 * x ^ 10 * y ^ 2 +
      97540 * x ^ 9 * y ^ 3 + 197077 * x ^ 8 * y ^ 4 +
      296264 * x ^ 7 * y ^ 5 + 338608 * x ^ 6 * y ^ 6 +
      296264 * x ^ 5 * y ^ 7 + 197077 * x ^ 4 * y ^ 8 +
      97540 * x ^ 3 * y ^ 9 + 34186 * x ^ 2 * y ^ 10 +
      7560 * x * y ^ 11 + 742 * y ^ 12) +
    r ^ 3 * (420 * x ^ 14 + 5936 * x ^ 13 * y + 33614 * x ^ 12 * y ^ 2 +
      115088 * x ^ 11 * y ^ 3 + 277546 * x ^ 10 * y ^ 4 +
      505128 * x ^ 9 * y ^ 5 + 716490 * x ^ 8 * y ^ 6 +
      803904 * x ^ 7 * y ^ 7 + 716490 * x ^ 6 * y ^ 8 +
      505128 * x ^ 5 * y ^ 9 + 277546 * x ^ 4 * y ^ 10 +
      115088 * x ^ 3 * y ^ 11 + 33614 * x ^ 2 * y ^ 12 +
      5936 * x * y ^ 13 + 420 * y ^ 14) +
    r ^ 2 * (105 * x ^ 16 + 2520 * x ^ 15 * y + 19112 * x ^ 14 * y ^ 2 +
      80724 * x ^ 13 * y ^ 3 + 232038 * x ^ 12 * y ^ 4 +
      498876 * x ^ 11 * y ^ 5 + 842184 * x ^ 10 * y ^ 6 +
      1144380 * x ^ 9 * y ^ 7 + 1266087 * x ^ 8 * y ^ 8 +
      1144380 * x ^ 7 * y ^ 9 + 842184 * x ^ 6 * y ^ 10 +
      498876 * x ^ 5 * y ^ 11 + 232038 * x ^ 4 * y ^ 12 +
      80724 * x ^ 3 * y ^ 13 + 19112 * x ^ 2 * y ^ 14 +
      2520 * x * y ^ 15 + 105 * y ^ 16) +
    r * (420 * x ^ 17 * y + 5196 * x ^ 16 * y ^ 2 +
      28960 * x ^ 15 * y ^ 3 + 102176 * x ^ 14 * y ^ 4 +
      260888 * x ^ 13 * y ^ 5 + 516868 * x ^ 12 * y ^ 6 +
      825824 * x ^ 11 * y ^ 7 + 1086612 * x ^ 10 * y ^ 8 +
      1189532 * x ^ 9 * y ^ 9 + 1086612 * x ^ 8 * y ^ 10 +
      825824 * x ^ 7 * y ^ 11 + 516868 * x ^ 6 * y ^ 12 +
      260888 * x ^ 5 * y ^ 13 + 102176 * x ^ 4 * y ^ 14 +
      28960 * x ^ 3 * y ^ 15 + 5196 * x ^ 2 * y ^ 16 + 420 * x * y ^ 17) +
    (408 * x ^ 18 * y ^ 2 + 3672 * x ^ 17 * y ^ 3 +
      17104 * x ^ 16 * y ^ 4 + 53600 * x ^ 15 * y ^ 5 +
      126008 * x ^ 14 * y ^ 6 + 235368 * x ^ 13 * y ^ 7 +
      361168 * x ^ 12 * y ^ 8 + 464008 * x ^ 11 * y ^ 9 +
      503920 * x ^ 10 * y ^ 10 + 464008 * x ^ 9 * y ^ 11 +
      361168 * x ^ 8 * y ^ 12 + 235368 * x ^ 7 * y ^ 13 +
      126008 * x ^ 6 * y ^ 14 + 53600 * x ^ 5 * y ^ 15 +
      17104 * x ^ 4 * y ^ 16 + 3672 * x ^ 3 * y ^ 17 + 408 * x ^ 2 * y ^ 18)
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hid :
      36 * complete3 u v 4 * complete3 u v 6 -
          35 * complete3 u v 5 ^ 2 = P := by
    rw [← hxu, ← hyv]
    norm_num [complete3, diagonal, Finset.sum_range_succ]
    dsimp [P, r]
    ring
  have hdet : 0 ≤
      36 * complete3 u v 4 * complete3 u v 6 -
        35 * complete3 u v 5 ^ 2 := by
    rw [hid]
    exact hP
  unfold normalizedComplete
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- The first three indices of normalized complete-homogeneous
log-convexity, now without any unproved certificate hypotheses. -/
theorem normalizedComplete_logConvex_of_le_three {u v : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v) (hroot : Real.sqrt u + Real.sqrt v ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) (hn3 : n ≤ 3) :
    normalizedComplete u v n ^ 2 ≤
      normalizedComplete u v (n - 1) * normalizedComplete u v (n + 1) := by
  interval_cases n
  · simpa using normalizedComplete_logConvex_one hu hv hroot
  · simpa using normalizedComplete_logConvex_two hu hv hroot
  · simpa using normalizedComplete_logConvex_three hu hv hroot

/-- All five finite indices preceding the analytic `n ≥ 6` tail argument. -/
theorem normalizedComplete_logConvex_of_le_five {u v : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v) (hroot : Real.sqrt u + Real.sqrt v ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) (hn5 : n ≤ 5) :
    normalizedComplete u v n ^ 2 ≤
      normalizedComplete u v (n - 1) * normalizedComplete u v (n + 1) := by
  interval_cases n
  · simpa using normalizedComplete_logConvex_one hu hv hroot
  · simpa using normalizedComplete_logConvex_two hu hv hroot
  · simpa using normalizedComplete_logConvex_three hu hv hroot
  · simpa using normalizedComplete_logConvex_four hu hv hroot
  · simpa using normalizedComplete_logConvex_five hu hv hroot

/-- Algebraic expansion behind the signed-uniform-moment determinant. -/
theorem signedMoment_det_decomp
    (u A₀ A₁ A₂ B₀ B₁ B₂ : ℝ) :
    (A₀ - u * B₀) * (A₂ - u * B₂) - (A₁ - u * B₁) ^ 2 =
      (A₀ * A₂ - A₁ ^ 2) + u ^ 2 * (B₀ * B₂ - B₁ ^ 2) -
        u * (A₀ * B₂ + A₂ * B₀ - 2 * A₁ * B₁) := by
  ring

/-- Division by the common signed-moment mass preserves the determinant
identity.  This is the form applied to `q_{n-1}`, `q_n`, and `q_{n+1}`. -/
theorem signedMoment_det_decomp_normalized
    (u A₀ A₁ A₂ B₀ B₁ B₂ : ℝ) (hu : u ≠ 1) :
    (1 - u) ^ 2 *
        (((A₀ - u * B₀) / (1 - u)) * ((A₂ - u * B₂) / (1 - u)) -
          ((A₁ - u * B₁) / (1 - u)) ^ 2) =
      (A₀ * A₂ - A₁ ^ 2) + u ^ 2 * (B₀ * B₂ - B₁ ^ 2) -
        u * (A₀ * B₂ + A₂ * B₀ - 2 * A₁ * B₁) := by
  have hden : 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  field_simp [hden]
  ring

/-- The abstract inequality step in the signed-moment proof.  Nonnegativity
of the `B` determinant and control of the mixed term by the `A` determinant
are precisely the two estimates needed after the algebraic expansion. -/
theorem signedMoment_det_nonneg_of_cross_bound
    {u A₀ A₁ A₂ B₀ B₁ B₂ : ℝ} (hB : 0 ≤ B₀ * B₂ - B₁ ^ 2)
    (hcross :
      u * (A₀ * B₂ + A₂ * B₀ - 2 * A₁ * B₁) ≤ A₀ * A₂ - A₁ ^ 2) :
    0 ≤ (A₀ - u * B₀) * (A₂ - u * B₂) - (A₁ - u * B₁) ^ 2 := by
  rw [signedMoment_det_decomp]
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  have hBterm : 0 ≤ u ^ 2 * (B₀ * B₂ - B₁ ^ 2) := mul_nonneg hu2 hB
  linarith

/-- The preceding abstract inequality after normalization by `1 - u`. -/
theorem signedMoment_normalized_det_nonneg_of_cross_bound
    {u A₀ A₁ A₂ B₀ B₁ B₂ : ℝ} (hu1 : u ≠ 1)
    (hB : 0 ≤ B₀ * B₂ - B₁ ^ 2)
    (hcross :
      u * (A₀ * B₂ + A₂ * B₀ - 2 * A₁ * B₁) ≤ A₀ * A₂ - A₁ ^ 2) :
    0 ≤ ((A₀ - u * B₀) / (1 - u)) * ((A₂ - u * B₂) / (1 - u)) -
      ((A₁ - u * B₁) / (1 - u)) ^ 2 := by
  have hraw := signedMoment_det_nonneg_of_cross_bound hB hcross
  have hscaled := signedMoment_det_decomp_normalized
    u A₀ A₁ A₂ B₀ B₁ B₂ hu1
  have hden : 1 - u ≠ 0 := sub_ne_zero.mpr hu1.symm
  have hden2 : 0 < (1 - u) ^ 2 := sq_pos_of_ne_zero hden
  rw [signedMoment_det_decomp] at hraw
  rw [← hscaled] at hraw
  nlinarith

/-- The signed-moment reduction specialized to the complete-homogeneous
sequence.  Subsequent files only need to supply log-convexity of the inner
uniform moments and the one-variable cross-term estimate. -/
theorem normalizedComplete_logConvex_of_uniformMoment_bounds
    {u v : ℝ} {n : ℕ} (_hn : 1 ≤ n) (hu1 : u ≠ 1)
    (hB :
      0 ≤ uniformMoment u v (n - 1) * uniformMoment u v (n + 1) -
        uniformMoment u v n ^ 2)
    (hcross :
      u *
          (uniformMoment 1 v (n - 1) * uniformMoment u v (n + 1) +
            uniformMoment 1 v (n + 1) * uniformMoment u v (n - 1) -
            2 * uniformMoment 1 v n * uniformMoment u v n) ≤
        uniformMoment 1 v (n - 1) * uniformMoment 1 v (n + 1) -
          uniformMoment 1 v n ^ 2) :
    normalizedComplete u v n ^ 2 ≤
      normalizedComplete u v (n - 1) * normalizedComplete u v (n + 1) := by
  have hdet := signedMoment_normalized_det_nonneg_of_cross_bound
    (u := u)
    (A₀ := uniformMoment 1 v (n - 1))
    (A₁ := uniformMoment 1 v n)
    (A₂ := uniformMoment 1 v (n + 1))
    (B₀ := uniformMoment u v (n - 1))
    (B₁ := uniformMoment u v n)
    (B₂ := uniformMoment u v (n + 1)) hu1 hB hcross
  rw [normalizedComplete_eq_signedUniformMoment u v (n - 1) hu1,
    normalizedComplete_eq_signedUniformMoment u v n hu1,
    normalizedComplete_eq_signedUniformMoment u v (n + 1) hu1]
  linarith

/-- In the exceptional range `1 ≤ n ≤ 5`, the inner uniform determinant is
already discharged by the explicit low-degree factorizations above. -/
theorem normalizedComplete_logConvex_small_of_cross_bound
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) {n : ℕ}
    (hn : 1 ≤ n) (hn5 : n ≤ 5) (hu1 : u ≠ 1)
    (hcross :
      u *
          (uniformMoment 1 v (n - 1) * uniformMoment u v (n + 1) +
            uniformMoment 1 v (n + 1) * uniformMoment u v (n - 1) -
            2 * uniformMoment 1 v n * uniformMoment u v n) ≤
        uniformMoment 1 v (n - 1) * uniformMoment 1 v (n + 1) -
          uniformMoment 1 v n ^ 2) :
    normalizedComplete u v n ^ 2 ≤
      normalizedComplete u v (n - 1) * normalizedComplete u v (n + 1) := by
  apply normalizedComplete_logConvex_of_uniformMoment_bounds hn hu1
  · simpa [uniformDet] using
      uniformDet_nonneg_of_one_le_of_le_five hu hv hn hn5
  · exact hcross

end SSP.K3CyclicRealTail
