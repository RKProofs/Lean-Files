import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Algebraic certificates for the equal-rate four-cycle extension

These are the arithmetic steps in `s4_proof_extension.md`. They do not yet
formalize the power-series identity, the root-of-unity filter, or the analytic
and moment conclusions. In particular this file does not prove the general
four-state conjecture.
-/

set_option autoImplicit false

namespace SSP.FourCycle

/-- Twice the numerator of the degree `N` curvature coefficient for residue `r`.
The coefficient itself is this integer divided by `2 * N!`.
-/
def twiceCoefficientNumerator (r N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (N + 1),
    if j % 4 = r ∧ (N - j) % 4 = r then
      (N.choose j : ℤ) * ((2 * (j : ℤ) - (N : ℤ)) ^ 2 - (N : ℤ) + 6)
    else 0

/-- Every even degree below ten, including the single negative coefficient. -/
theorem lowCoefficientTable :
    (List.range 4).map (fun r =>
      [twiceCoefficientNumerator r 0, twiceCoefficientNumerator r 2,
       twiceCoefficientNumerator r 4, twiceCoefficientNumerator r 6,
       twiceCoefficientNumerator r 8]) =
      [[6, 0, 36, 0, -16], [0, 8, 0, 192, 0],
       [0, 0, 12, 0, 784], [0, 0, 0, 0, 0]] := by
  decide

/-- The positive degree-twelve term used to absorb the degree-eight term. -/
theorem returnCoefficientTwelve : twiceCoefficientNumerator 0 12 = 10176 := by
  decide

/-- Exponential domination of the quadratic term in every even degree at least ten. -/
theorem evenDegreeDomination (n : ℕ) (hn : 5 ≤ n) :
    4 * n * n ≤ 3 * 2 ^ n + 2 * n + 6 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    have haux : 5 * n ≤ n * n := Nat.mul_le_mul_right n hn
    nlinarith

/-- Either sign of the oscillatory filtered term is allowed in the tail.
The analytic note derives this expression by a fourth-root-of-unity filter.
-/
theorem filteredTail_nonneg (n : ℕ) (hn : 5 ≤ n) (sign : ℝ)
    (hsign : sign = 1 ∨ sign = -1) :
    0 ≤ (3 * (2 : ℝ) ^ (2 * n) +
      (6 - (2 * (n : ℝ)) * (2 * (n : ℝ) - 1)) * sign * 2 ^ n) / 4 := by
  have hdom : 4 * (n : ℝ) * n ≤ 3 * (2 : ℝ) ^ n + 2 * n + 6 := by
    exact_mod_cast evenDegreeDomination n hn
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hpoly : 0 ≤ (2 * (n : ℝ)) * (2 * (n : ℝ) - 1) - 6 := by
    nlinarith
  have hinner : 0 ≤ 3 * (2 : ℝ) ^ n +
      (6 - (2 * (n : ℝ)) * (2 * (n : ℝ) - 1)) * sign := by
    rcases hsign with h | h <;> rw [h] <;> nlinarith
  have hprod := mul_nonneg hq hinner
  rw [show 2 * n = n + n by omega, pow_add]
  apply div_nonneg _ (by norm_num)
  nlinarith

/-- Exact decomposition of the low-degree return block into nonnegative terms. -/
theorem lowReturnBlock_identity (y : ℝ) :
    (3 / 4 : ℝ) - y / 5040 + 53 * y ^ 2 / 4989600 =
      53 * (y - 10) ^ 2 / 4989600 + y / 71280 + 37369 / 49896 := by
  ring

theorem lowReturnBlock_nonneg (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ (3 / 4 : ℝ) - y / 5040 + 53 * y ^ 2 / 4989600 := by
  rw [lowReturnBlock_identity]
  positivity

/-- The actual degree-four/eight/twelve polynomial, for every real argument. -/
theorem groupedReturnTerms_nonneg (t : ℝ) :
    0 ≤ (3 / 4 : ℝ) * t ^ 4 - t ^ 8 / 5040 +
      53 * t ^ 12 / 4989600 := by
  have h := mul_nonneg (show 0 ≤ t ^ 4 by positivity)
    (lowReturnBlock_nonneg (t ^ 4) (by positivity))
  nlinarith only [h]

/-- An obstruction to the quartic analogue of the three-state scalar shift.
The polynomial is `det (N + t I)` for the explicit matrix in the note.
-/
theorem shiftedObstructionDet_lower (t : ℝ) (ht : 0 ≤ t) :
    3 ≤ t ^ 4 + 9 * t ^ 3 + 26 * t ^ 2 + 25 * t + 3 := by
  have h2 : 0 ≤ t ^ 2 := sq_nonneg t
  have h3 : 0 ≤ t ^ 3 := pow_nonneg ht _
  have h4 : 0 ≤ t ^ 4 := by positivity
  nlinarith

end SSP.FourCycle
