import Mathlib
import SSPLean.SSPBound

/-!
# The moment-hierarchy route to order-dependent SSP bounds

This file machine-verifies the **reduction theorem** for the proposed moment-hierarchy
program (review §5-E3): a sharpened log-convexity inequality for phase-type moments
implies the sharp order-3 SSP bound `r ≤ s − 1 + √(s² − 1)`.

Background.  For an s-stage implicit SSP RK method at SSP value `r`, the transformed
quantities `h_k := wᵀNᵏ𝟙` are (up to `k!`) the moments of a continuous phase-type
distribution of order `s`, and the order-p "tall-tree" conditions pin them:
`h₁ = r`, `h₂ = r + r²/2`, `h₃ = r + r² + r³/6` (order ≥ 3).

**Conjecture (log-convexity hierarchy).**  For every phase-type distribution of order
`≤ s` with raw moments `m_k`: `m_{k−1} m_{k+1} / m_k² ≥ (s+k)/(s+k−1)`, with equality
iff the distribution is an atom-at-zero mixture of an Erlang(s).  The case `k = 1` is
the Aldous–Shepp least-variable-phase-type theorem; the case `k = 2` is what the
order-3 bound consumes.  Numerical evidence: `python/exp5_logconvexity.py`.

Contents:

* `LogConvexBound` — the k = 2 instance of the conjecture, in the `h_k` variables
  (`m₁ = h₁`, `m₂ = 2h₂`, `m₃ = 6h₃`): `(s+2)/(s+1) · (2h₂)² ≤ h₁ · 6h₃`.
* `order3_poly_bound` — the polynomial reduction: the inequality instantiated at the
  order-3 moment values forces `r² ≤ 2(s−1)(r+1)`, hence `r ≤ s−1+√(s²−1)`.
* `order3_ssp_bound` — assembled statement in the `wᵀNᵏ𝟙` sum form, conditional on
  `LogConvexBound` exactly as `ssp_coefficient_bound` is conditional on
  `ComponentBound`.

Everything here is verified; the conjecture itself is the assumed input (it plays the
role that Aldous–Shepp plays for the `r ≤ 2s` bound).
-/

open Finset

namespace SSP

/-- `(N³e)ᵢ` as a finite sum. -/
def rowSum3 (s : ℕ) (N : ℕ → ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ range s, ∑ l ∈ range s, ∑ m ∈ range s, N i j * N j l * N l m

/-- The `k = 2` instance of the **log-convexity hierarchy conjecture** for the
phase-type distribution attached to `(N, w)`: with raw moments `m₁ = h₁`,
`m₂ = 2h₂`, `m₃ = 6h₃` where `h_k = wᵀNᵏ𝟙`, it reads
`(s+2)/(s+1) · m₂² ≤ m₁ · m₃`.  This file treats it as an input predicate; the
unconditional all-stage theorem is `SSP.MainRevised.hierarchy_k2`, built from the direct
state-return proof without creating an import cycle here. -/
def LogConvexBound (s : ℕ) (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ) : Prop :=
  ((s : ℝ) + 2) / ((s : ℝ) + 1) * (2 * ∑ i ∈ range s, w i * rowSum2 s N i) ^ 2
    ≤ (∑ i ∈ range s, w i * rowSum s N i)
      * (6 * ∑ i ∈ range s, w i * rowSum3 s N i)

/-- **Polynomial reduction.**  If the k = 2 log-convexity inequality holds at the
order-3 moment values `m₁ = r`, `m₂ = r² + 2r`, `m₃ = r³ + 6r² + 6r`, then
`r ≤ s − 1 + √(s² − 1)`. -/
theorem order3_poly_bound (s : ℕ) (hs : 0 < s) (r : ℝ) (hr : 0 ≤ r)
    (h : ((s : ℝ) + 2) / ((s : ℝ) + 1) * (r ^ 2 + 2 * r) ^ 2
        ≤ r * (r ^ 3 + 6 * r ^ 2 + 6 * r)) :
    r ≤ (s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1) := by
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hsq_nonneg : (0 : ℝ) ≤ (s : ℝ) ^ 2 - 1 := by nlinarith
  have hsqrt : 0 ≤ Real.sqrt ((s : ℝ) ^ 2 - 1) := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · -- r = 0: the bound is nonnegative
    rw [← hr0]; linarith
  -- clear the denominator: (s+2)(r²+2r)² ≤ (s+1)·r·(r³+6r²+6r)
  have hs1pos : (0 : ℝ) < (s : ℝ) + 1 := by linarith
  have hcleared : ((s : ℝ) + 2) * (r ^ 2 + 2 * r) ^ 2
      ≤ ((s : ℝ) + 1) * (r * (r ^ 3 + 6 * r ^ 2 + 6 * r)) := by
    have := mul_le_mul_of_nonneg_left h (le_of_lt hs1pos)
    calc ((s : ℝ) + 2) * (r ^ 2 + 2 * r) ^ 2
        = ((s : ℝ) + 1) * (((s : ℝ) + 2) / ((s : ℝ) + 1)
            * (r ^ 2 + 2 * r) ^ 2) := by field_simp
      _ ≤ ((s : ℝ) + 1) * (r * (r ^ 3 + 6 * r ^ 2 + 6 * r)) := this
  -- expand: r²·(r² − 2(s−1)r − 2(s−1)) ≤ 0, and divide by r² > 0
  have hkey : r ^ 2 * (r ^ 2 - 2 * ((s : ℝ) - 1) * r - 2 * ((s : ℝ) - 1)) ≤ 0 := by
    nlinarith [hcleared]
  have hr2pos : (0 : ℝ) < r ^ 2 := by positivity
  have hquad : r ^ 2 - 2 * ((s : ℝ) - 1) * r - 2 * ((s : ℝ) - 1) ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [mul_pos hr2pos hcon]
  -- complete the square: (r − (s−1))² ≤ s² − 1
  have hsq : (r - ((s : ℝ) - 1)) ^ 2 ≤ (s : ℝ) ^ 2 - 1 := by nlinarith
  have habs : |r - ((s : ℝ) - 1)| ≤ Real.sqrt ((s : ℝ) ^ 2 - 1) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  have := abs_le.1 habs
  linarith [this.2]

/-- **Conditional sharp order-3 SSP bound.**  Given the SSP weight conditions, the
order-3 tall-tree moment conditions
`wᵀN𝟙 = r`, `wᵀN²𝟙 = r + r²/2`, `wᵀN³𝟙 = r + r² + r³/6`,
and the k = 2 log-convexity bound for `(N, w)`, the SSP value satisfies
`r ≤ s − 1 + √(s² − 1)`.

This is the moment-hierarchy analogue of `ssp_coefficient_bound`: the probabilistic input is
isolated as a hypothesis in this module, and is discharged unconditionally by
`SSP.MainRevised.hierarchy_k2`.
Together with the known methods attaining this value (Ketcheson–Macdonald–Gottlieb),
it would identify the optimal order-3 implicit SSP coefficient exactly. -/
theorem order3_ssp_bound (s : ℕ) (hs : 0 < s)
    (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hLC : LogConvexBound s N w)
    (hoc1 : ∑ i ∈ range s, w i * rowSum s N i = r)
    (hoc2 : ∑ i ∈ range s, w i * rowSum2 s N i = r + r ^ 2 / 2)
    (hoc3 : ∑ i ∈ range s, w i * rowSum3 s N i = r + r ^ 2 + r ^ 3 / 6) :
    r ≤ (s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1) := by
  apply order3_poly_bound s hs r hr
  unfold LogConvexBound at hLC
  rw [hoc1, hoc2, hoc3] at hLC
  calc ((s : ℝ) + 2) / ((s : ℝ) + 1) * (r ^ 2 + 2 * r) ^ 2
      = ((s : ℝ) + 2) / ((s : ℝ) + 1) * (2 * (r + r ^ 2 / 2)) ^ 2 := by ring_nf
    _ ≤ r * (6 * (r + r ^ 2 + r ^ 3 / 6)) := hLC
    _ = r * (r ^ 3 + 6 * r ^ 2 + 6 * r) := by ring

end SSP
