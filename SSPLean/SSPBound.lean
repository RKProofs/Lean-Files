import Mathlib

/-!
# The SSP coefficient bound r ≤ 2s (paper Section 3), formalized

This file machine-verifies the finite-dimensional part of the paper's main SSP result:
given the SSP conditions and the order-2 moment conditions, `r ≤ 2s`.

The proof structure mirrors the paper:

* `weighted_cauchy_schwarz` — the paper's Lemma 2 (Kocsis–Németh Lemma 2.9), restated
  in a division-free form that avoids the 0/0 issues of the ratio formulation (review
  finding §3.4) and is exactly what the final argument consumes.
* `entry_le_one_of_substochastic` — the finite content of the paper's Lemma 3.
* `ComponentBound` — the paper's Lemma 5, i.e. `((Ne)ᵢ)² ≤ (2s/(s+1))·(N²e)ᵢ`.
  This is the **assumed input**: in the paper it is derived from the Aldous–Shepp
  least-variable-phase-type theorem (1987) via Lemmas 1 and 4.  Formalizing
  Aldous–Shepp (or finding an elementary finite proof — see review §5-E6) is the
  single missing piece between this development and a fully verified paper.
* `ssp_coefficient_bound` — the paper's Theorem 3 endgame: `ComponentBound` + SSP
  weight conditions + order-2 moment conditions ⟹ `r ≤ 2s`.
  Handles the `r = 0` edge case and derives `r ≥ 0` (both glossed over in the draft).

`N` is an arbitrary function `ℕ → ℕ → ℝ` restricted to indices `< s`; `(Ne)ᵢ` and
`(N²e)ᵢ` are written as explicit finite sums, so no matrix inverses, spectral radii,
or infinite series enter the statements — those live only in the (assumed) proof of
`ComponentBound`.
-/

open Finset

namespace SSP

/-! ## Lemma 2, division-free form -/

/-- **Weighted Cauchy–Schwarz bound** (paper Lemma 2 / Kocsis–Németh 2.9, restated).
If `uᵢ² ≤ K·vᵢ` componentwise, `w ≥ 0`, and `Σw ≤ 1`, then `(Σ wᵢuᵢ)² ≤ K·Σ wᵢvᵢ`.
This avoids the ratio form's division-by-zero issues. -/
theorem weighted_cauchy_schwarz (s : ℕ) (w u v : ℕ → ℝ) (K : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (huv : ∀ i < s, (u i) ^ 2 ≤ K * v i) :
    (∑ i ∈ range s, w i * u i) ^ 2 ≤ K * ∑ i ∈ range s, w i * v i := by
  -- Cauchy–Schwarz with f = √w, g = √w · u
  have key : (∑ i ∈ range s, w i * u i) ^ 2
      ≤ (∑ i ∈ range s, w i) * ∑ i ∈ range s, w i * (u i) ^ 2 := by
    have h := sum_mul_sq_le_sq_mul_sq (range s)
      (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * u i)
    have e1 : ∀ i ∈ range s, Real.sqrt (w i) * (Real.sqrt (w i) * u i) = w i * u i := by
      intro i _
      rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
    have e2 : ∀ i ∈ range s, Real.sqrt (w i) ^ 2 = w i := fun i _ => Real.sq_sqrt (hw i)
    have e3 : ∀ i ∈ range s, (Real.sqrt (w i) * u i) ^ 2 = w i * (u i) ^ 2 := by
      intro i _
      rw [mul_pow, Real.sq_sqrt (hw i)]
    rw [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3] at h
    exact h
  have hsum_nonneg : 0 ≤ ∑ i ∈ range s, w i * (u i) ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  have step1 : (∑ i ∈ range s, w i * u i) ^ 2 ≤ ∑ i ∈ range s, w i * (u i) ^ 2 := by
    calc (∑ i ∈ range s, w i * u i) ^ 2
        ≤ (∑ i ∈ range s, w i) * ∑ i ∈ range s, w i * (u i) ^ 2 := key
      _ ≤ 1 * ∑ i ∈ range s, w i * (u i) ^ 2 :=
          mul_le_mul_of_nonneg_right hw1 hsum_nonneg
      _ = ∑ i ∈ range s, w i * (u i) ^ 2 := one_mul _
  have step2 : ∑ i ∈ range s, w i * (u i) ^ 2 ≤ K * ∑ i ∈ range s, w i * v i := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have h := huv i (mem_range.1 hi)
    calc w i * (u i) ^ 2 ≤ w i * (K * v i) := mul_le_mul_of_nonneg_left h (hw i)
      _ = K * (w i * v i) := by ring
  linarith

/-! ## Lemma 3, finite content -/

/-- Entries of a substochastic matrix are at most 1 (paper Lemma 3). -/
theorem entry_le_one_of_substochastic (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) :
    ∀ i < s, ∀ j < s, Q i j ≤ 1 := by
  intro i hi j hj
  calc Q i j ≤ ∑ j' ∈ range s, Q i j' :=
        single_le_sum (fun k _ => hQ i k) (mem_range.2 hj)
    _ ≤ 1 := hrow i hi

/-! ## The assumed input: the Aldous–Shepp component bound -/

/-- `(Ne)ᵢ` as a finite sum. -/
def rowSum (s : ℕ) (N : ℕ → ℕ → ℝ) (i : ℕ) : ℝ := ∑ j ∈ range s, N i j

/-- `(N²e)ᵢ` as a finite sum. -/
def rowSum2 (s : ℕ) (N : ℕ → ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ range s, ∑ l ∈ range s, N i j * N j l

/-- **The paper's Lemma 5** (component bound): `((Ne)ᵢ)² ≤ (2s/(s+1))·(N²e)ᵢ`.

In the paper this is proved for `N = (I−Q)⁻¹`, `Q` substochastic with `ρ(Q) < 1`,
via the Neumann series (Lemma 4) and the Aldous–Shepp least-variable-phase-type
theorem (Lemma 1).  That derivation is analytic/probabilistic and is **assumed** here;
it is the only unverified input of this development.  An elementary finite proof
(review §5-E6) would make the whole paper machine-checkable end to end. -/
def ComponentBound (s : ℕ) (N : ℕ → ℕ → ℝ) : Prop :=
  ∀ i < s, (rowSum s N i) ^ 2 ≤ (2 * s / (s + 1)) * rowSum2 s N i

/-! ## The main theorem -/

/-- **Paper Theorem 3 (endgame), full-matrix SSP bound.**
Given the SSP weight conditions (`w ≥ 0`, `Σw ≤ 1`), the component bound
(Aldous–Shepp input), and the order-2 moment conditions
`wᵀNe = r`, `wᵀN²e = r + r²/2`, we get `r ≤ 2s`.

Compared to the draft, this statement makes explicit: the `r = 0` case, the sign
of `r` (derived, not assumed), and that no structure of `N` beyond `ComponentBound`
is used. -/
theorem ssp_coefficient_bound (s : ℕ) (hs : 0 < s)
    (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (r : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (hCB : ComponentBound s N)
    (hoc1 : ∑ i ∈ range s, w i * rowSum s N i = r)
    (hoc2 : ∑ i ∈ range s, w i * rowSum2 s N i = r + r ^ 2 / 2) :
    r ≤ 2 * s := by
  set K : ℝ := 2 * s / (s + 1) with hK
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have hcs := weighted_cauchy_schwarz s w (rowSum s N) (rowSum2 s N) K hw hw1 hCB
  rw [hoc1, hoc2] at hcs
  -- r² ≤ (2s/(s+1)) (r + r²/2)  ⟹  (s+1) r² ≤ 2s·r + s·r²  ⟹  r² ≤ 2s·r  ⟹  r ≤ 2s
  have hmul : (r ^ 2) * ((s : ℝ) + 1) ≤ (2 * s * (r + r ^ 2 / 2) / (s + 1)) * ((s:ℝ) + 1) := by
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hs1)
    calc r ^ 2 ≤ K * (r + r ^ 2 / 2) := hcs
      _ = 2 * s * (r + r ^ 2 / 2) / (s + 1) := by rw [hK]; ring
  have hclear : (r ^ 2) * ((s : ℝ) + 1) ≤ 2 * s * (r + r ^ 2 / 2) := by
    have : (2 * s * (r + r ^ 2 / 2) / (s + 1)) * ((s:ℝ) + 1) = 2 * s * (r + r ^ 2 / 2) := by
      field_simp
    linarith [hmul, this.le, this.ge]
  -- (s+1)r² ≤ 2sr + sr²  ⟹  r² ≤ 2sr
  have hr2 : r ^ 2 ≤ 2 * (s : ℝ) * r := by nlinarith [hclear]
  -- conclude: r² ≥ 0 forces r ≥ 0; then r ≤ 2s
  by_contra hcon
  rw [not_le] at hcon
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  nlinarith [sq_nonneg r, hr2, hcon, hspos]

end SSP
