import SSPLean.ThirdMomentBridge

/-!
# The fourth-moment bridge, and the `k = 3` hierarchy predicate

This file extends the `rowSumᵏ`-to-resolvent dictionary of `SSPLean.MomentBridge` and
`SSPLean.ThirdMomentBridge` by one order, and records the `k = 3` instance of the
log-convexity hierarchy in the same `(N, w)` coordinates that `SSP.LogConvexBound`
uses for `k = 2`.

Contents:

* `rowSum4` — the finite-array fourth Neumann power, matching the `rowSum`/`rowSum2`/
  `rowSum3` interface.
* `rowSum4_invMat_eq` — `rowSum4` of the resolvent is `((I-Q)⁻¹)⁴𝟙` entrywise.
* `LogConvexBound3` — the `k = 3` assertion `(s+3)/(s+2) · m₃² ≤ m₂ · m₄` in the
  `h_k` variables (`m₂ = 2h₂`, `m₃ = 6h₃`, `m₄ = 24h₄`).

Everything here is verified; nothing is assumed.
-/

open Finset

namespace SSP

/-- `(N⁴e)ᵢ` as a finite sum. -/
def rowSum4 (s : ℕ) (N : ℕ → ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ range s, ∑ l ∈ range s, ∑ m ∈ range s, ∑ o ∈ range s,
    N i j * N j l * N l m * N m o

/-- The `k = 3` instance of the **log-convexity hierarchy conjecture** for the phase-type
distribution attached to `(N, w)`: with raw moments `m₂ = 2h₂`, `m₃ = 6h₃`, `m₄ = 24h₄`
where `h_k = wᵀNᵏ𝟙`, it reads `(s+3)/(s+2) · m₃² ≤ m₂ · m₄`. -/
def LogConvexBound3 (s : ℕ) (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ) : Prop :=
  ((s : ℝ) + 3) / ((s : ℝ) + 2) * (6 * ∑ i ∈ range s, w i * rowSum3 s N i) ^ 2
    ≤ (2 * ∑ i ∈ range s, w i * rowSum2 s N i)
      * (24 * ∑ i ∈ range s, w i * rowSum4 s N i)

namespace Bridge

/-- `rowSum4` of the resolvent is `((I-Q)⁻¹)⁴𝟙` entrywise. -/
theorem rowSum4_invMat_eq {s : ℕ} (Q : ℕ → ℕ → ℝ) (i : ℕ) (hi : i < s) :
    rowSum4 s (invMat s Q) i
      = ((1 - toMat s Q)⁻¹.mulVec ((1 - toMat s Q)⁻¹.mulVec
          ((1 - toMat s Q)⁻¹.mulVec
            ((1 - toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ)))))) ⟨i, hi⟩ := by
  unfold rowSum4
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => ∑ l ∈ range s, ∑ m ∈ range s, ∑ o ∈ range s,
      invMat s Q i j * invMat s Q j l * invMat s Q l m * invMat s Q m o) s]
  change (∑ j : Fin s, ∑ l ∈ range s, ∑ m ∈ range s, ∑ o ∈ range s,
      invMat s Q i j * invMat s Q j l * invMat s Q l m * invMat s Q m o)
    = ∑ j : Fin s, (1 - toMat s Q)⁻¹ ⟨i, hi⟩ j * _
  refine Finset.sum_congr rfl fun j _ => ?_
  change (∑ l ∈ range s, ∑ m ∈ range s, ∑ o ∈ range s,
      invMat s Q i j * invMat s Q j l * invMat s Q l m * invMat s Q m o)
    = (1 - toMat s Q)⁻¹ ⟨i, hi⟩ j *
      (∑ l : Fin s, (1 - toMat s Q)⁻¹ j l *
        (∑ m : Fin s, (1 - toMat s Q)⁻¹ l m *
          (∑ o : Fin s, (1 - toMat s Q)⁻¹ m o * 1)))
  rw [← Fin.sum_univ_eq_sum_range
    (fun l => ∑ m ∈ range s, ∑ o ∈ range s,
      invMat s Q i j * invMat s Q j l * invMat s Q l m * invMat s Q m o) s]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  change (∑ m ∈ range s, ∑ o ∈ range s,
      invMat s Q i j * invMat s Q j l * invMat s Q l m * invMat s Q m o)
    = (1 - toMat s Q)⁻¹ ⟨i, hi⟩ j *
      ((1 - toMat s Q)⁻¹ j l *
        (∑ m : Fin s, (1 - toMat s Q)⁻¹ l m *
          (∑ o : Fin s, (1 - toMat s Q)⁻¹ m o * 1)))
  rw [← Fin.sum_univ_eq_sum_range
    (fun m => ∑ o ∈ range s,
      invMat s Q i j * invMat s Q j l * invMat s Q l m * invMat s Q m o) s]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  change (∑ o ∈ range s,
      invMat s Q i j * invMat s Q j l * invMat s Q l m * invMat s Q m o)
    = (1 - toMat s Q)⁻¹ ⟨i, hi⟩ j *
      ((1 - toMat s Q)⁻¹ j l *
        ((1 - toMat s Q)⁻¹ l m *
          (∑ o : Fin s, (1 - toMat s Q)⁻¹ m o * 1)))
  rw [← Fin.sum_univ_eq_sum_range
    (fun o => invMat s Q i j * invMat s Q j l * invMat s Q l m * invMat s Q m o) s]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  simp only [invMat,
    dif_pos (⟨hi, j.isLt⟩ : i < s ∧ (j : ℕ) < s),
    dif_pos (⟨j.isLt, l.isLt⟩ : (j : ℕ) < s ∧ (l : ℕ) < s),
    dif_pos (⟨l.isLt, m.isLt⟩ : (l : ℕ) < s ∧ (m : ℕ) < s),
    dif_pos (⟨m.isLt, o.isLt⟩ : (m : ℕ) < s ∧ (o : ℕ) < s), mul_one]
  ring

end Bridge

end SSP
