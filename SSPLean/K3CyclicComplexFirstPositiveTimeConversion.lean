import SSPLean.K3CyclicComplexFirstBernsteinConversion
import SSPLean.K3CyclicComplexFirstPositiveDegreeBounds

/-! # Exact compact-time Bernstein conversion for the positive-m chart -/

set_option autoImplicit false

open Polynomial
open scoped BigOperators Polynomial

namespace SSP.K3CyclicComplex.PositiveCoeff

open Dense ComplexCoeff

theorem beval_range_foldl_badd (f : ℕ → Bi)
    (acc : Bi) (n : ℕ) (r t : ℝ) :
    beval ((List.range n).foldl (fun p i => badd p (f i)) acc) r t =
      beval acc r t + ∑ i ∈ Finset.range n, beval (f i) r t := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [beval_add, ih, Finset.sum_range_succ]
      ring

theorem beval_timeBernPolyFrom (powers : List Bi) (k : ℕ) (r t : ℝ) :
    beval (timeBernPolyFrom powers k) r t =
      ∑ N ∈ Finset.range (k + 1),
        (((Nat.choose k N : ℚ) / Nat.choose order N : ℚ) : ℝ) *
          beval (powers.getD N bzero) r t := by
  unfold timeBernPolyFrom
  rw [beval_range_foldl_badd]
  simp only [bzero, beval_nil, zero_add]
  apply Finset.sum_congr rfl
  intro N hN
  rw [beval_mul, beval_brat]

theorem real_monomial_bern (n k : ℕ) (hk : k ≤ n) (u : ℝ) :
    u ^ k = ∑ j ∈ Finset.range (n - k + 1),
      (((Nat.choose (k + j) k : ℚ) / Nat.choose n k : ℚ) : ℝ) *
        ((Nat.choose n (k + j) : ℝ) * u ^ (k + j) *
          (1 - u) ^ (n - (k + j))) := by
  have h := congrArg
    (fun p : ℚ[X] => p.eval₂ (algebraMap ℚ ℝ) u)
    (SSP.K3CyclicComplex.monomial_bern n k hk)
  simpa [Polynomial.eval₂_finsetSum, bernsteinPolynomial] using h

def compactTaylorFrom (powers : List Bi) (r t u : ℝ) : ℝ :=
  ∑ N ∈ Finset.range (order + 1),
    beval (powers.getD N bzero) r t * u ^ N

theorem compactTaylorFrom_eq_timeBernstein
    (powers : List Bi) (r t u : ℝ) :
    compactTaylorFrom powers r t u =
      ∑ k ∈ Finset.range (order + 1),
        beval (timeBernPolyFrom powers k) r t *
          ((Nat.choose order k : ℝ) * u ^ k *
            (1 - u) ^ (order - k)) := by
  unfold compactTaylorFrom
  calc
    (∑ N ∈ Finset.range (order + 1),
        beval (powers.getD N bzero) r t * u ^ N) =
        ∑ N ∈ Finset.range (order + 1),
          ∑ j ∈ Finset.range (order - N + 1),
            (beval (powers.getD N bzero) r t *
              (((Nat.choose (N + j) N : ℚ) /
                Nat.choose order N : ℚ) : ℝ)) *
              ((Nat.choose order (N + j) : ℝ) * u ^ (N + j) *
                (1 - u) ^ (order - (N + j))) := by
      apply Finset.sum_congr rfl
      intro N hN
      have hNorder : N ≤ order :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hN)
      rw [real_monomial_bern order N hNorder u, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ k ∈ Finset.range (order + 1),
          ∑ N ∈ Finset.range (k + 1),
            (beval (powers.getD N bzero) r t *
              (((Nat.choose k N : ℚ) / Nat.choose order N : ℚ) : ℝ)) *
              ((Nat.choose order k : ℝ) * u ^ k *
                (1 - u) ^ (order - k)) := by
      exact SSP.K3CyclicComplex.triangle_swap
        (fun N k =>
          (beval (powers.getD N bzero) r t *
            (((Nat.choose k N : ℚ) / Nat.choose order N : ℚ) : ℝ)) *
            ((Nat.choose order k : ℝ) * u ^ k *
              (1 - u) ^ (order - k))) order
    _ = ∑ k ∈ Finset.range (order + 1),
        beval (timeBernPolyFrom powers k) r t *
          ((Nat.choose order k : ℝ) * u ^ k *
            (1 - u) ^ (order - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [beval_timeBernPolyFrom, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro N hN
      ring

end SSP.K3CyclicComplex.PositiveCoeff
