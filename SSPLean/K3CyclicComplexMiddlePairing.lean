import SSPLean.K3CyclicComplexMiddleTailNumeric

/-! # Binomial pairing identities for the complex-middle tail -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

open scoped BigOperators

/-- The two-base binomial falling-factorial moments. -/
theorem complex_binomial_descFactorial_moment
    (N r : ℕ) (p q : ℂ) :
    (∑ j ∈ Finset.range (N + 1),
      (Nat.choose N j : ℂ) * (Nat.descFactorial j r : ℂ) *
        p ^ j * q ^ (N - j)) =
      (Nat.descFactorial N r : ℂ) * p ^ r * (p + q) ^ (N - r) := by
  have hpoly :
      ((Polynomial.X : Polynomial ℂ) + Polynomial.C q) ^ N =
        ∑ j ∈ Finset.range (N + 1),
          Polynomial.C ((Nat.choose N j : ℂ) * q ^ (N - j)) *
            Polynomial.X ^ j := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    simp
    ring
  have hd := congrArg
    (fun f : Polynomial ℂ => (Polynomial.derivative^[r]) f) hpoly
  rw [Polynomial.iterate_derivative_X_add_pow] at hd
  rw [Polynomial.iterate_derivative_sum] at hd
  simp_rw [Polynomial.iterate_derivative_C_mul,
    Polynomial.iterate_derivative_X_pow_eq_smul] at hd
  have heval := congrArg (Polynomial.evalRingHom p) hd
  simp only [map_sum, map_nsmul, map_mul] at heval
  norm_num at heval
  calc
    (∑ j ∈ Finset.range (N + 1),
        (Nat.choose N j : ℂ) * (Nat.descFactorial j r : ℂ) *
          p ^ j * q ^ (N - j)) =
        p ^ r * (∑ j ∈ Finset.range (N + 1),
          (Nat.choose N j : ℂ) * q ^ (N - j) *
            ((Nat.descFactorial j r : ℂ) * p ^ (j - r))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hrj : r ≤ j
      · have hp : p ^ j = p ^ r * p ^ (j - r) := by
          rw [← pow_add, Nat.add_sub_of_le hrj]
        rw [hp]
        ring
      · have hdesc : Nat.descFactorial j r = 0 :=
          Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hrj)
        simp [hdesc]
    _ = p ^ r * ((Nat.descFactorial N r : ℂ) *
          (p + q) ^ (N - r)) := by rw [← heval]
    _ = (Nat.descFactorial N r : ℂ) * p ^ r *
          (p + q) ^ (N - r) := by ring

/-- The curvature kernel has a closed form on two geometric sequences. -/
lemma kernel_cast_complex (N j : ℕ) :
    (kernel N j : ℂ) =
      ((2 - (N : ℂ) + ((N : ℂ) - 2 * j) ^ 2) / 2) *
        (Nat.choose N j : ℂ) := by
  unfold kernel
  push_cast
  ring

lemma descFactorial_two_cast_complex (j : ℕ) :
    (Nat.descFactorial j 2 : ℂ) = (j : ℂ) * ((j : ℂ) - 1) := by
  rcases j with (_ | _ | j)
  · simp [Nat.descFactorial_succ]
  · simp [Nat.descFactorial_succ]
  · simp [Nat.descFactorial_succ]
    ring

theorem kernel_geometric_pairing
    (N : ℕ) (p q : ℂ) :
    (∑ j ∈ Finset.range (N + 1),
      (kernel N j : ℂ) * p ^ j * q ^ (N - j)) =
      (p + q) ^ N +
        ((N : ℂ) * ((N : ℂ) - 1) / 2) *
          (p - q) ^ 2 * (p + q) ^ (N - 2) := by
  have hpoint (j : ℕ) :
      (kernel N j : ℂ) * p ^ j * q ^ (N - j) =
        ((2 - (N : ℂ) + (N : ℂ) ^ 2) / 2) *
            ((Nat.choose N j : ℂ) * (Nat.descFactorial j 0 : ℂ) *
              p ^ j * q ^ (N - j)) +
          (2 - 2 * (N : ℂ)) *
            ((Nat.choose N j : ℂ) * (Nat.descFactorial j 1 : ℂ) *
              p ^ j * q ^ (N - j)) +
          2 * ((Nat.choose N j : ℂ) * (Nat.descFactorial j 2 : ℂ) *
              p ^ j * q ^ (N - j)) := by
    rw [kernel_cast_complex, descFactorial_two_cast_complex]
    simp [Nat.descFactorial_succ]
    ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [complex_binomial_descFactorial_moment N 0,
    complex_binomial_descFactorial_moment N 1,
    complex_binomial_descFactorial_moment N 2]
  rcases N with (_ | _ | N)
  · norm_num
  · norm_num
  · simp [Nat.descFactorial_succ]
    ring

noncomputable def geometricPairClosed (N : ℕ) (p q : ℂ) : ℂ :=
  (p + q) ^ N +
    ((N : ℂ) * ((N : ℂ) - 1) / 2) *
      (p - q) ^ 2 * (p + q) ^ (N - 2)

noncomputable def geometricPairSum
    (N : ℕ) (a p b q : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1),
    (kernel N j : ℂ) * (a * p ^ j) * (b * q ^ (N - j))

theorem geometricPairSum_eq
    (N : ℕ) (a p b q : ℂ) :
    geometricPairSum N a p b q =
      a * b * geometricPairClosed N p q := by
  unfold geometricPairSum geometricPairClosed
  calc
    (∑ j ∈ Finset.range (N + 1),
        (kernel N j : ℂ) * (a * p ^ j) * (b * q ^ (N - j))) =
        a * b * (∑ j ∈ Finset.range (N + 1),
          (kernel N j : ℂ) * p ^ j * q ^ (N - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [kernel_geometric_pairing]

/-- Bilinear expansion of a constant and a conjugate geometric pair. -/
theorem three_geometric_pairing
    (N : ℕ) (a u v p q : ℂ) :
    (∑ j ∈ Finset.range (N + 1),
      (kernel N j : ℂ) *
        (a + u * p ^ j + v * q ^ j) *
        (a + u * p ^ (N - j) + v * q ^ (N - j))) =
      a * a * geometricPairClosed N 1 1 +
      a * u * geometricPairClosed N 1 p +
      a * v * geometricPairClosed N 1 q +
      u * a * geometricPairClosed N p 1 +
      u * u * geometricPairClosed N p p +
      u * v * geometricPairClosed N p q +
      v * a * geometricPairClosed N q 1 +
      v * u * geometricPairClosed N q p +
      v * v * geometricPairClosed N q q := by
  have hexpand :
      (∑ j ∈ Finset.range (N + 1),
        (kernel N j : ℂ) *
          (a + u * p ^ j + v * q ^ j) *
          (a + u * p ^ (N - j) + v * q ^ (N - j))) =
        geometricPairSum N a 1 a 1 +
        geometricPairSum N a 1 u p +
        geometricPairSum N a 1 v q +
        geometricPairSum N u p a 1 +
        geometricPairSum N u p u p +
        geometricPairSum N u p v q +
        geometricPairSum N v q a 1 +
        geometricPairSum N v q u p +
        geometricPairSum N v q v q := by
    unfold geometricPairSum
    simp only [one_pow]
    repeat' rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hexpand]
  repeat' rw [geometricPairSum_eq]

@[simp] theorem geometricPairClosed_one_one (N : ℕ) :
    geometricPairClosed N 1 1 = (2 : ℂ) ^ N := by
  norm_num [geometricPairClosed]

@[simp] theorem geometricPairClosed_self (N : ℕ) (p : ℂ) :
    geometricPairClosed N p p = (2 * p) ^ N := by
  simp [geometricPairClosed]
  ring

theorem geometricPairClosed_comm (N : ℕ) (p q : ℂ) :
    geometricPairClosed N p q = geometricPairClosed N q p := by
  unfold geometricPairClosed
  ring

@[simp] theorem geometricPairClosed_opposite
    {N : ℕ} (hN : 3 ≤ N) (p : ℂ) :
    geometricPairClosed N p (-p) = 0 := by
  have hN0 : N ≠ 0 := by omega
  have hN2 : N - 2 ≠ 0 := by omega
  simp [geometricPairClosed, hN0, hN2]

/-- For three bases `1,p,-p`, the two opposite-frequency cross terms vanish. -/
theorem three_geometric_opposite_pairing
    {N : ℕ} (hN : 3 ≤ N) (a u v p : ℂ) :
    (∑ j ∈ Finset.range (N + 1),
      (kernel N j : ℂ) *
        (a + u * p ^ j + v * (-p) ^ j) *
        (a + u * p ^ (N - j) + v * (-p) ^ (N - j))) =
      a ^ 2 * (2 : ℂ) ^ N +
      u ^ 2 * (2 * p) ^ N +
      v ^ 2 * (-2 * p) ^ N +
      2 * a * u * geometricPairClosed N 1 p +
      2 * a * v * geometricPairClosed N 1 (-p) := by
  rw [three_geometric_pairing]
  rw [geometricPairClosed_one_one, geometricPairClosed_self,
    geometricPairClosed_self,
    geometricPairClosed_opposite hN,
    geometricPairClosed_comm N (-p) p,
    geometricPairClosed_opposite hN,
    geometricPairClosed_comm N p 1,
    geometricPairClosed_comm N (-p) 1]
  ring

end SSP.K3CyclicComplex.MiddleCoeff
