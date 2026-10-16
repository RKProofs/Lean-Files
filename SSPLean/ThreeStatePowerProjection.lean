import SSPLean.MatrixMomentReduction

/-! # Positivity of the leading real-root matrix polynomial

For a nonnegative matrix with cubic annihilator `X(X-a)(X-b)`, where
`0 ≤ a ≤ b`, nonnegativity of every power forces `M²-aM ≥ 0` entrywise.
The argument also covers the repeated-root case `a=b`.
-/

set_option autoImplicit false
open Matrix

namespace SSP.ThreeState

def geometricCoeff (a b : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => a^(n+1)+b*geometricCoeff a b n

theorem geometricCoeff_lower {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    (n+1 : ℝ)*a^n ≤ geometricCoeff a b n := by
  induction n with
  | zero => simp [geometricCoeff]
  | succ n ih =>
    have hb : 0 ≤ b := ha.trans hab
    have hp : 0 ≤ geometricCoeff a b n := (by positivity : 0 ≤ (n+1 : ℝ)*a^n).trans ih
    have hmul := mul_le_mul_of_nonneg_left ih hb
    have hba := mul_le_mul_of_nonneg_right hab ((by positivity : 0 ≤ (n+1 : ℝ)*a^n))
    simp only [geometricCoeff,pow_succ,Nat.cast_add,Nat.cast_one]
    nlinarith

theorem power_decomposition {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (a b : ℝ)
    (hcubic : M^3 = (a+b) • M^2-(a*b) • M) (k : ℕ) :
    M^(k+2) = a^(k+1) • M+geometricCoeff a b k • (M^2-a • M) := by
  have hD : (M^2-a • M)*M = b • (M^2-a • M) := by
    rw [Matrix.sub_mul, Matrix.smul_mul, ← pow_succ, hcubic]
    simp only [pow_two,smul_sub,smul_smul]
    module
  induction k with
  | zero => simp [geometricCoeff]
  | succ k ih =>
    rw [show k+1+2 = (k+2)+1 by omega,pow_succ,ih,Matrix.add_mul,Matrix.smul_mul,
      Matrix.smul_mul,hD]
    simp only [geometricCoeff,pow_succ,smul_smul]
    rw [show M*M = M^2 by rw [pow_two]]
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    simp only [pow_zero,Matrix.one_mul,pow_two]
    ring

/-- This is an entrywise Perron-projection sign argument using only powers;
it does not assume a Perron–Frobenius theorem or diagonalizability. -/
theorem realRoot_projection_nonneg {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) {a b : ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (ha : 0 ≤ a) (hab : a ≤ b)
    (hcubic : M^3 = (a+b) • M^2-(a*b) • M) :
    ∀ i j, 0 ≤ (M^2-a • M) i j := by
  intro i j
  by_cases ha0 : a = 0
  · simpa [ha0] using SSP.Survival.pow_nonneg_entry M hM 2 i j
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  let D := (M^2-a • M) i j
  by_contra hD
  have hDneg : D < 0 := lt_of_not_ge hD
  obtain ⟨k,hk⟩ := exists_nat_gt (a*M i j/(-D))
  have hbound : 0 ≤ a*M i j+(k+1 : ℝ)*D := by
    have hpow := SSP.Survival.pow_nonneg_entry M hM (k+2) i j
    rw [power_decomposition M a b hcubic k] at hpow
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at hpow
    have hcoeff := geometricCoeff_lower ha hab k
    have hcomp := mul_le_mul_of_nonpos_right hcoeff hDneg.le
    have h : 0 ≤ a^k*(a*M i j+(k+1 : ℝ)*D) := by
      dsimp [D] at *
      rw [pow_succ] at hpow
      nlinarith
    exact nonneg_of_mul_nonneg_right h (pow_pos ha' k)
  have hlarge : a*M i j < (k : ℝ)*(-D) := (div_lt_iff₀ (neg_pos.mpr hDneg)).mp hk
  nlinarith

end SSP.ThreeState
