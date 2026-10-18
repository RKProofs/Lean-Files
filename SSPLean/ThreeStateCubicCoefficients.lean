import SSPLean.ThreeStateCanonicalAssembly

set_option autoImplicit false
open Matrix

namespace SSP.ThreeState

def traceCoeff (N : Mat) : ℝ := N 0 0+N 1 1+N 2 2
def pairCoeff (N : Mat) : ℝ :=
  N 0 0*N 1 1+N 0 0*N 2 2+N 1 1*N 2 2-
    N 0 1*N 1 0-N 0 2*N 2 0-N 1 2*N 2 1
def detCoeff (N : Mat) : ℝ :=
  N 0 0*N 1 1*N 2 2+N 0 1*N 1 2*N 2 0+N 0 2*N 1 0*N 2 1-
    N 0 2*N 1 1*N 2 0-N 0 1*N 1 0*N 2 2-N 0 0*N 1 2*N 2 1

set_option maxHeartbeats 1500000 in
theorem matrix_cubic (N : Mat) :
    N^3 = traceCoeff N • N^2-pairCoeff N • N+detCoeff N • (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceCoeff,pairCoeff,detCoeff,pow_succ,Matrix.mul_apply,Fin.sum_univ_three] <;> ring

set_option maxHeartbeats 1500000 in
theorem shifted_matrix_cubic (N : Mat) (t : ℝ) :
    (N+t • (1 : Mat))^3 =
      (traceCoeff N+3*t) • (N+t • (1 : Mat))^2-
        (pairCoeff N+2*traceCoeff N*t+3*t^2) • (N+t • (1 : Mat))+
          (detCoeff N+pairCoeff N*t+traceCoeff N*t^2+t^3) • (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceCoeff,pairCoeff,detCoeff,pow_succ,Matrix.mul_apply,Fin.sum_univ_three,
      Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] <;> ring

set_option maxHeartbeats 1500000 in
theorem pairCoeff_le_diagonal_products (N : Mat) (hN : ∀ i j, 0 ≤ N i j) :
    pairCoeff N ≤ N 0 0*N 1 1+N 0 0*N 2 2+N 1 1*N 2 2 := by
  dsimp [pairCoeff]
  nlinarith [mul_nonneg (hN 0 1) (hN 1 0),mul_nonneg (hN 0 2) (hN 2 0),
    mul_nonneg (hN 1 2) (hN 2 1)]

set_option maxHeartbeats 1500000 in
theorem zeroDiagonal_discriminant_nonneg (N : Mat) (hN : ∀ i j, 0 ≤ N i j)
    (hz : N 0 0 = 0 ∨ N 1 1 = 0 ∨ N 2 2 = 0) :
    0 ≤ (traceCoeff N)^2-4*pairCoeff N := by
  have hp := pairCoeff_le_diagonal_products N hN
  dsimp [traceCoeff]
  rcases hz with h | h | h
  · rw [h] at hp ⊢
    nlinarith [sq_nonneg (N 1 1-N 2 2)]
  · rw [h] at hp ⊢
    nlinarith [sq_nonneg (N 0 0-N 2 2)]
  · rw [h] at hp ⊢
    nlinarith [sq_nonneg (N 0 0-N 1 1)]

set_option maxHeartbeats 1500000 in
/-- Every diagonal is above the smaller nonnegative quadratic root when
there is a zero diagonal and the pair coefficient is nonnegative. -/
theorem zeroDiagonal_projection_nonneg (N : Mat) {a b : ℝ}
    (hN : ∀ i j, 0 ≤ N i j) (hz : N 0 0 = 0 ∨ N 1 1 = 0 ∨ N 2 2 = 0)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hs : a+b = traceCoeff N) (hp : a*b = pairCoeff N) :
    ∀ i j, 0 ≤ (N^2-a • N) i j := by
  have hprod01 := mul_nonneg (hN 0 1) (hN 1 0)
  have hprod02 := mul_nonneg (hN 0 2) (hN 2 0)
  have hprod12 := mul_nonneg (hN 1 2) (hN 2 1)
  have hp' := pairCoeff_le_diagonal_products N hN
  have hbounds :
      (N 0 0 = 0 ∧ a ≤ N 1 1 ∧ a ≤ N 2 2) ∨
      (N 1 1 = 0 ∧ a ≤ N 0 0 ∧ a ≤ N 2 2) ∨
      (N 2 2 = 0 ∧ a ≤ N 0 0 ∧ a ≤ N 1 1) := by
    dsimp [traceCoeff] at hs
    rcases hz with hz | hz | hz
    · left
      refine ⟨hz,?_,?_⟩ <;> rw [hz] at hs hp'
      · by_contra h; nlinarith [sq_nonneg (a-N 1 1)]
      · by_contra h; nlinarith [sq_nonneg (a-N 2 2)]
    · right; left
      refine ⟨hz,?_,?_⟩ <;> rw [hz] at hs hp'
      · by_contra h; nlinarith [sq_nonneg (a-N 0 0)]
      · by_contra h; nlinarith [sq_nonneg (a-N 2 2)]
    · right; right
      refine ⟨hz,?_,?_⟩ <;> rw [hz] at hs hp'
      · by_contra h; nlinarith [sq_nonneg (a-N 0 0)]
      · by_contra h; nlinarith [sq_nonneg (a-N 1 1)]
  have hs01 : 0 ≤ N 0 0+N 1 1-a := by
    rcases hbounds with ⟨h,h1,h2⟩ | ⟨h,h1,h2⟩ | ⟨h,h1,h2⟩ <;> linarith [hN 0 0,hN 1 1]
  have hs02 : 0 ≤ N 0 0+N 2 2-a := by
    rcases hbounds with ⟨h,h1,h2⟩ | ⟨h,h1,h2⟩ | ⟨h,h1,h2⟩ <;> linarith [hN 0 0,hN 2 2]
  have hs12 : 0 ≤ N 1 1+N 2 2-a := by
    rcases hbounds with ⟨h,h1,h2⟩ | ⟨h,h1,h2⟩ | ⟨h,h1,h2⟩ <;> linarith [hN 1 1,hN 2 2]
  have hd0 : 0 ≤ N 0 0*(N 0 0-a) := by
    rcases hbounds with ⟨h,h1,h2⟩ | ⟨h,h1,h2⟩ | ⟨h,h1,h2⟩
    · simp [h]
    · exact mul_nonneg (hN 0 0) (sub_nonneg.mpr h1)
    · exact mul_nonneg (hN 0 0) (sub_nonneg.mpr h1)
  have hd1 : 0 ≤ N 1 1*(N 1 1-a) := by
    rcases hbounds with ⟨h,h1,h2⟩ | ⟨h,h1,h2⟩ | ⟨h,h1,h2⟩
    · exact mul_nonneg (hN 1 1) (sub_nonneg.mpr h1)
    · simp [h]
    · exact mul_nonneg (hN 1 1) (sub_nonneg.mpr h2)
  have hd2 : 0 ≤ N 2 2*(N 2 2-a) := by
    rcases hbounds with ⟨h,h1,h2⟩ | ⟨h,h1,h2⟩ | ⟨h,h1,h2⟩
    · exact mul_nonneg (hN 2 2) (sub_nonneg.mpr h2)
    · exact mul_nonneg (hN 2 2) (sub_nonneg.mpr h2)
    · simp [h]
  intro i j
  simp only [pow_two,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.mul_apply,Fin.sum_univ_three]
  fin_cases i <;> fin_cases j
  · change 0 ≤ N 0 0*N 0 0+N 0 1*N 1 0+N 0 2*N 2 0-a*N 0 0
    nlinarith [mul_nonneg (hN 0 1) (hN 1 2),mul_nonneg (hN 0 2) (hN 2 1),
      mul_nonneg (hN 1 0) (hN 0 2),mul_nonneg (hN 1 2) (hN 2 0),
      mul_nonneg (hN 2 0) (hN 0 1),mul_nonneg (hN 2 1) (hN 1 0),
      mul_nonneg (hN 0 1) hs01,mul_nonneg (hN 1 0) hs01,
      mul_nonneg (hN 0 2) hs02,mul_nonneg (hN 2 0) hs02,
      mul_nonneg (hN 1 2) hs12,mul_nonneg (hN 2 1) hs12]
  · change 0 ≤ N 0 0*N 0 1+N 0 1*N 1 1+N 0 2*N 2 1-a*N 0 1
    nlinarith [mul_nonneg (hN 0 1) (hN 1 2),mul_nonneg (hN 0 2) (hN 2 1),
      mul_nonneg (hN 1 0) (hN 0 2),mul_nonneg (hN 1 2) (hN 2 0),
      mul_nonneg (hN 2 0) (hN 0 1),mul_nonneg (hN 2 1) (hN 1 0),
      mul_nonneg (hN 0 1) hs01,mul_nonneg (hN 1 0) hs01,
      mul_nonneg (hN 0 2) hs02,mul_nonneg (hN 2 0) hs02,
      mul_nonneg (hN 1 2) hs12,mul_nonneg (hN 2 1) hs12]
  · change 0 ≤ N 0 0*N 0 2+N 0 1*N 1 2+N 0 2*N 2 2-a*N 0 2
    nlinarith [mul_nonneg (hN 0 1) (hN 1 2),mul_nonneg (hN 0 2) (hN 2 1),
      mul_nonneg (hN 1 0) (hN 0 2),mul_nonneg (hN 1 2) (hN 2 0),
      mul_nonneg (hN 2 0) (hN 0 1),mul_nonneg (hN 2 1) (hN 1 0),
      mul_nonneg (hN 0 1) hs01,mul_nonneg (hN 1 0) hs01,
      mul_nonneg (hN 0 2) hs02,mul_nonneg (hN 2 0) hs02,
      mul_nonneg (hN 1 2) hs12,mul_nonneg (hN 2 1) hs12]
  · change 0 ≤ N 1 0*N 0 0+N 1 1*N 1 0+N 1 2*N 2 0-a*N 1 0
    nlinarith [mul_nonneg (hN 0 1) (hN 1 2),mul_nonneg (hN 0 2) (hN 2 1),
      mul_nonneg (hN 1 0) (hN 0 2),mul_nonneg (hN 1 2) (hN 2 0),
      mul_nonneg (hN 2 0) (hN 0 1),mul_nonneg (hN 2 1) (hN 1 0),
      mul_nonneg (hN 0 1) hs01,mul_nonneg (hN 1 0) hs01,
      mul_nonneg (hN 0 2) hs02,mul_nonneg (hN 2 0) hs02,
      mul_nonneg (hN 1 2) hs12,mul_nonneg (hN 2 1) hs12]
  · change 0 ≤ N 1 0*N 0 1+N 1 1*N 1 1+N 1 2*N 2 1-a*N 1 1
    nlinarith [mul_nonneg (hN 0 1) (hN 1 2),mul_nonneg (hN 0 2) (hN 2 1),
      mul_nonneg (hN 1 0) (hN 0 2),mul_nonneg (hN 1 2) (hN 2 0),
      mul_nonneg (hN 2 0) (hN 0 1),mul_nonneg (hN 2 1) (hN 1 0),
      mul_nonneg (hN 0 1) hs01,mul_nonneg (hN 1 0) hs01,
      mul_nonneg (hN 0 2) hs02,mul_nonneg (hN 2 0) hs02,
      mul_nonneg (hN 1 2) hs12,mul_nonneg (hN 2 1) hs12]
  · change 0 ≤ N 1 0*N 0 2+N 1 1*N 1 2+N 1 2*N 2 2-a*N 1 2
    nlinarith [mul_nonneg (hN 0 1) (hN 1 2),mul_nonneg (hN 0 2) (hN 2 1),
      mul_nonneg (hN 1 0) (hN 0 2),mul_nonneg (hN 1 2) (hN 2 0),
      mul_nonneg (hN 2 0) (hN 0 1),mul_nonneg (hN 2 1) (hN 1 0),
      mul_nonneg (hN 0 1) hs01,mul_nonneg (hN 1 0) hs01,
      mul_nonneg (hN 0 2) hs02,mul_nonneg (hN 2 0) hs02,
      mul_nonneg (hN 1 2) hs12,mul_nonneg (hN 2 1) hs12]
  · change 0 ≤ N 2 0*N 0 0+N 2 1*N 1 0+N 2 2*N 2 0-a*N 2 0
    nlinarith [mul_nonneg (hN 0 1) (hN 1 2),mul_nonneg (hN 0 2) (hN 2 1),
      mul_nonneg (hN 1 0) (hN 0 2),mul_nonneg (hN 1 2) (hN 2 0),
      mul_nonneg (hN 2 0) (hN 0 1),mul_nonneg (hN 2 1) (hN 1 0),
      mul_nonneg (hN 0 1) hs01,mul_nonneg (hN 1 0) hs01,
      mul_nonneg (hN 0 2) hs02,mul_nonneg (hN 2 0) hs02,
      mul_nonneg (hN 1 2) hs12,mul_nonneg (hN 2 1) hs12]
  · change 0 ≤ N 2 0*N 0 1+N 2 1*N 1 1+N 2 2*N 2 1-a*N 2 1
    nlinarith [mul_nonneg (hN 0 1) (hN 1 2),mul_nonneg (hN 0 2) (hN 2 1),
      mul_nonneg (hN 1 0) (hN 0 2),mul_nonneg (hN 1 2) (hN 2 0),
      mul_nonneg (hN 2 0) (hN 0 1),mul_nonneg (hN 2 1) (hN 1 0),
      mul_nonneg (hN 0 1) hs01,mul_nonneg (hN 1 0) hs01,
      mul_nonneg (hN 0 2) hs02,mul_nonneg (hN 2 0) hs02,
      mul_nonneg (hN 1 2) hs12,mul_nonneg (hN 2 1) hs12]
  · change 0 ≤ N 2 0*N 0 2+N 2 1*N 1 2+N 2 2*N 2 2-a*N 2 2
    nlinarith [mul_nonneg (hN 0 1) (hN 1 2),mul_nonneg (hN 0 2) (hN 2 1),
      mul_nonneg (hN 1 0) (hN 0 2),mul_nonneg (hN 1 2) (hN 2 0),
      mul_nonneg (hN 2 0) (hN 0 1),mul_nonneg (hN 2 1) (hN 1 0),
      mul_nonneg (hN 0 1) hs01,mul_nonneg (hN 1 0) hs01,
      mul_nonneg (hN 0 2) hs02,mul_nonneg (hN 2 0) hs02,
      mul_nonneg (hN 1 2) hs12,mul_nonneg (hN 2 1) hs12]

end SSP.ThreeState
