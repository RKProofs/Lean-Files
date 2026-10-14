import SSPLean.K3CyclicComplexMiddleCertificate

/-! # Scalar semantics of the complex-middle coefficient certificate -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

open SSP.K3CyclicComplex.Dense
open scoped BigOperators

noncomputable def scalarZ (rhoValue : ℝ) : ℝ :=
  (1 - rhoValue ^ 2) / 3

noncomputable def scalarA (rhoValue etaValue : ℝ) : ℝ :=
  (2 - 2 * rhoValue + rhoValue * etaValue) / 3

noncomputable def scalarB (rhoValue etaValue : ℝ) : ℝ :=
  1 - scalarA rhoValue etaValue + scalarZ rhoValue

noncomputable def scalarDerivative
    (rhoValue etaValue : ℝ) (n : ℕ) : ℝ :=
  scalarA rhoValue etaValue *
      (1 - (cosineSign n : ℝ) * scalarZ rhoValue ^ (n / 2)) +
    scalarB rhoValue etaValue *
      ((sineSign n : ℝ) * scalarZ rhoValue ^ ((n - 1) / 2))

noncomputable def scalarCurvatureCoefficient
    (rhoValue etaValue : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    (kernel N j : ℝ) * scalarDerivative rhoValue etaValue j *
      scalarDerivative rhoValue etaValue (N - j)

@[simp] theorem beval_z (rhoValue etaValue : ℝ) :
    beval z rhoValue etaValue = scalarZ rhoValue := by
  simp [z, bone, rho, scalarZ, beval_mul, beval_sub, beval_pow]
  ring

@[simp] theorem beval_A (rhoValue etaValue : ℝ) :
    beval A rhoValue etaValue = scalarA rhoValue etaValue := by
  simp [A, rho, eta, scalarA, beval_add, beval_mul, beval_sub]
  ring

@[simp] theorem beval_B (rhoValue etaValue : ℝ) :
    beval B rhoValue etaValue = scalarB rhoValue etaValue := by
  simp [B, bone, scalarB, beval_add, beval_sub]

theorem derivative_eval (rhoValue etaValue : ℝ) (n : ℕ) :
    beval (derivative n) rhoValue etaValue =
      scalarDerivative rhoValue etaValue n := by
  simp [derivative, scalarDerivative, bone, beval_add, beval_mul,
    beval_sub, beval_pow]

theorem beval_range_foldl_badd (f : ℕ → Bi)
    (acc : Bi) (n : ℕ) (rhoValue etaValue : ℝ) :
    beval ((List.range n).foldl (fun p i => badd p (f i)) acc)
        rhoValue etaValue =
      beval acc rhoValue etaValue +
        ∑ i ∈ Finset.range n, beval (f i) rhoValue etaValue := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [beval_add, ih, Finset.sum_range_succ]
      ring

theorem curvatureCoefficient_eval (rhoValue etaValue : ℝ) (N : ℕ) :
    beval (curvatureCoefficient N) rhoValue etaValue =
      scalarCurvatureCoefficient rhoValue etaValue N := by
  unfold curvatureCoefficient
  rw [beval_range_foldl_badd]
  simp only [bzero, beval_nil, zero_add]
  unfold scalarCurvatureCoefficient
  apply Finset.sum_congr rfl
  intro j hj
  rw [beval_mul, beval_brat, beval_mul, derivative_eval, derivative_eval]
  ring

theorem scalarCurvatureCoefficient_nonneg_through_twenty_four
    {N : ℕ} (hN4 : 4 ≤ N) (hN24 : N ≤ 24)
    {rhoValue etaValue : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) :
    0 ≤ scalarCurvatureCoefficient rhoValue etaValue N := by
  rw [← curvatureCoefficient_eval]
  exact curvatureCoefficient_nonneg_through_twenty_four
    hN4 hN24 hrho0 hrho1 heta0 heta1

end SSP.K3CyclicComplex.MiddleCoeff
