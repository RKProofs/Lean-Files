import SSPLean.K3CyclicComplexFirstNegativeDegreeBounds
import SSPLean.K3CyclicComplexFirstPositiveTimeConversion

/-! # Scalar meaning of the executable curvature coefficients -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex

open Dense

def scalarCurvatureCoefficient (d : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    (ComplexCoeff.kernel N j : ℝ) * d j * d (N - j)

theorem beval_curvatureFold (derivatives : List Bi) (N : ℕ) (r t : ℝ) :
    beval
      ((List.range (N + 1)).foldl (fun p j =>
        badd p (bmul (brat (ComplexCoeff.kernel N j))
          (bmul (derivatives.getD j [])
            (derivatives.getD (N - j) [])))) []) r t =
      scalarCurvatureCoefficient
        (fun j => beval (derivatives.getD j []) r t) N := by
  rw [PositiveCoeff.beval_range_foldl_badd]
  simp only [beval_nil, zero_add]
  unfold scalarCurvatureCoefficient
  apply Finset.sum_congr rfl
  intro j hj
  rw [beval_mul, beval_brat, beval_mul]
  ring

namespace PositiveCoeff

def derivativeValue (r t : ℝ) (n : ℕ) : ℝ :=
  beval (derivativeTriple n).1 r t

theorem curvatureCoefficientFrom_eval
    {count N : ℕ} (hN : N < count) (r t : ℝ) :
    beval (curvatureCoefficientFrom (derivativeTable count) N) r t =
      scalarCurvatureCoefficient (derivativeValue r t) N := by
  unfold curvatureCoefficientFrom
  change beval
    ((List.range (N + 1)).foldl (fun p j =>
      badd p (bmul (brat (ComplexCoeff.kernel N j))
        (bmul ((derivativeTable count).getD j [])
          ((derivativeTable count).getD (N - j) [])))) []) r t = _
  rw [beval_curvatureFold]
  unfold scalarCurvatureCoefficient derivativeValue
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hjEq : (derivativeTable count).getD j [] =
      (derivativeTriple j).1 := by
    simpa [bzero] using derivativeTable_getD (count := count) (j := j) (by omega)
  have hsubEq : (derivativeTable count).getD (N - j) [] =
      (derivativeTriple (N - j)).1 := by
    simpa [bzero] using derivativeTable_getD
      (count := count) (j := N - j) (by omega)
  dsimp only
  rw [hjEq, hsubEq]

theorem powerTableUpTo_eval {count N : ℕ} (hN : N < count)
    (r t : ℝ) :
    beval ((powerTableUpTo count).getD N bzero) r t =
      ((10 : ℝ) ^ N / Nat.factorial N) *
        scalarCurvatureCoefficient (derivativeValue r t) N := by
  rw [List.getD_eq_getElem _ _ (by simp [powerTableUpTo]; omega)]
  simp only [powerTableUpTo, List.getElem_map, List.getElem_range]
  rw [beval_mul, beval_brat, curvatureCoefficientFrom_eval hN]
  push_cast
  rfl

end PositiveCoeff

namespace NegativeCoeff

def derivativeValue (r t : ℝ) (n : ℕ) : ℝ :=
  beval (derivativeTriple n).1 r t

theorem curvatureCoefficient_eval (N : ℕ) (r t : ℝ) :
    beval (curvatureCoefficient N) r t =
      scalarCurvatureCoefficient (derivativeValue r t) N := by
  unfold curvatureCoefficient
  dsimp only
  change beval
    ((List.range (N + 1)).foldl (fun p j =>
      badd p (bmul (brat (ComplexCoeff.kernel N j))
        (bmul ((derivativeTable (N + 1)).getD j [])
          ((derivativeTable (N + 1)).getD (N - j) [])))) []) r t = _
  rw [beval_curvatureFold]
  unfold scalarCurvatureCoefficient derivativeValue
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hjEq : (derivativeTable (N + 1)).getD j [] =
      (derivativeTriple j).1 := by
    simpa [bzero] using derivativeTable_getD
      (count := N + 1) (j := j) (by omega)
  have hsubEq : (derivativeTable (N + 1)).getD (N - j) [] =
      (derivativeTriple (N - j)).1 := by
    simpa [bzero] using derivativeTable_getD
      (count := N + 1) (j := N - j) (by omega)
  dsimp only
  rw [hjEq, hsubEq]

end NegativeCoeff

end SSP.K3CyclicComplex
