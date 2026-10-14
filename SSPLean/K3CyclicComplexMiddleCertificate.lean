import SSPLean.K3CyclicComplexMiddleCoefficient

/-! # Finite Bernstein certificate for the complex middle start -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

open SSP.K3CyclicComplex.Dense
open SSP.K3CyclicComplex.ComplexCoeff

theorem certificate_through_twenty_four {N : ℕ}
    (hN4 : 4 ≤ N) (hN24 : N ≤ 24) : certificateOK N = true := by
  by_cases h12 : N ≤ 12
  · exact List.all_eq_true.mp certificate_four_through_twelve N
      (List.mem_map.mpr ⟨N - 4, List.mem_range.mpr (by omega), by omega⟩)
  by_cases h18 : N ≤ 18
  · exact List.all_eq_true.mp certificate_thirteen_through_eighteen N
      (List.mem_map.mpr ⟨N - 13, List.mem_range.mpr (by omega), by omega⟩)
  · exact List.all_eq_true.mp certificate_nineteen_through_twenty_four N
      (List.mem_map.mpr ⟨N - 19, List.mem_range.mpr (by omega), by omega⟩)

theorem degree_through_twenty_four {N : ℕ}
    (hN4 : 4 ≤ N) (hN24 : N ≤ 24) : degreeOK N = true := by
  exact List.all_eq_true.mp degree_four_through_twenty_four N
    (List.mem_map.mpr ⟨N - 4, List.mem_range.mpr (by omega), by omega⟩)

theorem bernCoeff_nonneg_of_certificate {N i j : ℕ}
    (h : certificateOK N = true)
    (hi : i ≤ certificateDegree N) (hj : j ≤ certificateDegree N / 2) :
    0 ≤ bernCoeffOf (curvatureCoefficient N) (certificateDegree N) i j := by
  simp only [certificateOK] at h
  have hi' := List.all_eq_true.mp h i
    (List.mem_range.mpr (Nat.lt_succ_iff.mpr hi))
  have hj' := List.all_eq_true.mp hi' j
    (List.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  exact of_decide_eq_true hj'

theorem degree_bounds_of_ok {N : ℕ} (h : degreeOK N = true) :
    (curvatureCoefficient N).length ≤ certificateDegree N / 2 + 1 ∧
      ∀ row ∈ curvatureCoefficient N,
        row.length ≤ certificateDegree N + 1 := by
  simp only [degreeOK] at h
  exact of_decide_eq_true h

theorem curvatureCoefficient_nonneg_of_certificate {N : ℕ}
    (hcert : certificateOK N = true) (hdegree : degreeOK N = true)
    {rhoValue etaValue : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) :
    0 ≤ beval (curvatureCoefficient N) rhoValue etaValue := by
  obtain ⟨houter, hrows⟩ := degree_bounds_of_ok hdegree
  have hinner : ∀ b, b ≤ certificateDegree N / 2 →
      ((curvatureCoefficient N).getD b []).length ≤ certificateDegree N + 1 := by
    intro b hb
    by_cases hmem : b < (curvatureCoefficient N).length
    · rw [List.getD_eq_getElem _ _ hmem]
      exact hrows _ (List.getElem_mem hmem)
    · rw [List.getD_eq_default _ _ (by omega)]
      simp
  rw [beval_eq_tensorBernstein (curvatureCoefficient N) (certificateDegree N)
    houter hinner]
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  have hiN : i ≤ certificateDegree N :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hjN : j ≤ certificateDegree N / 2 :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hc : 0 ≤
      (bernCoeffOf (curvatureCoefficient N) (certificateDegree N) i j : ℝ) := by
    exact_mod_cast bernCoeff_nonneg_of_certificate hcert hiN hjN
  have hr : 0 ≤ (Nat.choose (certificateDegree N) i : ℝ) *
      rhoValue ^ i * (1 - rhoValue) ^ (certificateDegree N - i) := by
    positivity
  have ht : 0 ≤ (Nat.choose (certificateDegree N / 2) j : ℝ) *
      etaValue ^ j *
        (1 - etaValue) ^ (certificateDegree N / 2 - j) := by
    positivity
  positivity

theorem curvatureCoefficient_nonneg_through_twenty_four
    {N : ℕ} (hN4 : 4 ≤ N) (hN24 : N ≤ 24)
    {rhoValue etaValue : ℝ}
    (hrho0 : 0 ≤ rhoValue) (hrho1 : rhoValue ≤ 1)
    (heta0 : 0 ≤ etaValue) (heta1 : etaValue ≤ 1) :
    0 ≤ beval (curvatureCoefficient N) rhoValue etaValue :=
  curvatureCoefficient_nonneg_of_certificate
    (certificate_through_twenty_four hN4 hN24)
    (degree_through_twenty_four hN4 hN24)
    hrho0 hrho1 heta0 heta1

end SSP.K3CyclicComplex.MiddleCoeff
