import SSPLean.K3CyclicComplexFirstCoefficient

/-! # Semantic core for the complex first-start compact certificate -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex

open Dense

namespace ComplexCoeff

theorem bernCoeffOf_nonneg_of_certificate {N i j : ℕ}
    (h : certificateOK N = true) (hi : i ≤ N) (hj : j ≤ N / 2) :
    0 ≤ bernCoeffOf (curvatureCoefficient N) N i j := by
  simp only [certificateOK] at h
  have hi' := List.all_eq_true.mp h i
    (List.mem_range.mpr (Nat.lt_succ_iff.mpr hi))
  have hj' := List.all_eq_true.mp hi' j
    (List.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  exact of_decide_eq_true hj'

@[simp] theorem beval_bernInner (n i : ℕ) (r t : ℝ) :
    beval (bernInner n i) r t =
      (Nat.choose n i : ℝ) * r ^ i * (1 - r) ^ (n - i) := by
  simp [bernInner, bone, beval_mul, beval_pow]
  ring

@[simp] theorem beval_bernOuter (n i : ℕ) (r t : ℝ) :
    beval (bernOuter n i) r t =
      (Nat.choose n i : ℝ) * t ^ i * (1 - t) ^ (n - i) := by
  simp [bernOuter, bone, beval_mul, beval_pow]
  ring

theorem beval_bernInner_nonneg {n i : ℕ} {r t : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ beval (bernInner n i) r t := by
  rw [beval_bernInner]
  positivity

theorem beval_bernOuter_nonneg {n i : ℕ} {r t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ beval (bernOuter n i) r t := by
  rw [beval_bernOuter]
  positivity

private theorem foldl_beval_nonneg {α : Type*}
    (l : List α) (step : Bi → α → Bi) (acc : Bi) (r t : ℝ)
    (hacc : 0 ≤ beval acc r t)
    (hstep : ∀ p a, a ∈ l → 0 ≤ beval p r t → 0 ≤ beval (step p a) r t) :
    0 ≤ beval (l.foldl step acc) r t := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons a l ih =>
      apply ih
      · exact hstep acc a (by simp) hacc
      · intro p b hb hp
        exact hstep p b (by simp [hb]) hp

theorem bernsteinReconstruction_nonneg {N : ℕ} {r t : ℝ}
    (hcert : certificateOK N = true)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ beval (bernsteinReconstruction N) r t := by
  unfold bernsteinReconstruction
  dsimp only
  apply foldl_beval_nonneg
  · change (0 : ℝ) ≤ 0
    exact le_rfl
  · intro acc i hi hacc
    apply foldl_beval_nonneg
    · exact hacc
    · intro acc j hj hacc
      rw [beval_add]
      apply add_nonneg hacc
      rw [beval_mul, beval_brat, beval_mul]
      apply mul_nonneg
      · exact_mod_cast bernCoeffOf_nonneg_of_certificate hcert
          (Nat.le_of_lt_succ (List.mem_range.mp hi))
          (Nat.le_of_lt_succ (List.mem_range.mp hj))
      · exact mul_nonneg (beval_bernInner_nonneg hr0 hr1)
          (beval_bernOuter_nonneg ht0 ht1)

end ComplexCoeff

end SSP.K3CyclicComplex
