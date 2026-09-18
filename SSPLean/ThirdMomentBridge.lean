import SSPLean.ThirdMomentLaw
import SSPLean.MomentHierarchy

/-!
# The third-moment bridge

This file identifies the analytic `N³𝟙` appearing in `SSP.Law.third_moment_eq` with the
finite-array quantity `SSP.rowSum3` used by the order-three SSP hierarchy.
-/

open scoped Matrix.Norms.Operator
open SSP Finset Matrix

set_option autoImplicit false

namespace SSP.Bridge

/-- `rowSum3` of the resolvent is `((I-Q)⁻¹)³𝟙` entrywise. -/
theorem rowSum3_invMat_eq {s : ℕ} (Q : ℕ → ℕ → ℝ) (i : ℕ) (hi : i < s) :
    rowSum3 s (invMat s Q) i
      = ((1 - toMat s Q)⁻¹.mulVec ((1 - toMat s Q)⁻¹.mulVec
          ((1 - toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) ⟨i, hi⟩ := by
  unfold rowSum3
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => ∑ l ∈ range s, ∑ m ∈ range s,
      invMat s Q i j * invMat s Q j l * invMat s Q l m) s]
  change (∑ j : Fin s, ∑ l ∈ range s, ∑ m ∈ range s,
      invMat s Q i j * invMat s Q j l * invMat s Q l m)
    = ∑ j : Fin s, (1 - toMat s Q)⁻¹ ⟨i, hi⟩ j * _
  refine Finset.sum_congr rfl fun j _ => ?_
  change (∑ l ∈ range s, ∑ m ∈ range s,
      invMat s Q i j * invMat s Q j l * invMat s Q l m)
    = (1 - toMat s Q)⁻¹ ⟨i, hi⟩ j *
      (∑ l : Fin s, (1 - toMat s Q)⁻¹ j l *
        (∑ m : Fin s, (1 - toMat s Q)⁻¹ l m * 1))
  rw [← Fin.sum_univ_eq_sum_range
    (fun l => ∑ m ∈ range s, invMat s Q i j * invMat s Q j l * invMat s Q l m) s]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  change (∑ m ∈ range s, invMat s Q i j * invMat s Q j l * invMat s Q l m)
    = (1 - toMat s Q)⁻¹ ⟨i, hi⟩ j *
      ((1 - toMat s Q)⁻¹ j l *
        (∑ m : Fin s, (1 - toMat s Q)⁻¹ l m * 1))
  rw [← Fin.sum_univ_eq_sum_range
    (fun m => invMat s Q i j * invMat s Q j l * invMat s Q l m) s]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [invMat,
    dif_pos (⟨hi, j.isLt⟩ : i < s ∧ (j : ℕ) < s),
    dif_pos (⟨j.isLt, l.isLt⟩ : (j : ℕ) < s ∧ (l : ℕ) < s),
    dif_pos (⟨l.isLt, m.isLt⟩ : (l : ℕ) < s ∧ (m : ℕ) < s), mul_one]
  ring

/-- The concrete absorption-law third moment, in the finite `rowSum3` interface. -/
theorem third_moment_eq_rowSum3 {s : ℕ} (Q : ℕ → ℕ → ℝ) (θ : ℝ)
    (hQ : ∀ i j, 0 ≤ toMat s Q i j)
    (hrow : ∀ i, ∑ j, toMat s Q i j ≤ 1)
    (hu : IsUnit (1 - toMat s Q)) (hnorm : ‖toMat s Q‖ ≤ θ) (hθ : θ < 1)
    (i : ℕ) (hi : i < s) :
    (∫ x, (id x)^3 ∂(SSP.Survival.survivalStieltjes
      (toMat s Q) hQ hrow ⟨i, hi⟩).measure)
      = 6 * rowSum3 s (invMat s Q) i := by
  rw [rowSum3_invMat_eq Q i hi]
  exact SSP.Law.third_moment_eq (toMat s Q) θ hQ hrow hu hnorm hθ ⟨i, hi⟩

/-- `rowSum3` agrees between the Neumann-series and resolvent fundamental matrices. -/
theorem rowSum3_Nmat_eq_invMat {s : ℕ} (Q : ℕ → ℕ → ℝ)
    (hρ : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (i : ℕ) (hi : i < s) :
    rowSum3 s (Nmat s Q) i = rowSum3 s (invMat s Q) i := by
  unfold rowSum3
  refine Finset.sum_congr rfl fun j hj => ?_
  refine Finset.sum_congr rfl fun l hl => ?_
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Nmat_eq_invMat s Q hρ i j hi (mem_range.1 hj),
    Nmat_eq_invMat s Q hρ j l (mem_range.1 hj) (mem_range.1 hl),
    Nmat_eq_invMat s Q hρ l m (mem_range.1 hl) (mem_range.1 hm)]

end SSP.Bridge
