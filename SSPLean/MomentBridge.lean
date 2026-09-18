import SSPLean.SemigroupMoments
import SSPLean.SpectralDecay

/-!
# Bridging the discrete and resolvent forms of the fundamental matrix

`SSPLean.QSequencePaths` and `SSPLean.SSPBound` work with `N` as a `ℕ → ℕ → ℝ` array — `Nmat`,
the entrywise Neumann series, read by `rowSum` and `rowSum2`.  `SSPLean.SemigroupMoments` proves
the resolvent integrals in terms of the genuine matrix inverse `(1 − Q)⁻¹` and `Matrix.mulVec`.

This file connects the two, so that the moment identities proved analytically can be stated in
the interface `SSPLean.AldousShepp` uses.  `SSP.Nmat_eq_invMat` already identifies the two
entrywise; what is added here is the row-sum level:

```
  rowSum  s (invMat s Q) i = ((1−Q)⁻¹ 𝟙)ᵢ ,      rowSum2 s (invMat s Q) i = ((1−Q)⁻¹((1−Q)⁻¹𝟙))ᵢ .
```

Combining these with `SSP.Semigroup.integral_survival` and
`SSP.Semigroup.integral_resolvent_sq` expresses `rowSum`/`rowSum2` as survival integrals, which
is the analytic half of the phase-type moment dictionary.
-/

open scoped Matrix.Norms.Operator
open SSP Finset Matrix

set_option autoImplicit false

namespace SSP.Bridge

/-- `rowSum` of the resolvent equals `((1−Q)⁻¹ 𝟙)ᵢ`. -/
theorem rowSum_invMat_eq {s : ℕ} (Q : ℕ → ℕ → ℝ) (i : ℕ) (hi : i < s) :
    rowSum s (invMat s Q) i
      = ((1 - toMat s Q)⁻¹.mulVec (fun _ => (1:ℝ))) ⟨i, hi⟩ := by
  change (∑ j ∈ range s, invMat s Q i j) = _
  rw [← Fin.sum_univ_eq_sum_range (fun j => invMat s Q i j) s]
  change (∑ j : Fin s, invMat s Q i j) = ∑ j : Fin s, (1 - toMat s Q)⁻¹ ⟨i, hi⟩ j * 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [invMat, dif_pos (⟨hi, j.isLt⟩ : i < s ∧ (j:ℕ) < s), mul_one]

/-- `rowSum2` of the resolvent equals `((1−Q)⁻¹((1−Q)⁻¹𝟙))ᵢ`, i.e. `(N²𝟙)ᵢ`. -/
theorem rowSum2_invMat_eq {s : ℕ} (Q : ℕ → ℕ → ℝ) (i : ℕ) (hi : i < s) :
    rowSum2 s (invMat s Q) i
      = ((1 - toMat s Q)⁻¹.mulVec ((1 - toMat s Q)⁻¹.mulVec (fun _ => (1:ℝ)))) ⟨i, hi⟩ := by
  change (∑ j ∈ range s, ∑ l ∈ range s, invMat s Q i j * invMat s Q j l) = _
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => ∑ l ∈ range s, invMat s Q i j * invMat s Q j l) s]
  change (∑ j : Fin s, ∑ l ∈ range s, invMat s Q i j * invMat s Q j l)
      = ∑ j : Fin s, (1 - toMat s Q)⁻¹ ⟨i, hi⟩ j * _
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun l => invMat s Q i j * invMat s Q j l) s]
  simp only [invMat, dif_pos (⟨hi, j.isLt⟩ : i < s ∧ (j:ℕ) < s)]
  rw [← Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [dif_pos (⟨j.isLt, l.isLt⟩ : (j:ℕ) < s ∧ (l:ℕ) < s), mul_one]

/-! ## The moment identities in the `rowSum` interface

With the bridges in place, the resolvent integrals of `SSPLean.SemigroupMoments` become
statements about `rowSum`/`rowSum2` — the form `SSPLean.AldousShepp` consumes. -/

/-- **First moment, in the `rowSum` interface.**
`∫₀^∞ (exp(t(Q−I))𝟙)ᵢ dt = rowSum s (invMat s Q) i`. -/
theorem integral_eq_rowSum {s : ℕ} (Q : ℕ → ℕ → ℝ) (θ : ℝ)
    (hu : IsUnit (1 - toMat s Q)) (hQ : ‖toMat s Q‖ ≤ θ) (hθ : θ < 1)
    (i : ℕ) (hi : i < s) :
    (∫ t in Set.Ioi (0:ℝ),
        ((NormedSpace.exp (t • (toMat s Q - 1))).mulVec (fun _ => 1)) ⟨i, hi⟩)
      = rowSum s (invMat s Q) i := by
  rw [rowSum_invMat_eq Q i hi]
  exact SSP.Semigroup.integral_survival (toMat s Q) θ hu hQ hθ ⟨i, hi⟩

/-- **Second moment, in the `rowSum` interface.**
`∫₀^∞ (exp(t(Q−I))·N𝟙)ᵢ dt = rowSum2 s (invMat s Q) i`, i.e. `E_i[X²]/2`. -/
theorem integral_eq_rowSum2 {s : ℕ} (Q : ℕ → ℕ → ℝ) (θ : ℝ)
    (hu : IsUnit (1 - toMat s Q)) (hQ : ‖toMat s Q‖ ≤ θ) (hθ : θ < 1)
    (i : ℕ) (hi : i < s) :
    (∫ t in Set.Ioi (0:ℝ),
        ((NormedSpace.exp (t • (toMat s Q - 1))).mulVec
          ((1 - toMat s Q)⁻¹.mulVec (fun _ => 1))) ⟨i, hi⟩)
      = rowSum2 s (invMat s Q) i := by
  rw [rowSum2_invMat_eq Q i hi]
  exact SSP.Semigroup.integral_resolvent_sq (toMat s Q) θ hu hQ hθ ⟨i, hi⟩

/-! ## From the Neumann series to the resolvent, at the row-sum level

`SSP.Nmat_eq_invMat` identifies the two entrywise; these lift it to `rowSum` and `rowSum2`, which
is the form `SSP.componentBound_unconditional` produces. -/

/-- `rowSum` agrees between the Neumann series and the resolvent. -/
theorem rowSum_Nmat_eq_invMat {s : ℕ} (Q : ℕ → ℕ → ℝ)
    (hρ : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1) (i : ℕ) (hi : i < s) :
    rowSum s (Nmat s Q) i = rowSum s (invMat s Q) i := by
  change (∑ j ∈ range s, Nmat s Q i j) = ∑ j ∈ range s, invMat s Q i j
  refine Finset.sum_congr rfl fun j hj => Nmat_eq_invMat s Q hρ i j hi (mem_range.1 hj)

/-- `rowSum2` agrees between the Neumann series and the resolvent. -/
theorem rowSum2_Nmat_eq_invMat {s : ℕ} (Q : ℕ → ℕ → ℝ)
    (hρ : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1) (i : ℕ) (hi : i < s) :
    rowSum2 s (Nmat s Q) i = rowSum2 s (invMat s Q) i := by
  change (∑ j ∈ range s, ∑ l ∈ range s, Nmat s Q i j * Nmat s Q j l)
      = ∑ j ∈ range s, ∑ l ∈ range s, invMat s Q i j * invMat s Q j l
  refine Finset.sum_congr rfl fun j hj => ?_
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Nmat_eq_invMat s Q hρ i j hi (mem_range.1 hj),
      Nmat_eq_invMat s Q hρ j l (mem_range.1 hj) (mem_range.1 hl)]

end SSP.Bridge
