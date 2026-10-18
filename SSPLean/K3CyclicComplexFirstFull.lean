import SSPLean.K3CyclicComplexFirstPositiveRemainder
import SSPLean.K3CyclicComplexFirstNegativeRemainder
import SSPLean.K3CyclicComplexFirstTail

/-! # Complete complex-spectrum canonical first-start inequality -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex

open SSP.K3Cyclic

theorem shiftedFirstF_correctedCurvature3_eq (m ω x : ℝ) :
    correctedCurvature3 x
        (shiftedFirstF m ω x) (shiftedFirstF1 m ω x)
          (shiftedFirstF2 m ω x) =
      Real.exp (2 * m * x) * correctedCurvature3 x
        (firstF m ω x) (firstF1 m ω x) (firstF2 m ω x) := by
  unfold shiftedFirstF shiftedFirstF1 shiftedFirstF2
  convert correctedCurvature3_exp_shift m x
    (firstF m ω x) (firstF1 m ω x) (firstF2 m ω x) using 1; ring

theorem firstFCurvature_pos_compact
    {m ω x : ℝ} (hdom : FirstDomain m ω)
    (hx0 : 0 ≤ x) (hx10 : x ≤ 10) (hω : ω ≠ 0) :
    0 < correctedCurvature3 x
      (firstF m ω x) (firstF1 m ω x) (firstF2 m ω x) := by
  rcases hdom with ⟨hmLower, hmUpper, hz0, hzLower, hzUpper⟩
  by_cases hm0 : 0 ≤ m
  · let r : ℝ := 3 * m
    let gap : ℝ := 1 - 2 * m - 3 * m ^ 2
    let τ : ℝ := 4 * ω ^ 2 / gap
    have hωsq : 0 < ω ^ 2 := sq_pos_of_ne_zero hω
    have hgap : 0 < gap := by dsimp [gap]; nlinarith
    have hr0 : 0 ≤ r := by dsimp [r]; linarith
    have hr1 : r ≤ 1 := by dsimp [r]; linarith
    have hτ0 : 0 ≤ τ := by dsimp [τ]; positivity
    have hτ1 : τ ≤ 1 := by
      dsimp [τ]
      exact (div_le_one hgap).2 hzUpper
    have hz : PositiveCoeff.scalarZ r τ = ω ^ 2 := by
      unfold PositiveCoeff.scalarZ
      dsimp only [r, τ]
      have hbracket : 3 - 2 * (3 * m) - (3 * m) ^ 2 = 3 * gap := by
        dsimp [gap]
        ring
      rw [hbracket]
      field_simp [hgap.ne']
      ring
    have h := PositiveCoeff.firstFCurvature_pos_on_positive_compact
      hr0 hr1 hτ0 hτ1 (by rfl) hz hω hx0 hx10
    simpa [correctedCurvature3, add_comm] using h
  · have hmNeg : m < 0 := lt_of_not_ge hm0
    let r : ℝ := -3 * m
    have hr0 : 0 ≤ r := by dsimp [r]; linarith
    have hr1 : r ≤ 1 := by dsimp [r]; linarith
    by_cases hmBoundary : m = -(1 / 3 : ℝ)
    · let τ : ℝ := 0
      have hzEq : ω ^ 2 = 1 / 3 := by
        subst m
        norm_num at hzLower hzUpper ⊢
        linarith
      have hz : NegativeCoeff.scalarZ r τ = ω ^ 2 := by
        dsimp [NegativeCoeff.scalarZ, r, τ]
        rw [hmBoundary, hzEq]
        norm_num
      have hshift := NegativeCoeff.shiftedFirstFCurvature_pos_on_negative_compact
        hr0 hr1 (by simp [τ]) (by simp [τ]) (by rfl) hz hω hx0 hx10
      have hshiftCurv : 0 < correctedCurvature3 x
          (shiftedFirstF m ω x) (shiftedFirstF1 m ω x)
            (shiftedFirstF2 m ω x) := by
        simpa [correctedCurvature3, add_comm] using hshift
      rw [shiftedFirstF_correctedCurvature3_eq] at hshiftCurv
      rcases mul_pos_iff.mp hshiftCurv with hpos | hneg
      · exact hpos.2
      · linarith [Real.exp_pos (2 * m * x)]
    · let lower : ℝ := -(3 * m ^ 2 + 2 * m)
      let gap : ℝ := (1 + 3 * m) ^ 2 / 4
      let τ : ℝ := (ω ^ 2 - lower) / gap
      have hmInterior : -(1 / 3 : ℝ) < m := lt_of_le_of_ne hmLower
        (Ne.symm hmBoundary)
      have hgap : 0 < gap := by
        dsimp [gap]
        have : 0 < 1 + 3 * m := by linarith
        positivity
      have hτ0 : 0 ≤ τ := by
        dsimp [τ, lower]
        exact div_nonneg (by linarith) hgap.le
      have hτ1 : τ ≤ 1 := by
        apply (div_le_one hgap).2
        dsimp [lower, gap]
        nlinarith
      have hz : NegativeCoeff.scalarZ r τ = ω ^ 2 := by
        dsimp [NegativeCoeff.scalarZ, r, τ, lower, gap]
        have hlinear : 1 + 3 * m ≠ 0 := by linarith
        field_simp [hlinear]
        ring
      have hshift := NegativeCoeff.shiftedFirstFCurvature_pos_on_negative_compact
        hr0 hr1 hτ0 hτ1 (by rfl) hz hω hx0 hx10
      have hshiftCurv : 0 < correctedCurvature3 x
          (shiftedFirstF m ω x) (shiftedFirstF1 m ω x)
            (shiftedFirstF2 m ω x) := by
        simpa [correctedCurvature3, add_comm] using hshift
      rw [shiftedFirstF_correctedCurvature3_eq] at hshiftCurv
      rcases mul_pos_iff.mp hshiftCurv with hpos | hneg
      · exact hpos.2
      · linarith [Real.exp_pos (2 * m * x)]

theorem firstH_correctedCurvature3_nonneg
    {m ω x : ℝ} (hdom : FirstDomain m ω)
    (hx : 0 ≤ x) (hω : ω ≠ 0) :
    0 ≤ correctedCurvature3 x
      (firstH m ω x) (firstH1 m ω x) (firstH2 m ω x) := by
  by_cases hx10 : x ≤ 10
  · have hF := (firstFCurvature_pos_compact hdom hx hx10 hω).le
    have hscale := correctedCurvature3_nonneg_of_amplitude
      (q := 1 + ω ^ 2) hF
    have hq : 1 + ω ^ 2 ≠ 0 := one_add_sq_ne_zero ω
    convert hscale using 1;
      simp [firstF, firstF1, firstF2]; field_simp [hq]
  · exact firstH_correctedCurvature3_nonneg_tail hdom (by linarith) hω

end SSP.K3CyclicComplex
