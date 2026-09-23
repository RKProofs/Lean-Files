import SSPLean.K3AllStagesTerminalFace
import SSPLean.K3AllStagesPositiveSlopeComplete

/-!
# Completion of the uniform `k = 3` induction step

This module assembles the completed return- and terminal-face certificates.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

/-- The return-face condition is unconditional after the positive-current-
slope chart certificates are inserted. -/
theorem uniformSharpFaceA_nonneg
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hgrad : uniformGradA n a T Y q < 0)
    (hreturn : uniformReturnSide n a T Y q ≤ 0) :
    0 ≤ uniformSharpFaceA n a T Y q := by
  have hgrad1 := uniformGradA_at_a_one_neg_of_neg
    n a T Y q hn ha ha1 hT.le hY hq.le hgrad
  by_cases hT1 : T ≤ n - 1
  · exact uniformSharpFaceA_nonneg_of_T_le
      n a T Y q hn ha hT hT1 hY hq hq1
  by_cases hM : 0 < uniformFaceACurrentM n T q
  · have hK := uniformFaceACurrentK_pos n T q hn (by linarith) hq.le hq1
    have hcert : ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
        uniformFaceACurrentGradPoly n T q w < 0 →
        0 ≤ uniformFaceACurrentPoly n T q w := by
      intro w hw hw1 hgradPoly
      let m := n-4
      let z := T-(n-1)
      have hm : 0 ≤ m := by dsimp [m]; linarith
      have hz : 0 ≤ z := by dsimp [z]; linarith
      have hnid : m+4 = n := by dsimp [m]; ring
      have hTid : m+3+z = T := by dsimp [m, z]; ring
      rw [← hnid, ← hTid] at hM hgradPoly ⊢
      exact uniformFaceAPositive_poly_nonneg
        m z q w hm hz hq hq1 hw hw1 hM hgradPoly
    have hcore := uniformFaceACore_nonneg_of_current_poly_of_grad
      n a T Y q (by linarith) ha hY hM hK hreturn hgrad1 hcert
    apply uniformSharpFaceA_nonneg_of_num n a T Y q hn ha hT hY hq
    have hm2 : 0 ≤ uniformCornerM2Num n a T Y q := by
      unfold uniformCornerM2Num
      have hn1 : 0 ≤ n - 1 := by linarith
      have hTq : 0 ≤ T * q := by positivity
      have hcross : 0 ≤ 2 * (n - 1) * (T * q) := by positivity
      have hmain : 0 ≤ n * T^2 * q := by positivity
      have hay : 0 ≤ n * a * Y := by positivity
      nlinarith
    rw [uniformFaceANum_factor]
    positivity
  · exact uniformSharpFaceA_nonneg_of_currentM_nonpos_complete
      n a T Y q hn ha hT (by linarith) hY hq (le_of_not_gt hM)

/-- Unconditional mixture-coordinate form of the all-stage `k = 3`
third-moment induction step. -/
theorem excursionReducedGap_mixture_coordinates_nonneg
    (n a T Y p q C D : ℝ)
    (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hp : 0 < p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hC : (n + 1) * (n * p * Y ^ 2 / (n - 1)) ^ 2 ≤ n * (p * Y) * C)
    (hD : (n + 1) * (n * q * T ^ 2 / (n - 1)) ^ 2 ≤ n * (q * T) * D) :
    0 ≤ excursionReducedGap n (a / (p * Y)) (p * Y * (1 - a) / (p * Y + a))
      (p * Y) (n * p * Y ^ 2 / (n - 1)) C (q * T) (n * q * T ^ 2 / (n - 1)) D := by
  apply excursionReducedGap_mixture_coordinates_nonneg_of_uniform_faces
    n a T Y p q C D hn ha ha1 hT hY hp hp1 hq hq1 hC hD
  · intro hgrad hreturn
    exact uniformSharpFaceA_nonneg
      n a T Y q hn ha ha1 hT hY hq hq1 hgrad hreturn
  · exact uniformSharpFaceB_nonneg n a T Y q hn ha ha1 hT hY hq hq1

end SSP.K3AllStages
