import SSPLean.K3AllStagesPositiveSlopeLargeB3C0
import SSPLean.K3AllStagesPositiveSlopeLargeB3C1
import SSPLean.K3AllStagesPositiveSlopeLargeB3C2
import SSPLean.K3AllStagesPositiveSlopeLargeB3C3
/-! Assemble the factored endpoint coefficients without expanding the full
rational chart. The common positive factors stay opaque during normalization. -/
set_option autoImplicit false
namespace SSP.K3AllStages

theorem B3CurrentK_affine (n T q t : ℝ) :
    uniformFaceACurrentK n T (q + t*(1-q)) =
      uniformFaceACurrentK n T q + t*(uniformFaceACurrentK n T 1 - uniformFaceACurrentK n T q) := by
  unfold uniformFaceACurrentK uniformReturnK
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem B3_shift_eq (m s r : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceAPositiveHighVWLargeB3 m s ((1+r)/2) =
      B3ShiftCoefficient 0 m s + B3ShiftCoefficient 1 m s*r
        + B3ShiftCoefficient 2 m s*r^2 + B3ShiftCoefficient 3 m s*r^3 := by
  simp only [uniformFaceAPositiveHighVWLargeB3, uniformCubicSampleB3]
  unfold uniformFaceAPositiveHighVWLargeEndpoint
  simp only [one_mul, uniformFaceAPositiveQ]
  rw [B3CurrentK_affine]
  rw [uniformFaceACoreXC0_at_one, uniformFaceACoreXC1_at_one,
      uniformFaceACoreXC2_at_one, uniformFaceACoreXC3_at_one]
  rw [LargeL_eq m s hm hs, LargeK0_eq m s hm hs, LargeK1_eq m s hm hs]
  rw [LargeX0_eq m s hm, LargeX1_eq m s hm, LargeX2_eq m s hm, LargeX3_eq m s hm]
  simp only [B3ShiftCoefficient, B3Power, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have ha : m+6 ≠ 0 := by linarith
  have hb : m+3 ≠ 0 := by linarith
  have hc : m+7 ≠ 0 := by linarith
  have hd : m+8 ≠ 0 := by linarith
  field_simp [ha,hb,hc,hd]
  ring


set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem B3ShiftCoefficient0_reduced (m s : ℝ) (hm : 0 ≤ m) :
    B3ShiftCoefficient 0 m s = (m+4)^3*(LargeLNumerator m s)^0*B3ReducedC0 m s / (8*(m+3)^2*(m+6)^8*(m+7)^3*(m+8)^3) := by
  have ha : m+6 ≠ 0 := by linarith
  have hb : m+3 ≠ 0 := by linarith
  have hc : m+7 ≠ 0 := by linarith
  have hd : m+8 ≠ 0 := by linarith
  calc
    B3ShiftCoefficient 0 m s = (m+4)^3*(LargeLNumerator m s)^0*(8*(LargeLNumerator m s)^0*((m+6)^8*ReducedX3 m s*(LargeK0Numerator m s)^3) + 4*(LargeLNumerator m s)^1*((m+6)^5*ReducedX2 m s*(LargeK0Numerator m s)^2*((m+3)*(m+7)*(m+8))+3*(m+6)^6*ReducedX3 m s*(LargeK0Numerator m s)^2*(ReducedH m s)) + 2*(LargeLNumerator m s)^2*((m+6)^2*ReducedX1 m s*(LargeK0Numerator m s)*((m+3)*(m+7)*(m+8))^2+2*(m+6)^3*ReducedX2 m s*(LargeK0Numerator m s)*(ReducedH m s)*((m+3)*(m+7)*(m+8))+3*(m+6)^4*ReducedX3 m s*(LargeK0Numerator m s)*(ReducedH m s)^2) + 1*(LargeLNumerator m s)^3*(ReducedX0 m s*((m+3)*(m+7)*(m+8))^3+ReducedX1 m s*(ReducedH m s)*((m+3)*(m+7)*(m+8))^2+(m+6)*ReducedX2 m s*(ReducedH m s)^2*((m+3)*(m+7)*(m+8))+(m+6)^2*ReducedX3 m s*(ReducedH m s)^3)) /
        (8*(m+6)^8*((m+3)*(m+7)*(m+8))^3) := by
      simp only [B3ShiftCoefficient, B3Power, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [LargeH_factor m s hm, LargeX0_factor, LargeX1_factor,
          LargeX2_factor, LargeX3_factor]
      field_simp [ha,hb,hc,hd]
      ring
    _ = _ := by
      rw [B3ReducedC0_identity]
      field_simp [ha,hb,hc,hd]

set_option maxRecDepth 100000 in
theorem B3ShiftCoefficient0_nonneg (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ B3ShiftCoefficient 0 m s := by
  rw [B3ShiftCoefficient0_reduced m s hm]
  have hC := B3ReducedC0_nonneg m s hm hs
  have hL : 0 ≤ LargeLNumerator m s := by unfold LargeLNumerator; positivity
  positivity


set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem B3ShiftCoefficient1_reduced (m s : ℝ) (hm : 0 ≤ m) :
    B3ShiftCoefficient 1 m s = (m+4)^3*(LargeLNumerator m s)^1*B3ReducedC1 m s / (8*(m+3)^2*(m+6)^8*(m+7)^3*(m+8)^3) := by
  have ha : m+6 ≠ 0 := by linarith
  have hb : m+3 ≠ 0 := by linarith
  have hc : m+7 ≠ 0 := by linarith
  have hd : m+8 ≠ 0 := by linarith
  calc
    B3ShiftCoefficient 1 m s = (m+4)^3*(LargeLNumerator m s)^1*(4*(LargeLNumerator m s)^0*((m+6)^5*ReducedX2 m s*(LargeK0Numerator m s)^2*((m+3)*(m+7)*(m+8))+3*(m+6)^6*ReducedX3 m s*(LargeK0Numerator m s)^2*(ReducedH m s)) + 4*(LargeLNumerator m s)^1*((m+6)^2*ReducedX1 m s*(LargeK0Numerator m s)*((m+3)*(m+7)*(m+8))^2+2*(m+6)^3*ReducedX2 m s*(LargeK0Numerator m s)*(ReducedH m s)*((m+3)*(m+7)*(m+8))+3*(m+6)^4*ReducedX3 m s*(LargeK0Numerator m s)*(ReducedH m s)^2) + 3*(LargeLNumerator m s)^2*(ReducedX0 m s*((m+3)*(m+7)*(m+8))^3+ReducedX1 m s*(ReducedH m s)*((m+3)*(m+7)*(m+8))^2+(m+6)*ReducedX2 m s*(ReducedH m s)^2*((m+3)*(m+7)*(m+8))+(m+6)^2*ReducedX3 m s*(ReducedH m s)^3)) /
        (8*(m+6)^8*((m+3)*(m+7)*(m+8))^3) := by
      simp only [B3ShiftCoefficient, B3Power, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [LargeH_factor m s hm, LargeX0_factor, LargeX1_factor,
          LargeX2_factor, LargeX3_factor]
      field_simp [ha,hb,hc,hd]
      ring
    _ = _ := by
      rw [B3ReducedC1_identity]
      field_simp [ha,hb,hc,hd]

set_option maxRecDepth 100000 in
theorem B3ShiftCoefficient1_nonneg (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ B3ShiftCoefficient 1 m s := by
  rw [B3ShiftCoefficient1_reduced m s hm]
  have hC := B3ReducedC1_nonneg m s hm hs
  have hL : 0 ≤ LargeLNumerator m s := by unfold LargeLNumerator; positivity
  positivity


set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem B3ShiftCoefficient2_reduced (m s : ℝ) (hm : 0 ≤ m) :
    B3ShiftCoefficient 2 m s = (m+4)^3*(LargeLNumerator m s)^2*B3ReducedC2 m s / (8*(m+3)^2*(m+6)^8*(m+7)^3*(m+8)^3) := by
  have ha : m+6 ≠ 0 := by linarith
  have hb : m+3 ≠ 0 := by linarith
  have hc : m+7 ≠ 0 := by linarith
  have hd : m+8 ≠ 0 := by linarith
  calc
    B3ShiftCoefficient 2 m s = (m+4)^3*(LargeLNumerator m s)^2*(2*(LargeLNumerator m s)^0*((m+6)^2*ReducedX1 m s*(LargeK0Numerator m s)*((m+3)*(m+7)*(m+8))^2+2*(m+6)^3*ReducedX2 m s*(LargeK0Numerator m s)*(ReducedH m s)*((m+3)*(m+7)*(m+8))+3*(m+6)^4*ReducedX3 m s*(LargeK0Numerator m s)*(ReducedH m s)^2) + 3*(LargeLNumerator m s)^1*(ReducedX0 m s*((m+3)*(m+7)*(m+8))^3+ReducedX1 m s*(ReducedH m s)*((m+3)*(m+7)*(m+8))^2+(m+6)*ReducedX2 m s*(ReducedH m s)^2*((m+3)*(m+7)*(m+8))+(m+6)^2*ReducedX3 m s*(ReducedH m s)^3)) /
        (8*(m+6)^8*((m+3)*(m+7)*(m+8))^3) := by
      simp only [B3ShiftCoefficient, B3Power, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [LargeH_factor m s hm, LargeX0_factor, LargeX1_factor,
          LargeX2_factor, LargeX3_factor]
      field_simp [ha,hb,hc,hd]
      ring
    _ = _ := by
      rw [B3ReducedC2_identity]
      field_simp [ha,hb,hc,hd]

set_option maxRecDepth 100000 in
theorem B3ShiftCoefficient2_nonneg (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ B3ShiftCoefficient 2 m s := by
  rw [B3ShiftCoefficient2_reduced m s hm]
  have hC := B3ReducedC2_nonneg m s hm hs
  have hL : 0 ≤ LargeLNumerator m s := by unfold LargeLNumerator; positivity
  positivity


set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem B3ShiftCoefficient3_reduced (m s : ℝ) (hm : 0 ≤ m) :
    B3ShiftCoefficient 3 m s = (m+4)^3*(LargeLNumerator m s)^3*B3ReducedC3 m s / (8*(m+3)^2*(m+6)^8*(m+7)^3*(m+8)^3) := by
  have ha : m+6 ≠ 0 := by linarith
  have hb : m+3 ≠ 0 := by linarith
  have hc : m+7 ≠ 0 := by linarith
  have hd : m+8 ≠ 0 := by linarith
  calc
    B3ShiftCoefficient 3 m s = (m+4)^3*(LargeLNumerator m s)^3*(1*(LargeLNumerator m s)^0*(ReducedX0 m s*((m+3)*(m+7)*(m+8))^3+ReducedX1 m s*(ReducedH m s)*((m+3)*(m+7)*(m+8))^2+(m+6)*ReducedX2 m s*(ReducedH m s)^2*((m+3)*(m+7)*(m+8))+(m+6)^2*ReducedX3 m s*(ReducedH m s)^3)) /
        (8*(m+6)^8*((m+3)*(m+7)*(m+8))^3) := by
      simp only [B3ShiftCoefficient, B3Power, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [LargeH_factor m s hm, LargeX0_factor, LargeX1_factor,
          LargeX2_factor, LargeX3_factor]
      field_simp [ha,hb,hc,hd]
    _ = _ := by
      simp only [pow_zero, one_mul]
      rw [B3ReducedC3_identity]
      field_simp [ha,hb,hc,hd]

set_option maxRecDepth 100000 in
theorem B3ShiftCoefficient3_nonneg (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ B3ShiftCoefficient 3 m s := by
  rw [B3ShiftCoefficient3_reduced m s hm]
  have hC := B3ReducedC3_nonneg m s hm hs
  have hL : 0 ≤ LargeLNumerator m s := by unfold LargeLNumerator; positivity
  positivity

theorem B3_large_nonneg (m s t : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) (ht : 1/2 ≤ t) :
    0 ≤ uniformFaceAPositiveHighVWLargeB3 m s t := by
  let r := 2*t-1
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have htId : t = (1+r)/2 := by dsimp [r]; ring
  rw [htId, B3_shift_eq m s r hm hs]
  have h0 := B3ShiftCoefficient0_nonneg m s hm hs
  have h1 := B3ShiftCoefficient1_nonneg m s hm hs
  have h2 := B3ShiftCoefficient2_nonneg m s hm hs
  have h3 := B3ShiftCoefficient3_nonneg m s hm hs
  positivity

end SSP.K3AllStages
