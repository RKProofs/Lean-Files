import SSPLean.K3AllStagesTerminalFaceCompactMid
import SSPLean.K3AllStagesTerminalFaceCompactOne
import SSPLean.K3AllStagesTerminalFaceCompactTC2
import SSPLean.K3AllStagesTerminalFaceCompactTC3
import SSPLean.K3AllStagesTerminalFaceCompactEnd
set_option autoImplicit false
namespace SSP.K3AllStages
theorem uniformFaceBCoreB1TC1_bernstein_a (m a Y : ℝ) :
    uniformFaceBCoreB1TC1 (m+4) a Y =
      cornerBern3 (uniformFaceBCoreB1TC1 (m+4) 0 Y)
        (sampledBern3C1 (uniformFaceBCoreB1TC1 (m+4) 0 Y)
          (uniformFaceBCoreB1TC1 (m+4) 1 Y)
          (uniformFaceBCoreB1TC1 (m+4) 2 Y)
          (uniformFaceBCoreB1TC1 (m+4) 3 Y))
        (sampledBern3C2 (uniformFaceBCoreB1TC1 (m+4) 0 Y)
          (uniformFaceBCoreB1TC1 (m+4) 1 Y)
          (uniformFaceBCoreB1TC1 (m+4) 2 Y)
          (uniformFaceBCoreB1TC1 (m+4) 3 Y))
        (uniformFaceBCoreB1TC1 (m+4) 1 Y) a := by
  unfold uniformFaceBCoreB1TC1 sampledBern3C1 sampledBern3C2
  unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1 cornerBern3
  ring

theorem uniformFaceBCoreB1TC1_nonneg
    (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1TC1 (m+4) a Y := by
  exact TerminalMid_nonneg m a Y hm ha ha1 hY

theorem uniformFaceBCoreB1_bernstein_T (n a T Y : ℝ) :
    uniformFaceBCoreB1 n a T Y =
      cornerBern2 (uniformFaceBCoreB1 n a 0 Y)
        (uniformFaceBCoreB1TC1 n a Y)
        (uniformFaceBCoreB1 n a 1 Y) T := by
  unfold uniformFaceBCoreB1TC1 uniformFaceBCoreB1
  unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1 cornerBern2
  ring

theorem uniformFaceBCoreB1_at_T_one_nonneg
    (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1 (m+4) a 1 Y := by
  exact TerminalOne_nonneg m a Y hm ha ha1 hY

theorem uniformFaceBCoreB1_nonneg_of_T_le_one
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1 n a T Y := by
  let m := n-4
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  rw [← hnid, uniformFaceBCoreB1_bernstein_T]
  apply cornerBern2_nonneg <;> try assumption
  · have hzero : uniformFaceBCoreB1 (m+4) a 0 Y =
        uniformFaceBCoreB0 (m+4) a 0 Y := by
      unfold uniformFaceBCoreB1 uniformFaceBCoreB0
      unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1
      ring
    rw [hzero]
    exact uniformFaceBCoreB0_nonneg (m+4) a 0 Y (by linarith) ha ha1 hY
  · exact uniformFaceBCoreB1TC1_nonneg m a Y hm ha ha1 hY
  · exact uniformFaceBCoreB1_at_T_one_nonneg m a Y hm ha ha1 hY

theorem uniformFaceBCoreB2_bernstein_T (n a T Y : ℝ) :
    uniformFaceBCoreB2 n a T Y =
      cornerBern4 (uniformFaceBCoreB2 n a 0 Y)
        (uniformFaceBCoreB2TC1 n a Y) (uniformFaceBCoreB2TC2 n a Y)
        (uniformFaceBCoreB2TC3 n a Y) (uniformFaceBCoreB2 n a 1 Y) T := by
  unfold uniformFaceBCoreB2TC1 uniformFaceBCoreB2TC2
  unfold uniformFaceBCoreB2TC3 sampledBern4C1 sampledBern4C2 sampledBern4C3
  unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1
  unfold uniformFaceBCoreQ2 cornerBern4
  ring

theorem uniformFaceBCoreB2TC1_eq_B1TC1 (n a Y : ℝ) :
    uniformFaceBCoreB2TC1 n a Y = uniformFaceBCoreB1TC1 n a Y := by
  unfold uniformFaceBCoreB2TC1 uniformFaceBCoreB1TC1 sampledBern4C1
  unfold uniformFaceBCoreB2 uniformFaceBCoreB1
  unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1 uniformFaceBCoreQ2
  ring

set_option maxHeartbeats 3000000 in
theorem uniformFaceBCoreB2TC2_nonneg
    (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB2TC2 (m+4) a Y := by
  exact TerminalTC2_nonneg m a Y hm ha ha1 hY

set_option maxHeartbeats 3000000 in
theorem uniformFaceBCoreB2TC3_nonneg
    (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB2TC3 (m+4) a Y := by
  exact TerminalTC3_nonneg m a Y hm ha ha1 hY

set_option maxHeartbeats 3000000 in
theorem uniformFaceBCoreB2_at_T_one_nonneg
    (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB2 (m+4) a 1 Y := by
  exact TerminalEnd_nonneg m a Y hm ha ha1 hY

theorem uniformFaceBCoreB2_nonneg_of_T_le_one
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB2 n a T Y := by
  let m := n-4
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  rw [← hnid, uniformFaceBCoreB2_bernstein_T]
  apply cornerBern4_nonneg <;> try assumption
  · have hzero : uniformFaceBCoreB2 (m+4) a 0 Y =
        uniformFaceBCoreB0 (m+4) a 0 Y := by
      unfold uniformFaceBCoreB2 uniformFaceBCoreB0
      unfold uniformFaceBCoreQ0 uniformFaceBCoreQ1 uniformFaceBCoreQ2
      ring
    rw [hzero]
    exact uniformFaceBCoreB0_nonneg (m+4) a 0 Y (by linarith) ha ha1 hY
  · rw [uniformFaceBCoreB2TC1_eq_B1TC1]
    exact uniformFaceBCoreB1TC1_nonneg m a Y hm ha ha1 hY
  · exact uniformFaceBCoreB2TC2_nonneg m a Y hm ha ha1 hY
  · exact uniformFaceBCoreB2TC3_nonneg m a Y hm ha ha1 hY
  · exact uniformFaceBCoreB2_at_T_one_nonneg m a Y hm ha ha1 hY

theorem uniformFaceBCore_nonneg_of_T_le_one
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hY : 0 ≤ Y)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ uniformFaceBCore n a T Y q := by
  apply uniformFaceBCore_nonneg_of_bernstein n a T Y q hq hq1
  · exact uniformFaceBCoreB0_nonneg n a T Y hn ha ha1 hY
  · exact uniformFaceBCoreB1_nonneg_of_T_le_one n a T Y hn ha ha1 hT hT1 hY
  · exact uniformFaceBCoreB2_nonneg_of_T_le_one n a T Y hn ha ha1 hT hT1 hY

/-- The entire compact terminal-scale range is unconditional. -/
theorem uniformSharpFaceB_nonneg_of_T_le_one
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (hY : 0 < Y)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    0 ≤ uniformSharpFaceB n a T Y q := by
  apply uniformSharpFaceB_nonneg_of_core n a T Y q hn ha hT hY hq
  exact uniformFaceBCore_nonneg_of_T_le_one
    n a T Y q hn ha.le ha1 hT.le hT1 hY.le hq.le hq1


end SSP.K3AllStages
