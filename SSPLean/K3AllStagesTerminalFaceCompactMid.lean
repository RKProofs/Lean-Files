import SSPLean.K3AllStagesTerminalFaceCompactDefinitions
set_option autoImplicit false
namespace SSP.K3AllStages
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalMidPositive0 (m _Y : ℝ) : ℝ :=
  18*(m + 3)^5*(m + 6)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalMidPositive0_nonneg (m Y : ℝ) (hm : 0 ≤ m) (_hY : 0 ≤ Y) :
    0 ≤ TerminalMidPositive0 m Y := by
  unfold TerminalMidPositive0
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalMidPositive1 (m Y : ℝ) : ℝ :=
  (m + 3)*(m + 6)*(Y^3*(m*(m*(m*(5*m + 105) + 820) + 2820) + 3600) + Y^2*(m*(m*(m*(14*m + 222) + 1306) + 3378) + 3240) + Y*(m*(m*(m*(66*m + 858) + 4158) + 8910) + 7128) + m*(m*(m*(108*m + 1296) + 5832) + 11664) + 8748)/6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalMidPositive1_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalMidPositive1 m Y := by
  unfold TerminalMidPositive1
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalMidPositive2 (m Y : ℝ) : ℝ :=
  (m + 6)*(Y^4*(m*(m*(2*m + 26) + 112) + 160) + Y^3*(m*(m*(m*(m*(m + 15) + 119) + 633) + 1872) + 2160) + Y^2*(m*(m*(m*(m*(52*m + 918) + 6452) + 22566) + 39276) + 27216) + Y*(m*(m*(m*(m*(132*m + 2112) + 13464) + 42768) + 67716) + 42768) + m*(m*(m*(m*(108*m + 1620) + 9720) + 29160) + 43740) + 26244)/6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalMidPositive2_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalMidPositive2 m Y := by
  unfold TerminalMidPositive2
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalMidPositive3 (m Y : ℝ) : ℝ :=
  (m + 6)*(Y^4*(m*(m*(2*m + 26) + 112) + 160) + Y^3*(m*(m*(m*(m*(8*m + 147) + 1072) + 3897) + 7092) + 5184) + Y^2*(m*(m*(m*(m*(38*m + 654) + 4480) + 15270) + 25902) + 17496) + Y*(m*(m*(m*(m*(66*m + 1056) + 6732) + 21384) + 33858) + 21384) + m*(m*(m*(m*(36*m + 540) + 3240) + 9720) + 14580) + 8748)/2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalMidPositive3_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalMidPositive3 m Y := by
  unfold TerminalMidPositive3
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalMid_identity (m a Y : ℝ) :
    uniformFaceBCoreB1TC1 (m+4) a Y = cornerBern3 (TerminalMidPositive0 m Y) (TerminalMidPositive1 m Y) (TerminalMidPositive2 m Y) (TerminalMidPositive3 m Y) a := by
  unfold uniformFaceBCoreB1TC1 uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1 cornerBern3 TerminalMidPositive0 TerminalMidPositive1 TerminalMidPositive2 TerminalMidPositive3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalMid_nonneg (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (hY : 0 ≤ Y) : 0 ≤ uniformFaceBCoreB1TC1 (m+4) a Y := by
  rw [TerminalMid_identity]
  apply cornerBern3_nonneg <;> try assumption
  · exact TerminalMidPositive0_nonneg m Y hm hY
  · exact TerminalMidPositive1_nonneg m Y hm hY
  · exact TerminalMidPositive2_nonneg m Y hm hY
  · exact TerminalMidPositive3_nonneg m Y hm hY
end SSP.K3AllStages
