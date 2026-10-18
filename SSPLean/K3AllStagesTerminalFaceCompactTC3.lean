import SSPLean.K3AllStagesTerminalFaceCompactDefinitions
set_option autoImplicit false
namespace SSP.K3AllStages
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalTC3Positive0 (m _Y : ℝ) : ℝ :=
  3*(m + 3)^3*(m + 6)*(m*(13*m + 75) + 104)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalTC3Positive0_nonneg (m Y : ℝ) (hm : 0 ≤ m) (_hY : 0 ≤ Y) :
    0 ≤ TerminalTC3Positive0 m Y := by
  unfold TerminalTC3Positive0
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalTC3Positive1 (m Y : ℝ) : ℝ :=
  (Y^3*(m*(m*(m*(m*(m*(7*m + 210) + 2598) + 16945) + 61370) + 116840) + 91200) + Y^2*(m*(m*(m*(m*(m*(32*m + 814) + 8512) + 46814) + 142752) + 228756) + 150480) + Y*(m*(m*(m*(m*(m*(125*m + 2753) + 24817) + 117547) + 309234) + 429156) + 245808) + m*(m*(m*(m*(m*(312*m + 6480) + 54768) + 242208) + 592920) + 763344) + 404352)/8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalTC3Positive1_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalTC3Positive1 m Y := by
  unfold TerminalTC3Positive1
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalTC3Positive2 (m Y : ℝ) : ℝ :=
  (Y^4*(m*(m*(m*(2*m + 38) + 268) + 832) + 960) + Y^3*(m*(m*(m*(m*(m*(10*m + 289) + 3515) + 22928) + 84120) + 163608) + 131040) + Y^2*(m*(m*(m*(m*(m*(117*m + 2859) + 28797) + 153093) + 453042) + 707388) + 455184) + Y*(m*(m*(m*(m*(m*(375*m + 8259) + 74451) + 352641) + 927702) + 1287468) + 737424) + m*(m*(m*(m*(m*(468*m + 9720) + 82152) + 363312) + 889380) + 1145016) + 606528)/12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalTC3Positive2_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalTC3Positive2 m Y := by
  unfold TerminalTC3Positive2
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalTC3Positive3 (m Y : ℝ) : ℝ :=
  (Y^4*(m*(m*(m*(4*m + 76) + 536) + 1664) + 1920) + Y^3*(m*(m*(m*(m*(m*(11*m + 272) + 2836) + 16093) + 52674) + 94200) + 71424) + Y^2*(m*(m*(m*(m*(m*(138*m + 3276) + 32058) + 165744) + 477828) + 728508) + 458928) + Y*(m*(m*(m*(m*(m*(375*m + 8259) + 74451) + 352641) + 927702) + 1287468) + 737424) + m*(m*(m*(m*(m*(312*m + 6480) + 54768) + 242208) + 592920) + 763344) + 404352)/8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalTC3Positive3_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalTC3Positive3 m Y := by
  unfold TerminalTC3Positive3
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalTC3Positive4 (m Y : ℝ) : ℝ :=
  (Y^4*(m*(m*(m*(2*m + 38) + 268) + 832) + 960) + Y^3*(m*(m*(m*(m*(m*(8*m + 193) + 1919) + 10110) + 29924) + 47432) + 31584) + Y^2*(m*(m*(m*(m*(m*(53*m + 1231) + 11773) + 59465) + 167538) + 249876) + 154224) + Y*(m*(m*(m*(m*(m*(125*m + 2753) + 24817) + 117547) + 309234) + 429156) + 245808) + m*(m*(m*(m*(m*(78*m + 1620) + 13692) + 60552) + 148230) + 190836) + 101088)/2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalTC3Positive4_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalTC3Positive4 m Y := by
  unfold TerminalTC3Positive4
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalTC3_identity (m a Y : ℝ) :
    uniformFaceBCoreB2TC3 (m+4) a Y = cornerBern4 (TerminalTC3Positive0 m Y) (TerminalTC3Positive1 m Y) (TerminalTC3Positive2 m Y) (TerminalTC3Positive3 m Y) (TerminalTC3Positive4 m Y) a := by
  unfold uniformFaceBCoreB2TC3 sampledBern4C3 uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1 uniformFaceBCoreQ2 cornerBern4 TerminalTC3Positive0 TerminalTC3Positive1 TerminalTC3Positive2 TerminalTC3Positive3 TerminalTC3Positive4
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalTC3_nonneg (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (hY : 0 ≤ Y) : 0 ≤ uniformFaceBCoreB2TC3 (m+4) a Y := by
  rw [TerminalTC3_identity]
  apply cornerBern4_nonneg <;> try assumption
  · exact TerminalTC3Positive0_nonneg m Y hm hY
  · exact TerminalTC3Positive1_nonneg m Y hm hY
  · exact TerminalTC3Positive2_nonneg m Y hm hY
  · exact TerminalTC3Positive3_nonneg m Y hm hY
  · exact TerminalTC3Positive4_nonneg m Y hm hY
end SSP.K3AllStages
