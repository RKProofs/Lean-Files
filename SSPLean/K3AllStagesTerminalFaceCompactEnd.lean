import SSPLean.K3AllStagesTerminalFaceCompactDefinitions
set_option autoImplicit false
namespace SSP.K3AllStages
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalEndPositive0 (m _Y : ℝ) : ℝ :=
  1*(m + 6)*(5*m + 16)*(m + 3)^2*(m*(11*m + 57) + 64)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalEndPositive0_nonneg (m Y : ℝ) (hm : 0 ≤ m) (_hY : 0 ≤ Y) :
    0 ≤ TerminalEndPositive0 m Y := by
  unfold TerminalEndPositive0
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalEndPositive1 (m Y : ℝ) : ℝ :=
  (Y^3*(m*(m*(m*(m*(m*(4*m + 120) + 1485) + 9691) + 35126) + 66944) + 52320) + Y^2*(m*(m*(m*(m*(m*(22*m + 562) + 5902) + 32590) + 99724) + 160240) + 105600) + Y*(m*(m*(m*(m*(m*(86*m + 1898) + 17164) + 81640) + 215892) + 301488) + 173952) + m*(m*(m*(m*(m*(220*m + 4484) + 36956) + 158092) + 370488) + 450432) + 221184)/4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalEndPositive1_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalEndPositive1 m Y := by
  unfold TerminalEndPositive1
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalEndPositive2 (m Y : ℝ) : ℝ :=
  (Y^4*(m*(m*(m*(m + 19) + 134) + 416) + 480) + Y^3*(m*(m*(m*(m*(m*(6*m + 174) + 2121) + 13851) + 50838) + 98880) + 79200) + Y^2*(m*(m*(m*(m*(m*(75*m + 1845) + 18723) + 100323) + 299226) + 470736) + 304992) + Y*(m*(m*(m*(m*(m*(258*m + 5694) + 51492) + 244920) + 647676) + 904464) + 521856) + m*(m*(m*(m*(m*(330*m + 6726) + 55434) + 237138) + 555732) + 675648) + 331776)/6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalEndPositive2_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalEndPositive2 m Y := by
  unfold TerminalEndPositive2
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalEndPositive3 (m Y : ℝ) : ℝ :=
  (Y^4*(m*(m*(m*(2*m + 38) + 268) + 832) + 960) + Y^3*(m*(m*(m*(m*(m*(6*m + 150) + 1587) + 9165) + 30570) + 55680) + 42912) + Y^2*(m*(m*(m*(m*(m*(84*m + 2004) + 19740) + 102876) + 299280) + 460752) + 293184) + Y*(m*(m*(m*(m*(m*(258*m + 5694) + 51492) + 244920) + 647676) + 904464) + 521856) + m*(m*(m*(m*(m*(220*m + 4484) + 36956) + 158092) + 370488) + 450432) + 221184)/4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalEndPositive3_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalEndPositive3 m Y := by
  unfold TerminalEndPositive3
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalEndPositive4 (m Y : ℝ) : ℝ :=
  1*(Y^4*(m*(m*(m*(m + 19) + 134) + 416) + 480) + Y^3*(m*(m*(m*(m*(m*(4*m + 96) + 951) + 5005) + 14858) + 23744) + 16032) + Y^2*(m*(m*(m*(m*(m*(31*m + 721) + 6919) + 35143) + 99778) + 150256) + 93792) + Y*(m*(m*(m*(m*(m*(86*m + 1898) + 17164) + 81640) + 215892) + 301488) + 173952) + m*(m*(m*(m*(m*(55*m + 1121) + 9239) + 39523) + 92622) + 112608) + 55296)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalEndPositive4_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalEndPositive4 m Y := by
  unfold TerminalEndPositive4
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalEnd_identity (m a Y : ℝ) :
    uniformFaceBCoreB2 (m+4) a 1 Y = cornerBern4 (TerminalEndPositive0 m Y) (TerminalEndPositive1 m Y) (TerminalEndPositive2 m Y) (TerminalEndPositive3 m Y) (TerminalEndPositive4 m Y) a := by
  unfold uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1 uniformFaceBCoreQ2 cornerBern4 TerminalEndPositive0 TerminalEndPositive1 TerminalEndPositive2 TerminalEndPositive3 TerminalEndPositive4
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalEnd_nonneg (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (hY : 0 ≤ Y) : 0 ≤ uniformFaceBCoreB2 (m+4) a 1 Y := by
  rw [TerminalEnd_identity]
  apply cornerBern4_nonneg <;> try assumption
  · exact TerminalEndPositive0_nonneg m Y hm hY
  · exact TerminalEndPositive1_nonneg m Y hm hY
  · exact TerminalEndPositive2_nonneg m Y hm hY
  · exact TerminalEndPositive3_nonneg m Y hm hY
  · exact TerminalEndPositive4_nonneg m Y hm hY
end SSP.K3AllStages
