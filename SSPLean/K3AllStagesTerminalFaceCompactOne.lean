import SSPLean.K3AllStagesTerminalFaceCompactDefinitions
set_option autoImplicit false
namespace SSP.K3AllStages
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalOnePositive0 (m _Y : ℝ) : ℝ :=
  2*(m + 3)^3*(m + 6)*(m*(13*m + 75) + 104)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalOnePositive0_nonneg (m Y : ℝ) (hm : 0 ≤ m) (_hY : 0 ≤ Y) :
    0 ≤ TerminalOnePositive0 m Y := by
  unfold TerminalOnePositive0
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalOnePositive1 (m Y : ℝ) : ℝ :=
  (Y^3*(m*(m*(m*(m*(m*(6*m + 180) + 2227) + 14527) + 52622) + 100208) + 78240) + Y^2*(m*(m*(m*(m*(m*(18*m + 442) + 4450) + 23502) + 68636) + 105032) + 65760) + Y*(m*(m*(m*(m*(m*(92*m + 2024) + 18220) + 86152) + 226176) + 313128) + 178848) + m*(m*(m*(m*(m*(156*m + 3240) + 27384) + 121104) + 296460) + 381672) + 202176)/6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalOnePositive1_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalOnePositive1 m Y := by
  unfold TerminalOnePositive1
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalOnePositive2 (m Y : ℝ) : ℝ :=
  (Y^4*(m*(m*(m*(m + 19) + 134) + 416) + 480) + Y^3*(m*(m*(m*(m*(m*(m + 25) + 282) + 1842) + 7172) + 15248) + 13440) + Y^2*(m*(m*(m*(m*(m*(33*m + 781) + 7597) + 38913) + 110756) + 166136) + 102624) + Y*(m*(m*(m*(m*(m*(92*m + 2024) + 18220) + 86152) + 226176) + 313128) + 178848) + m*(m*(m*(m*(m*(78*m + 1620) + 13692) + 60552) + 148230) + 190836) + 101088)/3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalOnePositive2_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalOnePositive2 m Y := by
  unfold TerminalOnePositive2
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalOnePositive3 (m Y : ℝ) : ℝ :=
  (Y^4*(m*(m*(m*(2*m + 38) + 268) + 832) + 960) + Y^3*(m*(m*(m*(m*(m*(8*m + 194) + 1937) + 10229) + 30266) + 47792) + 31584) + Y^2*(m*(m*(m*(m*(m*(48*m + 1120) + 10744) + 54324) + 152876) + 227240) + 139488) + Y*(m*(m*(m*(m*(m*(92*m + 2024) + 18220) + 86152) + 226176) + 313128) + 178848) + m*(m*(m*(m*(m*(52*m + 1080) + 9128) + 40368) + 98820) + 127224) + 67392)/2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalOnePositive3_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalOnePositive3 m Y := by
  unfold TerminalOnePositive3
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalOne_identity (m a Y : ℝ) :
    uniformFaceBCoreB1 (m+4) a 1 Y = cornerBern3 (TerminalOnePositive0 m Y) (TerminalOnePositive1 m Y) (TerminalOnePositive2 m Y) (TerminalOnePositive3 m Y) a := by
  unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1 cornerBern3 TerminalOnePositive0 TerminalOnePositive1 TerminalOnePositive2 TerminalOnePositive3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalOne_nonneg (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (hY : 0 ≤ Y) : 0 ≤ uniformFaceBCoreB1 (m+4) a 1 Y := by
  rw [TerminalOne_identity]
  apply cornerBern3_nonneg <;> try assumption
  · exact TerminalOnePositive0_nonneg m Y hm hY
  · exact TerminalOnePositive1_nonneg m Y hm hY
  · exact TerminalOnePositive2_nonneg m Y hm hY
  · exact TerminalOnePositive3_nonneg m Y hm hY
end SSP.K3AllStages
