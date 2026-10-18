import SSPLean.K3AllStagesTerminalFaceCompactDefinitions
set_option autoImplicit false
namespace SSP.K3AllStages
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalTC2Positive0 (m _Y : ℝ) : ℝ :=
  2*(m + 3)^3*(m + 6)*(m*(40*m + 237) + 347)/3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalTC2Positive0_nonneg (m Y : ℝ) (hm : 0 ≤ m) (_hY : 0 ≤ Y) :
    0 ≤ TerminalTC2Positive0 m Y := by
  unfold TerminalTC2Positive0
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalTC2Positive1 (m Y : ℝ) : ℝ :=
  (Y^3*(m*(m*(m*(m*(m*(18*m + 540) + 6679) + 43543) + 157598) + 299792) + 233760) + Y^2*(m*(m*(m*(m*(m*(66*m + 1666) + 17290) + 94422) + 286148) + 456248) + 299040) + Y*(m*(m*(m*(m*(m*(272*m + 5984) + 53860) + 254632) + 668436) + 925488) + 528768) + m*(m*(m*(m*(m*(640*m + 13392) + 114272) + 511392) + 1270080) + 1663632) + 899424)/24

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalTC2Positive1_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalTC2Positive1 m Y := by
  unfold TerminalTC2Positive1
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalTC2Positive2 (m Y : ℝ) : ℝ :=
  (Y^4*(m*(m*(m*(2*m + 38) + 268) + 832) + 960) + Y^3*(m*(m*(m*(m*(m*(8*m + 230) + 2789) + 18173) + 66698) + 129872) + 104160) + Y^2*(m*(m*(m*(m*(m*(89*m + 2155) + 21489) + 113045) + 331022) + 511672) + 326208) + Y*(m*(m*(m*(m*(m*(272*m + 5984) + 53860) + 254632) + 668436) + 925488) + 528768) + m*(m*(m*(m*(m*(320*m + 6696) + 57136) + 255696) + 635040) + 831816) + 449712)/12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalTC2Positive2_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalTC2Positive2 m Y := by
  unfold TerminalTC2Positive2
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalTC2Positive3 (m Y : ℝ) : ℝ :=
  (Y^4*(m*(m*(m*(12*m + 228) + 1608) + 4992) + 5760) + Y^3*(m*(m*(m*(m*(m*(30*m + 732) + 7497) + 41625) + 133026) + 232368) + 172512) + Y^2*(m*(m*(m*(m*(m*(336*m + 7932) + 77064) + 395004) + 1127688) + 1701288) + 1060128) + Y*(m*(m*(m*(m*(m*(816*m + 17952) + 161580) + 763896) + 2005308) + 2776464) + 1586304) + m*(m*(m*(m*(m*(640*m + 13392) + 114272) + 511392) + 1270080) + 1663632) + 899424)/24

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalTC2Positive3_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalTC2Positive3 m Y := by
  unfold TerminalTC2Positive3
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def TerminalTC2Positive4 (m Y : ℝ) : ℝ :=
  (Y^4*(m*(m*(m*(6*m + 114) + 804) + 2496) + 2880) + Y^3*(m*(m*(m*(m*(m*(24*m + 582) + 5809) + 30649) + 90530) + 142544) + 93792) + Y^2*(m*(m*(m*(m*(m*(135*m + 3133) + 29887) + 150291) + 420770) + 622520) + 380544) + Y*(m*(m*(m*(m*(m*(272*m + 5984) + 53860) + 254632) + 668436) + 925488) + 528768) + m*(m*(m*(m*(m*(160*m + 3348) + 28568) + 127848) + 317520) + 415908) + 224856)/6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalTC2Positive4_nonneg (m Y : ℝ) (hm : 0 ≤ m) (hY : 0 ≤ Y) :
    0 ≤ TerminalTC2Positive4 m Y := by
  unfold TerminalTC2Positive4
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalTC2_identity (m a Y : ℝ) :
    uniformFaceBCoreB2TC2 (m+4) a Y = cornerBern4 (TerminalTC2Positive0 m Y) (TerminalTC2Positive1 m Y) (TerminalTC2Positive2 m Y) (TerminalTC2Positive3 m Y) (TerminalTC2Positive4 m Y) a := by
  unfold uniformFaceBCoreB2TC2 sampledBern4C2 uniformFaceBCoreB2 uniformFaceBCoreQ0 uniformFaceBCoreQ1 uniformFaceBCoreQ2 cornerBern4 TerminalTC2Positive0 TerminalTC2Positive1 TerminalTC2Positive2 TerminalTC2Positive3 TerminalTC2Positive4
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem TerminalTC2_nonneg (m a Y : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (hY : 0 ≤ Y) : 0 ≤ uniformFaceBCoreB2TC2 (m+4) a Y := by
  rw [TerminalTC2_identity]
  apply cornerBern4_nonneg <;> try assumption
  · exact TerminalTC2Positive0_nonneg m Y hm hY
  · exact TerminalTC2Positive1_nonneg m Y hm hY
  · exact TerminalTC2Positive2_nonneg m Y hm hY
  · exact TerminalTC2Positive3_nonneg m Y hm hY
  · exact TerminalTC2Positive4_nonneg m Y hm hY
end SSP.K3AllStages
