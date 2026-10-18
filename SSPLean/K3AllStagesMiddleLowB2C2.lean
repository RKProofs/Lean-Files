import SSPLean.K3AllStagesMiddleLowBase
set_option autoImplicit false
namespace SSP.K3AllStages
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def MiddleLowB2Positive2 (m s : ℝ) : ℝ :=
  (m + 7)*(m + 8)*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(24*m + 1572) + 48978) + 979122) + 14276820) + 162772668) + 1507690308) + 11570683764) + 74244669840) + 399147884988) + 1788548203338) + 6587032792122) + 19478728697076) + 44750531769012) + 76338203784624) + 90397989936720) + 65998483423488) + s^6*(m*(m*(m*(m*(m*(m*(3*m + 111) + 1752) + 15288) + 79632) + 247536) + 425088) + 311040) + s^5*(m*(m*(m*(m*(m*(m*(m*(m*(24*m + 1170) + 25128) + 311982) + 2467056) + 12881280) + 44392032) + 97327008) + 123120000) + 68428800) + s^4*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(96*m + 5616) + 149343) + 2378991) + 25183167) + 185726859) + 972442008) + 3610281816) + 9303719616) + 15834433392) + 16005107520) + 7273483776) + s^3*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(208*m + 14368) + 458300) + 8929388) + 118423402) + 1127387134) + 7914955770) + 41433707022) + 161517032288) + 462518055464) + 944704750320) + 1302179011200) + 1084898774592) + 412377433344) + s^2*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(220*m + 17788) + 672371) + 15719747) + 253615265) + 2984759917) + 26426576889) + 179005245965) + 934363587659) + 3755731251487) + 11525527206476) + 26513443049336) + 44258448740160) + 50621677182576) + 35486682389568) + 11499301494720) + s*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(88*m + 8152) + 358976) + 9912512) + 191114136) + 2717798080) + 29423248872) + 247170838992) + 1629180450880) + 8470153637128) + 34741306396776) + 111860498630000) + 279614626034864) + 532112622788192) + 745991043329040) + 727676296994304) + 442025784084096) + 126192772371456) + 22298024383488)/9

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem MiddleLowB2Positive2_eq (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformCubicSampleB2 (fun v => uniformFaceANonposMiddleLowB2 m s v) =
      MiddleLowB2Positive2 m s := by
  unfold uniformCubicSampleB2 uniformFaceANonposMiddleLowB2 uniformFaceANonposMiddleLow
  simp only [uniformCubicSampleB2, NonposCompactPolynomial_eq m s _ _ hm hs]
  unfold NonposCompactPolynomial MiddleLowB2Positive2
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem MiddleLowB2Positive2_nonneg (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ MiddleLowB2Positive2 m s := by
  unfold MiddleLowB2Positive2
  positivity
end SSP.K3AllStages
