import SSPLean.K3AllStages
/-! Compact positive coefficients for the far-tail derivative certificate.
The chart denominators are canceled once, and all identities are kernel checked. -/
set_option autoImplicit false
namespace SSP.K3AllStages
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
noncomputable def TailCompactB0 (m _s : ℝ) : ℝ :=
  m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(2*m + 196) + 17989/2) + 513541/2) + 5108975) + 75224682) + 849295087) + 7516507787) + 52856307946) + 297493596262) + 2686379147669/2) + 9705821162061/2) + 13925247713289) + 31303041061752) + 53911645108416) + 68640713433792) + 60841484702208) + 33504702271488) + 8627797721088

set_option maxRecDepth 100000 in
theorem TailCompactB0_nonneg (m s : ℝ) (hm : 0 ≤ m) (_hs : 0 ≤ s) :
    0 ≤ TailCompactB0 m s := by
  unfold TailCompactB0
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
noncomputable def TailCompactB1 (m s : ℝ) : ℝ :=
  m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(2*m + 196) + 17989/2) + 513541/2) + 5108975) + 75224682) + 849295087) + 7516507787) + 52856307946) + 297493596262) + 2686379147669/2) + 9705821162061/2) + 13925247713289) + 31303041061752) + 53911645108416) + 68640713433792) + 60841484702208) + 33504702271488) + s^4*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m/3 + 64/3) + 616) + 10590) + 120401) + 950234) + 15930884/3) + 63016040/3) + 57612032) + 104300928) + 112121856) + 54190080) + s^3*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(2*m/3 + 152/3) + 5288/3) + 111470/3) + 529342) + 5380132) + 120369364/3) + 666665110/3) + 2741167432/3) + 8261300152/3) + 5910647616) + 8553037440) + 7476295680) + 2980454400) + s^2*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m/2 + 521/12) + 20975/12) + 173125/4) + 2949015/4) + 109836611/12) + 1027092221/12) + 7370788081/12) + 40967701285/12) + 14719715839) + 48959858195) + 371824497784/3) + 699455523352/3) + 313213843520) + 280781972352) + 147715835904) + 33305223168) + s*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m + 593/6) + 9133/2) + 785989/6) + 15679129/6) + 115413827/3) + 2597357747/6) + 3803909652) + 158630297603/6) + 877683428909/6) + 1935123475627/3) + 13549205270567/6) + 18654751892831/3) + 39760135701212/3) + 63941617235288/3) + 24840184572128) + 19618810654464) + 9264206923776) + 1928061370368) + 8627797721088

set_option maxRecDepth 100000 in
theorem TailCompactB1_nonneg (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ TailCompactB1 m s := by
  unfold TailCompactB1
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
noncomputable def TailCompactB2 (m s : ℝ) : ℝ :=
  m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(2*m + 196) + 17989/2) + 513541/2) + 5108975) + 75224682) + 849295087) + 7516507787) + 52856307946) + 297493596262) + 2686379147669/2) + 9705821162061/2) + 13925247713289) + 31303041061752) + 53911645108416) + 68640713433792) + 60841484702208) + 33504702271488) + s^4*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(2*m + 120) + 3250) + 52436) + 559872) + 4152928) + 21832224) + 81322560) + 210283776) + 359396352) + 365285376) + 167215104) + s^3*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(20*m/3 + 1424/3) + 46390/3) + 915364/3) + 12203156/3) + 116045108/3) + 269881726) + 1398473352) + 16142733160/3) + 45542667328/3) + 30518751744) + 41393602560) + 33946380288) + 12711444480) + s^2*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m + 553/6) + 47197/12) + 2475065/24) + 14872675/8) + 97691719/4) + 1450579067/6) + 44127347293/24) + 260423368793/24) + 99657808009/2) + 531992908700/3) + 1450645278124/3) + 2968492488118/3) + 1467347360144) + 1485156254112) + 915145436160) + 258085287936) + s*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(2*m + 593/3) + 9133) + 785989/3) + 15679129/3) + 230827654/3) + 2597357747/3) + 7607819304) + 158630297603/3) + 877683428909/3) + 3870246951254/3) + 13549205270567/3) + 37309503785662/3) + 79520271402424/3) + 127883234470576/3) + 49680369144256) + 39237621308928) + 18528413847552) + 3856122740736) + 8627797721088

set_option maxRecDepth 100000 in
theorem TailCompactB2_nonneg (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ TailCompactB2 m s := by
  unfold TailCompactB2
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
noncomputable def TailCompactB3 (m s : ℝ) : ℝ :=
  m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(2*m + 196) + 17989/2) + 513541/2) + 5108975) + 75224682) + 849295087) + 7516507787) + 52856307946) + 297493596262) + 2686379147669/2) + 9705821162061/2) + 13925247713289) + 31303041061752) + 53911645108416) + 68640713433792) + 60841484702208) + 33504702271488) + s^4*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(5*m + 296) + 7898) + 125354) + 1314673) + 9564010) + 49234108) + 179299096) + 452566848) + 753829632) + 745555968) + 331610112) + s^3*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(18*m + 1272) + 41094) + 803430) + 10603002) + 99716168) + 687339102) + 3514956178) + 13331998416) + 37033258056) + 73211038272) + 97521411456) + 78441613056) + 28771200000) + s^2*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(3*m/2 + 585/4) + 13111/2) + 1436315/8) + 26923935/8) + 91619273/2) + 1874065913/4) + 29385771131/8) + 178487966223/8) + 210655128993/2) + 385113334115) + 1078820780340) + 2269036964766) + 3462400549872) + 3613122845280) + 2302288800768) + 674340194304) + s*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(3*m + 593/2) + 27399/2) + 785989/2) + 15679129/2) + 115413827) + 2597357747/2) + 11411728956) + 158630297603/2) + 877683428909/2) + 1935123475627) + 13549205270567/2) + 18654751892831) + 39760135701212) + 63941617235288) + 74520553716384) + 58856431963392) + 27792620771328) + 5784184111104) + 8627797721088

set_option maxRecDepth 100000 in
theorem TailCompactB3_nonneg (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ TailCompactB3 m s := by
  unfold TailCompactB3
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem TailCompact_identity (m s v : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceANonposXC1 m s v
      +(uniformFaceANonposP m/8)*uniformFaceANonposXC2 m s v =
    cornerBern3 (TailCompactB0 m s) (TailCompactB1 m s)
      (TailCompactB2 m s) (TailCompactB3 m s) v := by
  have h1 : uniformFaceANonposXC1 m s v =
      (-11*uniformFaceANonposScaled m s v 0+18*uniformFaceANonposScaled m s v 1
        -9*uniformFaceANonposScaled m s v 2+2*uniformFaceANonposScaled m s v 3)/6 := by
    unfold uniformFaceANonposXC1 uniformFaceACoreXC1 uniformFaceANonposScaled
    ring
  have h2 : uniformFaceANonposXC2 m s v =
      (2*uniformFaceANonposScaled m s v 0-5*uniformFaceANonposScaled m s v 1
        +4*uniformFaceANonposScaled m s v 2-uniformFaceANonposScaled m s v 3)/2 := by
    unfold uniformFaceANonposXC2 uniformFaceACoreXC2 uniformFaceANonposScaled
    ring
  rw [h1,h2]
  simp only [NonposCompactPolynomial_eq m s _ _ hm hs]
  unfold NonposCompactPolynomial uniformFaceANonposP cornerBern3
  unfold TailCompactB0 TailCompactB1 TailCompactB2 TailCompactB3
  ring
end SSP.K3AllStages
