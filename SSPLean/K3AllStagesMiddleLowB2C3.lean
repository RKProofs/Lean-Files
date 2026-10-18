import SSPLean.K3AllStagesMiddleLowBase
set_option autoImplicit false
namespace SSP.K3AllStages
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def MiddleLowB2Positive3 (m s : ℝ) : ℝ :=
  (m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(8*m + 644) + 24634) + 600608) + 10568806) + 143918600) + 1582927416) + 14433769264) + 110745194516) + 720258741124) + 3977822663066) + 18589179133840) + 72814306655278) + 235268432861328) + 612801662452020) + 1247166941923584) + 1898969248137744) + 2024854237397376) + 1343461812489216) + s^6*(m*(m*(m*(m*(m*(m*(m*(m*(3*m + 156) + 3585) + 47784) + 407064) + 2298144) + 8597520) + 20549376) + 28470528) + 17418240) + s^5*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(24*m + 1530) + 44022) + 754422) + 8553954) + 67358112) + 375766368) + 1484559168) + 4068978912) + 7365541248) + 7921152000) + 3832012800) + s^4*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(88*m + 6478) + 219696) + 4541352) + 63781984) + 642141568) + 4763440992) + 26337375630) + 108444395212) + 328145635192) + 708717149904) + 1033804517184) + 912249851904) + 367545931776) + s^3*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(168*m + 14052) + 548442) + 13243572) + 221130870) + 2702125162) + 24939258714) + 176849833420) + 970432441638) + 4116277282618) + 13372680026664) + 32645269987896) + 57916728649440) + 70441278906816) + 52483109497344) + 18047450778624) + s^2*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(150*m + 14232) + 636017) + 17761712) + 346765322) + 5016665872) + 55624680768) + 482300759556) + 3307289318812) + 18022158414040) + 77978717670295) + 266204249419364) + 707845785333516) + 1434700148427816) + 2139973083136368) + 2213112024359424) + 1416803137155648) + 422781210948096) + s*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(44*m + 4736) + 243092) + 7876832) + 179952236) + 3069805396) + 40446305844) + 420358132276) + 3492222486296) + 23374713691940) + 126513858101488) + 553654349130404) + 1951517631852160) + 5495259968295576) + 12193049721552152) + 20857924411534328) + 26566334332712448) + 23753226082656960) + 13323167747140608) + 3533397626400768) + 416229788491776)/3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem MiddleLowB2Positive3_eq (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformCubicSampleB3 (fun v => uniformFaceANonposMiddleLowB2 m s v) =
      MiddleLowB2Positive3 m s := by
  unfold uniformCubicSampleB3 uniformFaceANonposMiddleLowB2 uniformFaceANonposMiddleLow
  simp only [uniformCubicSampleB2, NonposCompactPolynomial_eq m s _ _ hm hs]
  unfold NonposCompactPolynomial MiddleLowB2Positive3
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem MiddleLowB2Positive3_nonneg (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ MiddleLowB2Positive3 m s := by
  unfold MiddleLowB2Positive3
  positivity
end SSP.K3AllStages
