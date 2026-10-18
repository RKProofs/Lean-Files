import SSPLean.K3AllStagesPositiveSlopeLargeB3Helpers
set_option autoImplicit false
namespace SSP.K3AllStages
set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
noncomputable def LargeB0Positive3 (m s : ℝ) : ℝ :=
  1*(m + 3)^3*(m + 7)^3*(m + 8)^3*(m*(m*(2*m + 35) + 191) + s*(m + 6) + 312)^2*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(16*m + 1360) + 53440) + 1287360) + 21256672) + 254763152) + 2288936032) + 15694427200) + 82780409692) + 335802574236) + 1038890259748) + 2406813813188) + 4041296460096) + 4642610843952) + 3262656965760) + s^4*(m*(m*(m*(m*(m*(m*(m + 37) + 584) + 5096) + 26544) + 82512) + 141696) + 103680) + s^3*(m*(m*(m*(m*(m*(m*(m*(m*(8*m + 392) + 8456) + 105384) + 836048) + 4377424) + 15121632) + 33220800) + 42097536) + 23431680) + s^2*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(24*m + 1464) + 40176) + 654576) + 7033464) + 52319844) + 274853484) + 1019397432) + 2615082624) + 4417767648) + 4421884608) + 1986114816) + s*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(m*(32*m + 2336) + 77920) + 1572064) + 21397536) + 207430224) + 1473019016) + 7756217840) + 30274988488) + 86498716528) + 175791590880) + 240604677504) + 198753810048) + 74830293504) + 1057378204224)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem LargeB0Positive3_identity (m s : ℝ) :
    ((m+3)*(m+7)*(m+8))^3*(ReducedX0 m s) = LargeB0Positive3 m s := by
  simp only [ReducedX0, LargeB0Positive3]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem LargeB0Positive3_nonneg (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ LargeB0Positive3 m s := by
  unfold LargeB0Positive3
  positivity
end SSP.K3AllStages
