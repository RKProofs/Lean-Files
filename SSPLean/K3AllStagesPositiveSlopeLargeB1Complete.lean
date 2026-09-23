import SSPLean.K3AllStagesPositiveSlopeLargeB1T3

set_option autoImplicit false
namespace SSP.K3AllStages

theorem uniformFaceAPositiveHighVWLargeB1_nonneg
    (m s t : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (ht : 1/2 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ uniformFaceAPositiveHighVWLargeB1 m s t := by
  let r := 2*t-1
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have htId : t = (1+r)/2 := by dsimp [r]; ring
  rw [htId]
  change 0 ≤ uniformFaceAPositiveHighVWLargeB1R m s r
  rw [uniformFaceAPositiveHighVWLargeB1_bernstein_r]
  exact cornerBern3_nonneg _ _ _ _ r
    (uniformFaceAPositiveHighVWLargeB1T0_nonneg m s hm hs)
    (uniformFaceAPositiveHighVWLargeB1T1_nonneg m s hm hs)
    (uniformFaceAPositiveHighVWLargeB1T2_nonneg m s hm hs)
    (uniformFaceAPositiveHighVWLargeB1T3_nonneg m s hm hs) hr hr1

end SSP.K3AllStages
