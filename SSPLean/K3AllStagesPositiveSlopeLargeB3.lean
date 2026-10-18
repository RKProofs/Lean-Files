import SSPLean.K3AllStagesPositiveSlopeLargeB2Complete
import SSPLean.K3AllStagesPositiveSlopeLargeB3Certificate

/-!
# Right endpoint coefficient of the large-ratio positive-slope chart

At `w = 1` the final cubic Bernstein coefficient is again nonnegative after
translating the large-ratio interval by `t = (1+r)/2`.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem uniformFaceAPositiveHighVWLargeB3_nonneg
    (m s t : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) (ht : 1/2 ≤ t) :
    0 ≤ uniformFaceAPositiveHighVWLargeB3 m s t := by
  exact B3_large_nonneg m s t hm hs ht

end SSP.K3AllStages
