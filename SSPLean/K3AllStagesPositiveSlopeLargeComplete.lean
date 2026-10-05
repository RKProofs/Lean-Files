import SSPLean.K3AllStagesPositiveSlopeLargeB3
import SSPLean.K3AllStagesPositiveSlopeLargeB1Complete
import SSPLean.K3AllStagesPositiveSlopeLargeB0

/-!
# Completion of the large-ratio positive-slope chart

The serialized coefficient certificates are assembled first in the face
coordinate.  The resulting endpoint certificate supplies the last
`q`-Bernstein coefficient of the original return-face core.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

/-- The denominator-cleared `q = 1` endpoint is nonnegative throughout the
large-ratio chart. -/
theorem uniformFaceAPositiveHighVWLargeEndpoint_nonneg
    (m s w t : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (ht : 1/2 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ uniformFaceAPositiveHighVWLargeEndpoint m s w t := by
  rw [uniformFaceAPositiveHighVWLarge_bernstein_w]
  exact cornerBern3_nonneg _ _ _ _ w
    (uniformFaceAPositiveHighVWLargeB0_nonneg m s t hm hs ht)
    (uniformFaceAPositiveHighVWLargeB1_nonneg m s t hm hs ht ht1)
    (uniformFaceAPositiveHighVWLargeB2_nonneg m s t hm hs ht ht1)
    (uniformFaceAPositiveHighVWLargeB3_nonneg m s t hm hs ht) hw hw1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
/-- The high-`z` chart `v = w*t` is nonnegative when `1/2 ≤ t ≤ 1`. -/
theorem uniformFaceAPositiveHighVWLarge_nonneg
    (m s v t w : ℝ)
    (hm : 0 ≤ m) (hs : 0 ≤ s) (hv : 0 < v) (hv1 : v ≤ 1)
    (ht : 1/2 ≤ t) (ht1 : t ≤ 1) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hvt : v = w*t) :
    0 ≤ uniformFaceACurrentPoly (m+4) (uniformFaceANonposT m s)
      (uniformFaceAPositiveQ m s v) w := by
  subst v
  let n := m+4
  let T := uniformFaceANonposT m s
  let L := uniformFaceACurrentM n T 1
  let q := uniformFaceAPositiveQ m s (w*t)
  let K := uniformFaceACurrentK n T q
  let X := K/(t*n*L)
  have hn : 4 ≤ n := by dsimp [n]; linarith
  have hnpos : 0 < n := by linarith
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hwpos : 0 < w := by
    by_contra hnw
    have hw0 : w = 0 := le_antisymm (le_of_not_gt hnw) hw
    subst w
    norm_num at hv
  have hT : 0 < T := by
    dsimp [T]
    exact uniformFaceANonposT_pos m s hm hs
  have hTge : n-1 ≤ T := by
    have hz : 0 ≤ uniformFaceANonposZ m s := by
      unfold uniformFaceANonposZ uniformFaceANonposP
      positivity
    dsimp [n, T]
    unfold uniformFaceANonposT
    linarith
  have hL : 0 < L := by
    have hz : 0 ≤ uniformFaceANonposZ m s := by
      unfold uniformFaceANonposZ uniformFaceANonposP
      positivity
    dsimp [L, n, T]
    simpa [uniformFaceALargeM, uniformFaceACurrentM,
      uniformFaceANonposT] using
      uniformFaceALargeM_pos m (uniformFaceANonposZ m s) hm hz
  have hq : 0 ≤ q ∧ q ≤ 1 := by
    dsimp [q]
    exact uniformFaceAPositiveQ_mem_unit m s (w*t) hm hs hv.le hv1
  have hK : 0 < K := by
    dsimp [K]
    exact uniformFaceACurrentK_pos n T q hn hTge hq.1 hq.2
  have hX : 0 < X := by dsimp [X]; positivity
  have hendpoint := uniformFaceAPositiveHighVWLargeEndpoint_nonneg
    m s w t hm hs hw hw1 ht ht1
  have hendpointId :
      uniformFaceAPositiveHighVWLargeEndpoint m s w t =
        (t*n*L)^3 * uniformFaceAQB3 n X T := by
    change
      t^3*n^3*L^3*uniformFaceACoreXC0 n T 1
        + t^2*n^2*L^2*K*uniformFaceACoreXC1 n T 1
        + t*n*L*K^2*uniformFaceACoreXC2 n T 1
        + K^3*uniformFaceACoreXC3 n T 1 =
      (t*n*L)^3 * uniformFaceACore n (K/(t*n*L)) T 1
    unfold uniformFaceACoreXC0 uniformFaceACoreXC1
    unfold uniformFaceACoreXC2 uniformFaceACoreXC3 uniformFaceACore
    field_simp [htpos.ne', hnpos.ne', hL.ne']
    ring
  have h3 : 0 ≤ uniformFaceAQB3 n X T := by
    rw [hendpointId] at hendpoint
    have hscale : 0 < (t*n*L)^3 := by positivity
    exact (mul_nonneg_iff_of_pos_left hscale).mp hendpoint
  have hcore : 0 ≤ uniformFaceACore n X T q :=
    uniformFaceACore_nonneg_of_q_bernstein n X T q hn hX.le hq.1 hq.2
      (uniformFaceAQB1_nonneg n X T hn hX.le hT.le)
      (uniformFaceAQB2_nonneg n X T hn hX.le hT.le) h3
  have hMqId : uniformFaceACurrentM n T q = w*t*L := by
    dsimp [n, T, q, L]
    exact uniformFaceACurrentM_positiveQ m s (w*t) hm hs
  have hMq : 0 < uniformFaceACurrentM n T q := by
    rw [hMqId]
    positivity
  have hXid : w*K/(n*uniformFaceACurrentM n T q) = X := by
    rw [hMqId]
    dsimp [X]
    field_simp [hwpos.ne', htpos.ne', hnpos.ne', hL.ne']
  rw [← uniformFaceACurrentScaled_eq_poly n T q w hnpos.ne' hMq.ne']
  unfold uniformFaceACurrentScaled
  rw [hXid]
  positivity

/-- Positive-current-slope assembly after discharging the large-ratio chart.
Only the low chart and the small-ratio high chart remain as certificates. -/
theorem uniformFaceAPositive_poly_nonneg_of_remaining_chart_certificates
    (m z q w : ℝ)
    (hm : 0 ≤ m) (hz : 0 ≤ z) (hq : 0 < q) (hq1 : q ≤ 1)
    (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hM : 0 < uniformFaceACurrentM (m + 4) (m + 3 + z) q)
    (hgrad : uniformFaceACurrentGradPoly (m + 4) (m + 3 + z) q w < 0)
    (hLow : ∀ m u q w : ℝ,
      0 ≤ m → 0 ≤ u → u ≤ 1 → 0 < q → q ≤ 1 →
      0 ≤ w → w ≤ 1 →
      uniformFaceACurrentGradPoly (m + 4)
          (m + 3 + uniformFaceAPositiveLowZ m u) q w < 0 →
      0 ≤ uniformFaceACurrentPoly (m + 4)
          (m + 3 + uniformFaceAPositiveLowZ m u) q w)
    (hHighVWSmall : ∀ m s v t w : ℝ,
      0 ≤ m → 0 ≤ s → 0 < v → v ≤ 1 →
      0 < t → t < 1 / 2 → 0 ≤ w → w ≤ 1 → v = w * t →
      uniformFaceACurrentGradPoly (m + 4) (uniformFaceANonposT m s)
          (uniformFaceAPositiveQ m s v) w < 0 →
      0 ≤ uniformFaceACurrentPoly (m + 4) (uniformFaceANonposT m s)
          (uniformFaceAPositiveQ m s v) w) :
    0 ≤ uniformFaceACurrentPoly (m + 4) (m + 3 + z) q w := by
  apply uniformFaceAPositive_poly_nonneg_of_chart_certificates
    m z q w hm hz hq hq1 hw hw1 hM hgrad hLow hHighVWSmall
  intro m s v t w hm hs hv hv1 ht ht1 hw hw1 hvt
  exact uniformFaceAPositiveHighVWLarge_nonneg
    m s v t w hm hs hv hv1 ht ht1 hw hw1 hvt

end SSP.K3AllStages
