import SSPLean.K3AllStagesPositiveSlopeLarge

/-!
# Reduction of the small-ratio positive-slope chart

For `v = w*t`, both the face polynomial and its active-gradient polynomial
have a removable power of `w`.  This file isolates the remaining implication
between the resulting quadratic gradient and the `q = 1` endpoint.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

/-- The quadratic left after removing `w^2` from the active gradient in the
chart `v = w*t`. -/
noncomputable def uniformFaceAPositiveHighVWSmallGrad
    (m s w t : ℝ) : ℝ :=
  let n := m + 4
  let T := uniformFaceANonposT m s
  let L := uniformFaceACurrentM n T 1
  let q := uniformFaceAPositiveQ m s (w*t)
  let K := uniformFaceACurrentK n T q
  K^2 + t*L*K*uniformGradACurrentC1 n T q
    + n*t^2*L^2*uniformGradACurrentC0 n T q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem uniformFaceAPositiveHighVWSmall_grad_factor
    (m s w t : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceACurrentGradPoly (m+4) (uniformFaceANonposT m s)
        (uniformFaceAPositiveQ m s (w*t)) w =
      w^2 * uniformFaceAPositiveHighVWSmallGrad m s w t := by
  unfold uniformFaceACurrentGradPoly
  rw [uniformFaceACurrentM_positiveQ m s (w*t) hm hs]
  unfold uniformFaceAPositiveHighVWSmallGrad
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
/-- Once the `q = 1` endpoint is nonnegative, the global `q`-Bernstein
lemmas imply nonnegativity of the original face polynomial in the chart
`v = w*t`. -/
theorem uniformFaceAPositiveHighVW_nonneg_of_endpoint
    (m s v t w : ℝ)
    (hm : 0 ≤ m) (hs : 0 ≤ s) (hv : 0 < v) (hv1 : v ≤ 1)
    (ht : 0 < t) (hw : 0 ≤ w) (hw1 : w ≤ 1) (hvt : v = w*t)
    (hendpoint : 0 ≤ uniformFaceAPositiveHighVWLargeEndpoint m s w t) :
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
    field_simp [ht.ne', hnpos.ne', hL.ne']
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
    field_simp [hwpos.ne', ht.ne', hnpos.ne', hL.ne']
  rw [← uniformFaceACurrentScaled_eq_poly n T q w hnpos.ne' hMq.ne']
  unfold uniformFaceACurrentScaled
  rw [hXid]
  positivity

/-! ### Positivity of the high-chart endpoint

After the high-`z` substitution, the constant, quadratic, and cubic
coefficients of the `q = 1` core are positive.  Its only negative monomial
coefficient is the linear one, and the following discriminant certificate
shows that the constant and quadratic terms dominate it. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceAPositiveHigh_qOne_C2_pos
    (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 < uniformFaceACoreXC2 (m + 4) (uniformFaceANonposT m s) 1 := by
  unfold uniformFaceACoreXC2 uniformFaceANonposT uniformFaceANonposZ
  unfold uniformFaceANonposP uniformFaceACore
  field_simp [show m + 6 ≠ 0 by positivity]
  ring_nf
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceAPositiveHigh_qOne_C3_nonneg
    (m s : ℝ) (hm : 0 ≤ m) :
    0 ≤ uniformFaceACoreXC3 (m + 4) (uniformFaceANonposT m s) 1 := by
  unfold uniformFaceACoreXC3 uniformFaceANonposT uniformFaceANonposZ
  unfold uniformFaceANonposP uniformFaceACore
  field_simp [show m + 6 ≠ 0 by positivity]
  ring_nf
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
/-- The quadratic part of the high-chart `q = 1` core has nonpositive
discriminant. -/
theorem uniformFaceAPositiveHigh_qOne_discriminant
    (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    (uniformFaceACoreXC1 (m + 4) (uniformFaceANonposT m s) 1)^2 ≤
      4 * uniformFaceACoreXC2 (m + 4) (uniformFaceANonposT m s) 1 *
        uniformFaceACoreXC0 (m + 4) (uniformFaceANonposT m s) 1 := by
  rw [← sub_nonneg]
  unfold uniformFaceACoreXC0 uniformFaceACoreXC1
  unfold uniformFaceACoreXC2 uniformFaceANonposT uniformFaceANonposZ
  unfold uniformFaceANonposP uniformFaceACore
  field_simp [show m + 6 ≠ 0 by positivity]
  ring_nf
  positivity

/-- On the high-`z` chart the endpoint core is nonnegative for every
nonnegative projective coordinate. -/
theorem uniformFaceAPositiveHigh_qOne_nonneg
    (m s X : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) (hX : 0 ≤ X) :
    0 ≤ uniformFaceACore (m + 4) X (uniformFaceANonposT m s) 1 := by
  let C0 := uniformFaceACoreXC0 (m + 4) (uniformFaceANonposT m s) 1
  let C1 := uniformFaceACoreXC1 (m + 4) (uniformFaceANonposT m s) 1
  let C2 := uniformFaceACoreXC2 (m + 4) (uniformFaceANonposT m s) 1
  let C3 := uniformFaceACoreXC3 (m + 4) (uniformFaceANonposT m s) 1
  have h0 : 0 ≤ C0 := by
    dsimp [C0]
    exact uniformFaceACoreXC0_nonneg_of_positive_high
      m s 1 hm hs (by norm_num) (by norm_num)
  have h2 : 0 < C2 := by
    dsimp [C2]
    exact uniformFaceAPositiveHigh_qOne_C2_pos m s hm hs
  have h3 : 0 ≤ C3 := by
    dsimp [C3]
    exact uniformFaceAPositiveHigh_qOne_C3_nonneg m s hm
  have hdisc : C1^2 ≤ 4*C2*C0 := by
    dsimp [C0, C1, C2]
    exact uniformFaceAPositiveHigh_qOne_discriminant m s hm hs
  have hquad : 0 ≤ C2*X^2 + C1*X + C0 := by
    have hid :
        4*C2*(C2*X^2 + C1*X + C0) =
          (2*C2*X + C1)^2 + (4*C2*C0 - C1^2) := by ring
    apply (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*C2)).mp
    rw [hid]
    nlinarith [sq_nonneg (2*C2*X + C1)]
  have hcore :
      uniformFaceACore (m + 4) X (uniformFaceANonposT m s) 1 =
        C2*X^2 + C1*X + C0 + C3*X^3 := by
    dsimp [C0, C1, C2, C3]
    unfold uniformFaceACoreXC0 uniformFaceACoreXC1
    unfold uniformFaceACoreXC2 uniformFaceACoreXC3 uniformFaceACore
    ring
  rw [hcore]
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
/-- The denominator-cleared endpoint is nonnegative throughout the full
high-`z` chart. -/
theorem uniformFaceAPositiveHighVWEndpoint_nonneg
    (m s v t w : ℝ)
    (hm : 0 ≤ m) (hs : 0 ≤ s) (hv : 0 < v) (hv1 : v ≤ 1)
    (ht : 0 < t) (_hw : 0 ≤ w) (hvt : v = w*t) :
    0 ≤ uniformFaceAPositiveHighVWLargeEndpoint m s w t := by
  subst v
  let n := m + 4
  let T := uniformFaceANonposT m s
  let L := uniformFaceACurrentM n T 1
  let q := uniformFaceAPositiveQ m s (w*t)
  let K := uniformFaceACurrentK n T q
  let X := K/(t*n*L)
  have hn : 4 ≤ n := by dsimp [n]; linarith
  have hnpos : 0 < n := by linarith
  have hTge : n - 1 ≤ T := by
    have hz : 0 ≤ uniformFaceANonposZ m s := by
      unfold uniformFaceANonposZ uniformFaceANonposP
      positivity
    dsimp [n, T]
    unfold uniformFaceANonposT
    linarith
  have hL : 0 < L := by
    dsimp [L]
    exact uniformFaceACurrentM_at_one_pos n T hn hTge
  have hq : 0 ≤ q ∧ q ≤ 1 := by
    dsimp [q]
    exact uniformFaceAPositiveQ_mem_unit m s (w*t) hm hs hv.le hv1
  have hK : 0 < K := by
    dsimp [K]
    exact uniformFaceACurrentK_pos n T q hn hTge hq.1 hq.2
  have hX : 0 < X := by dsimp [X]; positivity
  have hcore : 0 ≤ uniformFaceACore n X T 1 := by
    dsimp [n, T] at X ⊢
    exact uniformFaceAPositiveHigh_qOne_nonneg m s X hm hs hX.le
  have hid :
      uniformFaceAPositiveHighVWLargeEndpoint m s w t =
        (t*n*L)^3 * uniformFaceACore n X T 1 := by
    change
      t^3*n^3*L^3*uniformFaceACoreXC0 n T 1
        + t^2*n^2*L^2*K*uniformFaceACoreXC1 n T 1
        + t*n*L*K^2*uniformFaceACoreXC2 n T 1
        + K^3*uniformFaceACoreXC3 n T 1 =
      (t*n*L)^3 * uniformFaceACore n (K/(t*n*L)) T 1
    unfold uniformFaceACoreXC0 uniformFaceACoreXC1
    unfold uniformFaceACoreXC2 uniformFaceACoreXC3 uniformFaceACore
    field_simp [ht.ne', hnpos.ne', hL.ne']
    ring
  rw [hid]
  positivity

/-- The small-ratio chart required by the positive-slope assembly.  The
gradient premise is retained to match that interface, but the endpoint
certificate proves the stronger unconditional statement. -/
theorem uniformFaceAPositiveHighVWSmall_nonneg
    (m s v t w : ℝ)
    (hm : 0 ≤ m) (hs : 0 ≤ s) (hv : 0 < v) (hv1 : v ≤ 1)
    (ht : 0 < t) (_htHalf : t < 1 / 2) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hvt : v = w*t)
    (_hgrad : uniformFaceACurrentGradPoly (m + 4)
      (uniformFaceANonposT m s) (uniformFaceAPositiveQ m s v) w < 0) :
    0 ≤ uniformFaceACurrentPoly (m + 4) (uniformFaceANonposT m s)
      (uniformFaceAPositiveQ m s v) w := by
  apply uniformFaceAPositiveHighVW_nonneg_of_endpoint
    m s v t w hm hs hv hv1 ht hw hw1 hvt
  exact uniformFaceAPositiveHighVWEndpoint_nonneg
    m s v t w hm hs hv hv1 ht hw hvt

/-- Unconditional form of the complementary high-`z` chart. -/
theorem uniformFaceAPositiveHighVW_nonneg
    (m s v t w : ℝ)
    (hm : 0 ≤ m) (hs : 0 ≤ s) (hv : 0 < v) (hv1 : v ≤ 1)
    (ht : 0 < t) (hw : 0 ≤ w) (hw1 : w ≤ 1) (hvt : v = w*t) :
    0 ≤ uniformFaceACurrentPoly (m + 4) (uniformFaceANonposT m s)
      (uniformFaceAPositiveQ m s v) w := by
  apply uniformFaceAPositiveHighVW_nonneg_of_endpoint
    m s v t w hm hs hv hv1 ht hw hw1 hvt
  exact uniformFaceAPositiveHighVWEndpoint_nonneg
    m s v t w hm hs hv hv1 ht hw hvt

end SSP.K3AllStages
