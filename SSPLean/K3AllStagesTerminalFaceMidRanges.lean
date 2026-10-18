import SSPLean.K3AllStagesTerminalFaceMidB4
set_option autoImplicit false
namespace SSP.K3AllStages
/-- In the large-scale slope regime, the middle endpoint certificate is
reduced to four normalized Bernstein coefficients.  The zeroth coefficient
is unconditional. -/
theorem uniformFaceBCoreB1_nonneg_of_large_slope_coefficients
    (m a t Y : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (ha1 : a ≤ 1)
    (ht : 0 ≤ t) (hY : 0 ≤ Y)
    (hslope : uniformGradB0 (m+4) a (t+1) Y <
      uniformGradB1 (m+4) a (t+1) Y)
    :
    0 ≤ uniformFaceBCoreB1 (m+4) a (t+1) Y := by
  have hx : 0 ≤ a*Y := mul_nonneg ha.le hY
  have hthreshold :=
    (uniformLargeGradSlope_threshold_lt m a t Y hm ht hslope).2.le
  have h1 := uniformLargeMidB1_nonneg_of_threshold
    m t (a*Y) hm ht hx hthreshold
  have h2 := uniformLargeMidB2_nonneg_of_threshold
    m t (a*Y) hm ht hx hthreshold
  have h3 := uniformLargeMidB3_nonneg_of_threshold
    m t (a*Y) hm ht hthreshold
  have h4 := uniformLargeMidB4_nonneg_of_threshold
    m t (a*Y) hm ht hthreshold
  have hscaled : 0 ≤ a^2*uniformFaceBCoreB1 (m+4) a (t+1) Y := by
    rw [show Y = (a*Y)/a by field_simp [ha.ne']]
    rw [uniformLargeMid_bernstein_a m a t (a*Y) ha.ne']
    exact cornerBern4_nonneg _ _ _ _ _ a
      (uniformLargeMidB0_nonneg m t (a*Y) hm ht hx) h1 h2 h3 h4 ha.le ha1
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos ha)).mp hscaled

/-- The middle Bernstein coefficient is nonnegative in the large-scale
regime whenever the endpoint gradient increases across the terminal face. -/
theorem uniformFaceBCoreB1_nonneg_of_large_slope
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 1 ≤ T) (hY : 0 ≤ Y)
    (hslope : uniformGradB0 n a T Y < uniformGradB1 n a T Y) :
    0 ≤ uniformFaceBCoreB1 n a T Y := by
  let m := n-4
  let t := T-1
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : t+1 = T := by dsimp [t]; ring
  rw [← hnid, ← hTid] at hslope ⊢
  exact uniformFaceBCoreB1_nonneg_of_large_slope_coefficients
    m a t Y hm ha ha1 ht hY hslope

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeMidB0_nonneg_of_t_le_one
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidB0 m t x := by
  let c0 := sampledBern2C0
    (uniformLargeMidB0 m 1 x) (uniformLargeMidB0 m 2 x)
      (uniformLargeMidB0 m 3 x)
  let c1 := sampledBern2C1
    (uniformLargeMidB0 m 1 x) (uniformLargeMidB0 m 2 x)
      (uniformLargeMidB0 m 3 x)
  let c2 := sampledBern2C2
    (uniformLargeMidB0 m 1 x) (uniformLargeMidB0 m 2 x)
      (uniformLargeMidB0 m 3 x)
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    unfold sampledBern2C0 uniformLargeMidB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc1 : 0 ≤ c1 := by
    dsimp [c1]
    unfold sampledBern2C1 uniformLargeMidB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    unfold sampledBern2C2 uniformLargeMidB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hid : uniformLargeMidB0 m t x = cornerBern2 c0 c1 c2 t := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    ring
  rw [hid]
  exact cornerBern2_nonneg c0 c1 c2 t hc0 hc1 hc2
    (by positivity) (by linarith)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeMidA1_nonneg_of_t_le_one
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidA1 m t x := by
  let c0 := sampledBern2C0
    (uniformLargeMidA1 m 1 x) (uniformLargeMidA1 m 2 x)
      (uniformLargeMidA1 m 3 x)
  let c1 := sampledBern2C1
    (uniformLargeMidA1 m 1 x) (uniformLargeMidA1 m 2 x)
      (uniformLargeMidA1 m 3 x)
  let c2 := sampledBern2C2
    (uniformLargeMidA1 m 1 x) (uniformLargeMidA1 m 2 x)
      (uniformLargeMidA1 m 3 x)
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    unfold sampledBern2C0 uniformLargeMidA1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc1 : 0 ≤ c1 := by
    dsimp [c1]
    unfold sampledBern2C1 uniformLargeMidA1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    unfold sampledBern2C2 uniformLargeMidA1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hid : uniformLargeMidA1 m t x = cornerBern2 c0 c1 c2 t := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidA1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    ring
  rw [hid]
  exact cornerBern2_nonneg c0 c1 c2 t hc0 hc1 hc2
    (by positivity) (by linarith)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeMidB4_nonneg_of_t_le_one
    (m t x : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidB4 m t x := by
  let c0 := sampledBern2C0
    (uniformLargeMidB4 m 1 x) (uniformLargeMidB4 m 2 x)
      (uniformLargeMidB4 m 3 x)
  let c1 := sampledBern2C1
    (uniformLargeMidB4 m 1 x) (uniformLargeMidB4 m 2 x)
      (uniformLargeMidB4 m 3 x)
  let c2 := sampledBern2C2
    (uniformLargeMidB4 m 1 x) (uniformLargeMidB4 m 2 x)
      (uniformLargeMidB4 m 3 x)
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    unfold sampledBern2C0 uniformLargeMidB4 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc1 : 0 ≤ c1 := by
    dsimp [c1]
    unfold sampledBern2C1 uniformLargeMidB4 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    unfold sampledBern2C2 uniformLargeMidB4 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hid : uniformLargeMidB4 m t x = cornerBern2 c0 c1 c2 t := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidB4 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    ring
  rw [hid]
  exact cornerBern2_nonneg c0 c1 c2 t hc0 hc1 hc2
    (by positivity) (by linarith)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceBCoreB1_nonneg_of_t_le_one
    (m a t Y : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (ha1 : a ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1 (m+4) a (t+1) Y := by
  have hx : 0 ≤ a*Y := mul_nonneg ha.le hY
  have haid : a^2*uniformFaceBCoreB1 (m+4) a (t+1) Y =
      cornerBern2 (uniformLargeMidB0 m t (a*Y))
        (uniformLargeMidA1 m t (a*Y))
        (uniformLargeMidB4 m t (a*Y)) a := by
    unfold uniformLargeMidB0 uniformLargeMidA1 uniformLargeMidB4
    unfold uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    field_simp [ha.ne']
    ring
  have hscaled : 0 ≤ a^2*uniformFaceBCoreB1 (m+4) a (t+1) Y := by
    rw [haid]
    exact cornerBern2_nonneg _ _ _ a
      (uniformLargeMidB0_nonneg_of_t_le_one m t (a*Y) hm ht ht1 hx)
      (uniformLargeMidA1_nonneg_of_t_le_one m t (a*Y) hm ht ht1 hx)
      (uniformLargeMidB4_nonneg_of_t_le_one m t (a*Y) hm ht ht1 hx)
      ha.le ha1
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos ha)).mp hscaled

theorem uniformFaceBCoreB1_nonneg_of_T_le_two
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 1 ≤ T) (hT2 : T ≤ 2) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1 n a T Y := by
  let m := n-4
  let t := T-1
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : t+1 = T := by dsimp [t]; ring
  rw [← hnid, ← hTid]
  exact uniformFaceBCoreB1_nonneg_of_t_le_one
    m a t Y hm ha ha1 ht ht1 hY

theorem uniformFaceBCoreB1_nonneg_of_T_le_three_halves
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 1 ≤ T) (hT32 : T ≤ 3/2) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1 n a T Y := by
  exact uniformFaceBCoreB1_nonneg_of_T_le_two
    n a T Y hn ha ha1 hT (by linarith) hY

noncomputable def uniformLargeMidTimeB0 (m a x : ℝ) : ℝ :=
  3*uniformLargeMidSample m a 8 x
    - 3*uniformLargeMidSample m a 16 x
    + uniformLargeMidSample m a 24 x

noncomputable def uniformLargeMidTimeB1 (m a x : ℝ) : ℝ :=
  (7*uniformLargeMidSample m a 8 x
    - 4*uniformLargeMidSample m a 16 x
    + uniformLargeMidSample m a 24 x) / 4

noncomputable def uniformLargeMidTimeB2 (m a x : ℝ) : ℝ :=
  uniformLargeMidSample m a 8 x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeMidTimeB0_nonneg
    (m a x : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidTimeB0 m a x := by
  let c0 := sampledBern2C0 (uniformLargeMidTimeB0 m 1 x)
    (uniformLargeMidTimeB0 m 2 x) (uniformLargeMidTimeB0 m 3 x)
  let c1 := sampledBern2C1 (uniformLargeMidTimeB0 m 1 x)
    (uniformLargeMidTimeB0 m 2 x) (uniformLargeMidTimeB0 m 3 x)
  let c2 := sampledBern2C2 (uniformLargeMidTimeB0 m 1 x)
    (uniformLargeMidTimeB0 m 2 x) (uniformLargeMidTimeB0 m 3 x)
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    unfold sampledBern2C0 uniformLargeMidTimeB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    unfold sampledBern2C2 uniformLargeMidTimeB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hdet : 0 ≤ c0*c2-c1^2 := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidTimeB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hid : uniformLargeMidTimeB0 m a x = cornerBern2 c0 c1 c2 a := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidTimeB0 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    field_simp [ha.ne']
    ring
  rw [hid]
  exact cornerBern2_nonneg_of_det c0 c1 c2 a hc0 hc2 hdet

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeMidTimeB1_nonneg
    (m a x : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidTimeB1 m a x := by
  let c0 := sampledBern2C0 (uniformLargeMidTimeB1 m 1 x)
    (uniformLargeMidTimeB1 m 2 x) (uniformLargeMidTimeB1 m 3 x)
  let c1 := sampledBern2C1 (uniformLargeMidTimeB1 m 1 x)
    (uniformLargeMidTimeB1 m 2 x) (uniformLargeMidTimeB1 m 3 x)
  let c2 := sampledBern2C2 (uniformLargeMidTimeB1 m 1 x)
    (uniformLargeMidTimeB1 m 2 x) (uniformLargeMidTimeB1 m 3 x)
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    unfold sampledBern2C0 uniformLargeMidTimeB1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    unfold sampledBern2C2 uniformLargeMidTimeB1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hdet : 0 ≤ c0*c2-c1^2 := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidTimeB1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hid : uniformLargeMidTimeB1 m a x = cornerBern2 c0 c1 c2 a := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidTimeB1 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    field_simp [ha.ne']
    ring
  rw [hid]
  exact cornerBern2_nonneg_of_det c0 c1 c2 a hc0 hc2 hdet

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformLargeMidTimeB2_nonneg
    (m a x : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (hx : 0 ≤ x) :
    0 ≤ uniformLargeMidTimeB2 m a x := by
  let c0 := sampledBern2C0 (uniformLargeMidTimeB2 m 1 x)
    (uniformLargeMidTimeB2 m 2 x) (uniformLargeMidTimeB2 m 3 x)
  let c1 := sampledBern2C1 (uniformLargeMidTimeB2 m 1 x)
    (uniformLargeMidTimeB2 m 2 x) (uniformLargeMidTimeB2 m 3 x)
  let c2 := sampledBern2C2 (uniformLargeMidTimeB2 m 1 x)
    (uniformLargeMidTimeB2 m 2 x) (uniformLargeMidTimeB2 m 3 x)
  have hc0 : 0 ≤ c0 := by
    dsimp [c0]
    unfold sampledBern2C0 uniformLargeMidTimeB2 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hc2 : 0 ≤ c2 := by
    dsimp [c2]
    unfold sampledBern2C2 uniformLargeMidTimeB2 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hdet : 0 ≤ c0*c2-c1^2 := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidTimeB2 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    ring_nf
    positivity
  have hid : uniformLargeMidTimeB2 m a x = cornerBern2 c0 c1 c2 a := by
    dsimp [c0, c1, c2]
    unfold sampledBern2C0 sampledBern2C1 sampledBern2C2
    unfold uniformLargeMidTimeB2 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    field_simp [ha.ne']
    ring
  rw [hid]
  exact cornerBern2_nonneg_of_det c0 c1 c2 a hc0 hc2 hdet

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem uniformFaceBCoreB1_nonneg_of_t_le_eight
    (m a t Y : ℝ) (hm : 0 ≤ m) (ha : 0 < a)
    (ht : 0 ≤ t) (ht8 : t ≤ 8) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1 (m+4) a (t+1) Y := by
  have hx : 0 ≤ a*Y := mul_nonneg ha.le hY
  have hid : uniformLargeMidSample m a t (a*Y) =
      cornerBern2 (uniformLargeMidTimeB0 m a (a*Y))
        (uniformLargeMidTimeB1 m a (a*Y))
        (uniformLargeMidTimeB2 m a (a*Y)) (t/8) := by
    unfold uniformLargeMidTimeB0 uniformLargeMidTimeB1
    unfold uniformLargeMidTimeB2 uniformLargeMidSample
    unfold uniformFaceBCoreB1 uniformFaceBCoreQ0 uniformFaceBCoreQ1
    unfold cornerBern2
    field_simp [ha.ne']
    ring
  have hscaled : 0 ≤ uniformLargeMidSample m a t (a*Y) := by
    rw [hid]
    exact cornerBern2_nonneg _ _ _ (t/8)
      (uniformLargeMidTimeB0_nonneg m a (a*Y) hm ha hx)
      (uniformLargeMidTimeB1_nonneg m a (a*Y) hm ha hx)
      (uniformLargeMidTimeB2_nonneg m a (a*Y) hm ha hx)
      (by positivity) (by linarith)
  unfold uniformLargeMidSample at hscaled
  rw [show a*Y/a = Y by field_simp [ha.ne']] at hscaled
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos ha)).mp hscaled

theorem uniformFaceBCoreB1_nonneg_of_T_le_nine
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 < a)
    (hT : 1 ≤ T) (hT9 : T ≤ 9) (hY : 0 ≤ Y) :
    0 ≤ uniformFaceBCoreB1 n a T Y := by
  let m := n-4
  let t := T-1
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht8 : t ≤ 8 := by dsimp [t]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : t+1 = T := by dsimp [t]; ring
  rw [← hnid, ← hTid]
  exact uniformFaceBCoreB1_nonneg_of_t_le_eight
    m a t Y hm ha ht ht8 hY


end SSP.K3AllStages
