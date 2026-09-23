import SSPLean.K3AllStagesCore

set_option autoImplicit false

namespace SSP.K3AllStages

open SSP.K3S4Renewal
open SSP.K3S4KKT

/-! On the compact half `0 ≤ T ≤ n-1`, two of the three remaining
coefficients admit short positive Bernstein certificates in
`t = T/(n-1)`. -/

noncomputable def cornerBern2 (c0 c1 c2 t : ℝ) : ℝ :=
  c0*(1-t)^2+2*c1*t*(1-t)+c2*t^2

noncomputable def cornerBern3 (c0 c1 c2 c3 t : ℝ) : ℝ :=
  c0*(1-t)^3+3*c1*t*(1-t)^2+3*c2*t^2*(1-t)+c3*t^3

noncomputable def cornerBern4 (c0 c1 c2 c3 c4 t : ℝ) : ℝ :=
  c0*(1-t)^4+4*c1*t*(1-t)^3+6*c2*t^2*(1-t)^2
    +4*c3*t^3*(1-t)+c4*t^4

noncomputable def cornerBern6 (c0 c1 c2 c3 c4 c5 c6 t : ℝ) : ℝ :=
  c0*(1-t)^6+6*c1*t*(1-t)^5+15*c2*t^2*(1-t)^4
    +20*c3*t^3*(1-t)^3+15*c4*t^4*(1-t)^2
    +6*c5*t^5*(1-t)+c6*t^6

theorem cornerBern2_nonneg (c0 c1 c2 t : ℝ)
    (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ cornerBern2 c0 c1 c2 t := by
  unfold cornerBern2
  positivity

theorem cornerBern3_nonneg (c0 c1 c2 c3 t : ℝ)
    (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ cornerBern3 c0 c1 c2 c3 t := by
  unfold cornerBern3
  positivity

theorem cornerBern4_nonneg (c0 c1 c2 c3 c4 t : ℝ)
    (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (h3 : 0 ≤ c3) (h4 : 0 ≤ c4)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ cornerBern4 c0 c1 c2 c3 c4 t := by
  unfold cornerBern4
  positivity

theorem cornerBern6_nonneg (c0 c1 c2 c3 c4 c5 c6 t : ℝ)
    (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (h3 : 0 ≤ c3) (h4 : 0 ≤ c4) (h5 : 0 ≤ c5) (h6 : 0 ≤ c6)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ cornerBern6 c0 c1 c2 c3 c4 c5 c6 t := by
  unfold cornerBern6
  positivity

noncomputable def uniformCornerAOneCommonY1Small (m t : ℝ) : ℝ :=
  cornerBern4
    (24*(m+3)^4*(m+4))
    (3*(m+3)^4*(m+4)*(3*m+17))
    (2*(m+3)^4*(m+4)*(m+6)*(3*m+14))
    ((m+3)^4*(m+4)*(m+5)*(m+6)*(5*m+23)/2)
    ((m+3)^4*(m+4)^3*(m+5)*(m+6)) t

noncomputable def uniformCornerAOneB1Y2Small (m t : ℝ) : ℝ :=
  cornerBern3
    (4*(m+3)^3*(m+4)*(m+5)/3)
    (4*(m+3)^3*(m+4)*(m+5)*(m+6)/3)
    (10*(m+3)^3*(m+4)*(m+5)^2*(m+6)/9)
    (2*(m+3)^3*(m+4)^2*(m+5)^2*(m+6)/3) t

noncomputable def uniformCornerAOneB1Y3Small (m t : ℝ) : ℝ :=
  cornerBern2
    (2*(m+3)*(m+4)*(m+5)*(m+6)^2/3)
    ((m+3)*(m+4)*(m+5)^2*(m+6)^2/3)
    ((m+3)*(m+4)^2*(m+5)^2*(m+6)^2/3) t

noncomputable def uniformCornerAOneB3Y2Small (m t : ℝ) : ℝ :=
  cornerBern3
    (4*(m+3)^3*(m+4)*(4*m+17))
    (4*(m+3)^3*(m+4)*(m+5)*(m+6))
    ((m+3)^3*(m+4)*(13*m^3+202*m^2+1033*m+1752)/3)
    ((m+3)^3*(m+4)^2*(m+5)^2*(2*m+15)) t

noncomputable def uniformCornerAOneB3Y3Small (m t : ℝ) : ℝ :=
  cornerBern2
    (2*(m+3)*(m+4)*(2*m^3+23*m^2+86*m+108))
    ((m+3)*(m+4)*(3*m^3+38*m^2+157*m+216))
    ((m+3)*(m+4)^2*(m^2+10*m+22)*(m^2+10*m+27)) t

noncomputable def uniformCornerAOneB2Y2Small (m t : ℝ) : ℝ :=
  cornerBern3
    (4*(m+3)^3*(m+4)*(5*m+22)/3)
    (8*(m+3)^3*(m+4)*(m+5)*(m+6)/3)
    ((m+3)^3*(m+4)*(23*m^3+362*m^2+1883*m+3252)/9)
    ((m+3)^3*(m+4)^2*(m+5)^2*(4*m+27)/3) t

/-- The nonnegative part of the cubic `Y` coefficient of the middle
`a`-Bernstein coefficient. -/
noncomputable def uniformCornerAOneB2Y3RestSmall (m t : ℝ) : ℝ :=
  2*((m+3)*(m+4)*(m+5)*(m^3+14*m^2+65*m+108)/3)*t*(1-t)
    +(2*(m+3)*(m+4)^2*(m+5)^2*(m^2+11*m+27)/3)*t^2

noncomputable def uniformCornerAOneB2Y4 (m : ℝ) : ℝ :=
  (m+4)^2*(m+5)/3

noncomputable def uniformCornerAOneB2Bad (m t : ℝ) : ℝ :=
  (4*m*(m+3)*(m+4)*(m+5)/3)*(1-t)^2

/-- Bernstein certificate for the discriminant which absorbs the sole
negative term in the compact-region middle coefficient. -/
noncomputable def uniformCornerAOneB2MarginSmall (m t : ℝ) : ℝ :=
  cornerBern4
    (32*(m+3)^2*(m+4)^2*(m+5)*(2*m^3+26*m^2+107*m+132)/9)
    (4*(m+3)^3*(m+4)^3*(m+5)*(6*m^2+71*m+202)/9)
    (2*(m+3)^3*(m+4)^3*(m+5)
      *(23*m^3+386*m^2+2147*m+3972)/27)
    (2*(m+3)^3*(m+4)^3*(m+5)
      *(2*m^4+53*m^3+500*m^2+2019*m+2976)/9)
    (4*(m+3)^3*(m+4)^4*(m+5)^3*(4*m+27)/9) t

theorem uniformCornerAOneCommonY1Small_nonneg
    (m t : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ uniformCornerAOneCommonY1Small m t := by
  unfold uniformCornerAOneCommonY1Small
  apply cornerBern4_nonneg <;> first | assumption | positivity

theorem uniformCornerAOneB1Y2Small_nonneg
    (m t : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ uniformCornerAOneB1Y2Small m t := by
  unfold uniformCornerAOneB1Y2Small
  apply cornerBern3_nonneg <;> first | assumption | positivity

theorem uniformCornerAOneB1Y3Small_nonneg
    (m t : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ uniformCornerAOneB1Y3Small m t := by
  unfold uniformCornerAOneB1Y3Small
  apply cornerBern2_nonneg <;> first | assumption | positivity

theorem uniformCornerAOneB3Y2Small_nonneg
    (m t : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ uniformCornerAOneB3Y2Small m t := by
  unfold uniformCornerAOneB3Y2Small
  apply cornerBern3_nonneg <;> first | assumption | positivity

theorem uniformCornerAOneB3Y3Small_nonneg
    (m t : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ uniformCornerAOneB3Y3Small m t := by
  unfold uniformCornerAOneB3Y3Small
  apply cornerBern2_nonneg <;> first | assumption | positivity

theorem uniformCornerAOneB2Y2Small_nonneg
    (m t : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ uniformCornerAOneB2Y2Small m t := by
  unfold uniformCornerAOneB2Y2Small
  apply cornerBern3_nonneg <;> first | assumption | positivity

theorem uniformCornerAOneB2Y3RestSmall_nonneg
    (m t : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ uniformCornerAOneB2Y3RestSmall m t := by
  unfold uniformCornerAOneB2Y3RestSmall
  positivity

theorem uniformCornerAOneB2MarginSmall_nonneg
    (m t : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ uniformCornerAOneB2MarginSmall m t := by
  unfold uniformCornerAOneB2MarginSmall
  apply cornerBern4_nonneg <;> first | assumption | positivity

theorem uniformCornerAOneB2MarginSmall_identity (m t : ℝ) :
    uniformCornerAOneB2MarginSmall m t =
      4*uniformCornerAOneB2Y4 m*uniformCornerAOneB2Y2Small m t
        -(uniformCornerAOneB2Bad m t)^2 := by
  unfold uniformCornerAOneB2MarginSmall uniformCornerAOneB2Y4
  unfold uniformCornerAOneB2Y2Small uniformCornerAOneB2Bad
  unfold cornerBern3 cornerBern4
  ring

/-- The negative cubic term is controlled by its adjacent quadratic and
quartic terms. -/
theorem uniformCornerAOneB2QuadraticSmall_nonneg
    (m t Y : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ uniformCornerAOneB2Y2Small m t
      -uniformCornerAOneB2Bad m t*Y+uniformCornerAOneB2Y4 m*Y^2 := by
  let A := uniformCornerAOneB2Y4 m
  let b := uniformCornerAOneB2Bad m t
  let c := uniformCornerAOneB2Y2Small m t
  have hA : 0 < A := by
    dsimp [A]
    unfold uniformCornerAOneB2Y4
    positivity
  have hmargin := uniformCornerAOneB2MarginSmall_nonneg m t hm ht ht1
  rw [uniformCornerAOneB2MarginSmall_identity] at hmargin
  have hid : 4*A*(A*Y^2-b*Y+c) = (2*A*Y-b)^2+(4*A*c-b^2) := by ring
  have hscaled : 0 ≤ 4*A*(A*Y^2-b*Y+c) := by
    rw [hid]
    dsimp [A, b, c] at hmargin ⊢
    positivity
  have hcore : 0 ≤ A*Y^2-b*Y+c :=
    (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*A)).mp hscaled
  dsimp [A, b, c] at hcore ⊢
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformCornerAOneB1_small_identity (m t Y : ℝ) :
    uniformCornerAOneB1 (m+4) ((m+3)*t) Y =
      uniformCornerA0B2 m ((m+3)*t)
        +(Y/3)*uniformCornerAOneCommonY1Small m t
        +Y^2*uniformCornerAOneB1Y2Small m t
        +Y^3*uniformCornerAOneB1Y3Small m t := by
  unfold uniformCornerAOneB1 uniformCornerQOne uniformCornerPoly
  unfold uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num
  unfold uniformCornerA0B2 uniformCornerAOneCommonY1Small
  unfold uniformCornerAOneB1Y2Small uniformCornerAOneB1Y3Small
  unfold cornerBern2 cornerBern3 cornerBern4
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformCornerAOneB3_small_identity (m t Y : ℝ) :
    uniformCornerAOneB3 (m+4) ((m+3)*t) Y =
      uniformCornerA0B2 m ((m+3)*t)
        +Y*uniformCornerAOneCommonY1Small m t
        +Y^2*uniformCornerAOneB3Y2Small m t
        +Y^3*uniformCornerAOneB3Y3Small m t
        +(m+4)^2*(m+5)*Y^4 := by
  unfold uniformCornerAOneB3 uniformCornerQOne uniformCornerPoly
  unfold uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num
  unfold uniformCornerA0B2 uniformCornerAOneCommonY1Small
  unfold uniformCornerAOneB3Y2Small uniformCornerAOneB3Y3Small
  unfold cornerBern2 cornerBern3 cornerBern4
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformCornerAOneB2_small_identity (m t Y : ℝ) :
    uniformCornerAOneB2 (m+4) ((m+3)*t) Y =
      uniformCornerA0B2 m ((m+3)*t)
        +(2*Y/3)*uniformCornerAOneCommonY1Small m t
        +Y^2*(uniformCornerAOneB2Y2Small m t
          -uniformCornerAOneB2Bad m t*Y+uniformCornerAOneB2Y4 m*Y^2)
        +Y^3*uniformCornerAOneB2Y3RestSmall m t := by
  unfold uniformCornerAOneB2 uniformCornerQOne uniformCornerPoly
  unfold uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num
  unfold uniformCornerA0B2 uniformCornerAOneCommonY1Small
  unfold uniformCornerAOneB2Y2Small uniformCornerAOneB2Y3RestSmall
  unfold uniformCornerAOneB2Y4 uniformCornerAOneB2Bad
  unfold cornerBern3 cornerBern4
  ring

theorem uniformCornerAOneB1_small_nonneg
    (m t Y : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hY : 0 ≤ Y) : 0 ≤ uniformCornerAOneB1 (m+4) ((m+3)*t) Y := by
  have h0 := uniformCornerA0B2_nonneg m ((m+3)*t) hm (by positivity)
  have h1 := uniformCornerAOneCommonY1Small_nonneg m t hm ht ht1
  have h2 := uniformCornerAOneB1Y2Small_nonneg m t hm ht ht1
  have h3 := uniformCornerAOneB1Y3Small_nonneg m t hm ht ht1
  rw [uniformCornerAOneB1_small_identity]
  positivity

theorem uniformCornerAOneB3_small_nonneg
    (m t Y : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hY : 0 ≤ Y) : 0 ≤ uniformCornerAOneB3 (m+4) ((m+3)*t) Y := by
  have h0 := uniformCornerA0B2_nonneg m ((m+3)*t) hm (by positivity)
  have h1 := uniformCornerAOneCommonY1Small_nonneg m t hm ht ht1
  have h2 := uniformCornerAOneB3Y2Small_nonneg m t hm ht ht1
  have h3 := uniformCornerAOneB3Y3Small_nonneg m t hm ht ht1
  rw [uniformCornerAOneB3_small_identity]
  positivity

theorem uniformCornerAOneB2_small_nonneg
    (m t Y : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hY : 0 ≤ Y) : 0 ≤ uniformCornerAOneB2 (m+4) ((m+3)*t) Y := by
  have h0 := uniformCornerA0B2_nonneg m ((m+3)*t) hm (by positivity)
  have h1 := uniformCornerAOneCommonY1Small_nonneg m t hm ht ht1
  have h2 := uniformCornerAOneB2QuadraticSmall_nonneg m t Y hm ht ht1
  have h3 := uniformCornerAOneB2Y3RestSmall_nonneg m t hm ht ht1
  rw [uniformCornerAOneB2_small_identity]
  positivity

theorem uniformCornerAOneB1_nonneg_of_T_le
    (n T Y : ℝ) (hn : 4 ≤ n) (hT : 0 ≤ T) (hT1 : T ≤ n-1)
    (hY : 0 ≤ Y) : 0 ≤ uniformCornerAOneB1 n T Y := by
  let m := n-4
  let t := T/(n-1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hn1 : 0 < n-1 := by linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; exact (div_le_one hn1).2 hT1
  have hid : (m+3)*t = T := by
    dsimp [m, t]
    field_simp [hn1.ne']
    ring
  rw [← hid]
  simpa [m] using uniformCornerAOneB1_small_nonneg m t Y hm ht ht1 hY

theorem uniformCornerAOneB3_nonneg_of_T_le
    (n T Y : ℝ) (hn : 4 ≤ n) (hT : 0 ≤ T) (hT1 : T ≤ n-1)
    (hY : 0 ≤ Y) : 0 ≤ uniformCornerAOneB3 n T Y := by
  let m := n-4
  let t := T/(n-1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hn1 : 0 < n-1 := by linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; exact (div_le_one hn1).2 hT1
  have hid : (m+3)*t = T := by
    dsimp [m, t]
    field_simp [hn1.ne']
    ring
  rw [← hid]
  simpa [m] using uniformCornerAOneB3_small_nonneg m t Y hm ht ht1 hY

theorem uniformCornerAOneB2_nonneg_of_T_le
    (n T Y : ℝ) (hn : 4 ≤ n) (hT : 0 ≤ T) (hT1 : T ≤ n-1)
    (hY : 0 ≤ Y) : 0 ≤ uniformCornerAOneB2 n T Y := by
  let m := n-4
  let t := T/(n-1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hn1 : 0 < n-1 := by linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; exact (div_le_one hn1).2 hT1
  have hid : (m+3)*t = T := by
    dsimp [m, t]
    field_simp [hn1.ne']
    ring
  rw [← hid]
  simpa [m] using uniformCornerAOneB2_small_nonneg m t Y hm ht ht1 hY

/-- On `0 ≤ T ≤ n-1`, only the middle `a`-Bernstein coefficient remains. -/
theorem uniformCornerQOne_nonneg_of_T_le
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hT1 : T ≤ n-1) (hY : 0 ≤ Y)
    (h2 : 0 ≤ uniformCornerAOneB2 n T Y) :
    0 ≤ uniformCornerQOne n a T Y := by
  apply uniformCornerQOne_nonneg_of_a_bernstein n a T Y hn ha ha1 hT
  · exact uniformCornerAOneB1_nonneg_of_T_le n T Y hn hT hT1 hY
  · exact h2
  · exact uniformCornerAOneB3_nonneg_of_T_le n T Y hn hT hT1 hY

/-- Complete sharp-corner endpoint certificate on the compact half
`0 ≤ T ≤ n-1`. -/
theorem uniformCornerQOne_T_le_nonneg
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hT1 : T ≤ n-1) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerQOne n a T Y := by
  apply uniformCornerQOne_nonneg_of_T_le n a T Y hn ha ha1 hT hT1 hY
  exact uniformCornerAOneB2_nonneg_of_T_le n T Y hn hT hT1 hY

/-! ### The complementary region `n-1 ≤ T`

The three coefficients have the same potentially negative linear term in
`Y`, with multiplicities one, two, and three.  After writing
`T = n-1+z`, all other monomials have nonnegative coefficients. -/

noncomputable def uniformCornerAOneLargeN (m z : ℝ) : ℝ :=
  16*z^2*(5*m*z^2+65*m*z+6*z^2+102*z+189)

noncomputable def uniformCornerAOneB1Y2Large (m z : ℝ) : ℝ :=
  let T := m+3+z
  (2*(m+4)*(m+5)/3)*(T^3*m^3+10*T^3*m^2+25*T^3*m+4*T^3
    +5*T^2*m^3+58*T^2*m^2+213*T^2*m+252*T^2
    +6*T*m^3+66*T*m^2+234*T*m+270*T
    +2*m^3+18*m^2+54*m+54)

noncomputable def uniformCornerAOneB1LargeRest (m z Y : ℝ) : ℝ :=
  uniformCornerAOneB1 (m+4) (m+3+z) Y
    -uniformCornerA0B2 m (m+3+z)
    +uniformCornerAOneLargeN m z*Y
    -uniformCornerAOneB1Y2Large m z*Y^2

theorem uniformCornerAOneB1Y2Large_nonneg
    (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 ≤ uniformCornerAOneB1Y2Large m z := by
  unfold uniformCornerAOneB1Y2Large
  dsimp
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformCornerAOneB1LargeRest_nonneg
    (m z Y : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerAOneB1LargeRest m z Y := by
  unfold uniformCornerAOneB1LargeRest uniformCornerAOneB1
  unfold uniformCornerQOne uniformCornerPoly
  unfold uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num
  unfold uniformCornerA0B2 uniformCornerAOneLargeN
  unfold uniformCornerAOneB1Y2Large
  dsimp
  ring_nf
  positivity

noncomputable def uniformCornerAOneB1LargeMargin (m z : ℝ) : ℝ :=
  4*uniformCornerA0B2 m (m+3+z)*uniformCornerAOneB1Y2Large m z
    -(uniformCornerAOneLargeN m z)^2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformCornerAOneB1LargeMargin_nonneg
    (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 ≤ uniformCornerAOneB1LargeMargin m z := by
  unfold uniformCornerAOneB1LargeMargin uniformCornerA0B2
  unfold uniformCornerAOneB1Y2Large uniformCornerAOneLargeN
  dsimp
  ring_nf
  positivity

theorem uniformCornerAOneB1LargeCore_nonneg
    (m z Y : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 ≤ uniformCornerA0B2 m (m+3+z)
      -uniformCornerAOneLargeN m z*Y
      +uniformCornerAOneB1Y2Large m z*Y^2 := by
  let A := uniformCornerAOneB1Y2Large m z
  let b := uniformCornerAOneLargeN m z
  let c := uniformCornerA0B2 m (m+3+z)
  have hA : 0 < A := by
    dsimp [A]
    unfold uniformCornerAOneB1Y2Large
    dsimp
    positivity
  have hmargin := uniformCornerAOneB1LargeMargin_nonneg m z hm hz
  have hmargin' : 0 ≤ 4*c*A-b^2 := by
    simpa [uniformCornerAOneB1LargeMargin, A, b, c] using hmargin
  have hid : 4*A*(A*Y^2-b*Y+c) = (2*A*Y-b)^2+(4*A*c-b^2) := by ring
  have hscaled : 0 ≤ 4*A*(A*Y^2-b*Y+c) := by
    rw [hid]
    nlinarith [sq_nonneg (2*A*Y-b)]
  have hcore : 0 ≤ A*Y^2-b*Y+c :=
    (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*A)).mp hscaled
  dsimp [A, b, c] at hcore ⊢
  linarith

theorem uniformCornerAOneB1_large_nonneg
    (m z Y : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerAOneB1 (m+4) (m+3+z) Y := by
  have hcore := uniformCornerAOneB1LargeCore_nonneg m z Y hm hz
  have hrest := uniformCornerAOneB1LargeRest_nonneg m z Y hm hz hY
  unfold uniformCornerAOneB1LargeRest at hrest
  linarith

theorem uniformCornerAOneB1_nonneg_of_T_ge
    (n T Y : ℝ) (hn : 4 ≤ n) (hT1 : n-1 ≤ T) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerAOneB1 n T Y := by
  let m := n-4
  let z := T-(n-1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : m+3+z = T := by dsimp [m, z]; ring
  rw [← hnid, ← hTid]
  exact uniformCornerAOneB1_large_nonneg m z Y hm hz hY

noncomputable def uniformCornerAOneB2Y2Large (m z : ℝ) : ℝ :=
  let T := m+3+z
  ((m+4)/3)*(4*T^3*m^4+60*T^3*m^3+300*T^3*m^2+516*T^3*m+80*T^3
    +23*T^2*m^4+383*T^2*m^3+2357*T^2*m^2+6321*T^2*m+6228*T^2
    +24*T*m^4+348*T*m^3+1896*T*m^2+4572*T*m+4104*T
    +20*m^4+268*m^3+1332*m^2+2916*m+2376)

noncomputable def uniformCornerAOneB2LargeRest (m z Y : ℝ) : ℝ :=
  uniformCornerAOneB2 (m+4) (m+3+z) Y
    -uniformCornerA0B2 m (m+3+z)
    +2*uniformCornerAOneLargeN m z*Y
    -uniformCornerAOneB2Y2Large m z*Y^2

noncomputable def uniformCornerAOneB2LargeMargin (m z : ℝ) : ℝ :=
  4*uniformCornerA0B2 m (m+3+z)*uniformCornerAOneB2Y2Large m z
    -(2*uniformCornerAOneLargeN m z)^2

theorem uniformCornerAOneB2Y2Large_pos
    (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 < uniformCornerAOneB2Y2Large m z := by
  unfold uniformCornerAOneB2Y2Large
  dsimp
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformCornerAOneB2LargeRest_nonneg
    (m z Y : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerAOneB2LargeRest m z Y := by
  unfold uniformCornerAOneB2LargeRest uniformCornerAOneB2
  unfold uniformCornerQOne uniformCornerPoly
  unfold uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num
  unfold uniformCornerA0B2 uniformCornerAOneLargeN
  unfold uniformCornerAOneB2Y2Large
  dsimp
  ring_nf
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformCornerAOneB2LargeMargin_nonneg
    (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 ≤ uniformCornerAOneB2LargeMargin m z := by
  unfold uniformCornerAOneB2LargeMargin uniformCornerA0B2
  unfold uniformCornerAOneB2Y2Large uniformCornerAOneLargeN
  dsimp
  ring_nf
  positivity

theorem uniformCornerAOneB2LargeCore_nonneg
    (m z Y : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 ≤ uniformCornerA0B2 m (m+3+z)
      -2*uniformCornerAOneLargeN m z*Y
      +uniformCornerAOneB2Y2Large m z*Y^2 := by
  let A := uniformCornerAOneB2Y2Large m z
  let b := 2*uniformCornerAOneLargeN m z
  let c := uniformCornerA0B2 m (m+3+z)
  have hA : 0 < A := uniformCornerAOneB2Y2Large_pos m z hm hz
  have hmargin := uniformCornerAOneB2LargeMargin_nonneg m z hm hz
  have hmargin' : 0 ≤ 4*c*A-b^2 := by
    simpa [uniformCornerAOneB2LargeMargin, A, b, c] using hmargin
  have hid : 4*A*(A*Y^2-b*Y+c) = (2*A*Y-b)^2+(4*A*c-b^2) := by ring
  have hscaled : 0 ≤ 4*A*(A*Y^2-b*Y+c) := by
    rw [hid]
    nlinarith [sq_nonneg (2*A*Y-b)]
  have hcore : 0 ≤ A*Y^2-b*Y+c :=
    (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*A)).mp hscaled
  dsimp [A, b, c] at hcore ⊢
  linarith

theorem uniformCornerAOneB2_large_nonneg
    (m z Y : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerAOneB2 (m+4) (m+3+z) Y := by
  have hcore := uniformCornerAOneB2LargeCore_nonneg m z Y hm hz
  have hrest := uniformCornerAOneB2LargeRest_nonneg m z Y hm hz hY
  unfold uniformCornerAOneB2LargeRest at hrest
  linarith

theorem uniformCornerAOneB2_nonneg_of_T_ge
    (n T Y : ℝ) (hn : 4 ≤ n) (hT1 : n-1 ≤ T) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerAOneB2 n T Y := by
  let m := n-4
  let z := T-(n-1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : m+3+z = T := by dsimp [m, z]; ring
  rw [← hnid, ← hTid]
  exact uniformCornerAOneB2_large_nonneg m z Y hm hz hY

noncomputable def uniformCornerAOneB3Y2Large (m z : ℝ) : ℝ :=
  let T := m+3+z
  (m+4)*(2*T^3*m^4+30*T^3*m^3+150*T^3*m^2+258*T^3*m+40*T^3
    +13*T^2*m^4+217*T^2*m^3+1351*T^2*m^2+3687*T^2*m+3708*T^2
    +12*T*m^4+156*T*m^3+768*T*m^2+1692*T*m+1404*T
    +16*m^4+212*m^3+1044*m^2+2268*m+1836)

noncomputable def uniformCornerAOneB3LargeRest (m z Y : ℝ) : ℝ :=
  uniformCornerAOneB3 (m+4) (m+3+z) Y
    -uniformCornerA0B2 m (m+3+z)
    +3*uniformCornerAOneLargeN m z*Y
    -uniformCornerAOneB3Y2Large m z*Y^2

noncomputable def uniformCornerAOneB3LargeMargin (m z : ℝ) : ℝ :=
  4*uniformCornerA0B2 m (m+3+z)*uniformCornerAOneB3Y2Large m z
    -(3*uniformCornerAOneLargeN m z)^2

theorem uniformCornerAOneB3Y2Large_pos
    (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 < uniformCornerAOneB3Y2Large m z := by
  unfold uniformCornerAOneB3Y2Large
  dsimp
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformCornerAOneB3LargeRest_nonneg
    (m z Y : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerAOneB3LargeRest m z Y := by
  unfold uniformCornerAOneB3LargeRest uniformCornerAOneB3
  unfold uniformCornerQOne uniformCornerPoly
  unfold uniformCornerM2Num uniformCornerM3Num uniformCornerM4Num
  unfold uniformCornerA0B2 uniformCornerAOneLargeN
  unfold uniformCornerAOneB3Y2Large
  dsimp
  ring_nf
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem uniformCornerAOneB3LargeMargin_nonneg
    (m z : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 ≤ uniformCornerAOneB3LargeMargin m z := by
  unfold uniformCornerAOneB3LargeMargin uniformCornerA0B2
  unfold uniformCornerAOneB3Y2Large uniformCornerAOneLargeN
  dsimp
  ring_nf
  positivity

theorem uniformCornerAOneB3LargeCore_nonneg
    (m z Y : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) :
    0 ≤ uniformCornerA0B2 m (m+3+z)
      -3*uniformCornerAOneLargeN m z*Y
      +uniformCornerAOneB3Y2Large m z*Y^2 := by
  let A := uniformCornerAOneB3Y2Large m z
  let b := 3*uniformCornerAOneLargeN m z
  let c := uniformCornerA0B2 m (m+3+z)
  have hA : 0 < A := uniformCornerAOneB3Y2Large_pos m z hm hz
  have hmargin := uniformCornerAOneB3LargeMargin_nonneg m z hm hz
  have hmargin' : 0 ≤ 4*c*A-b^2 := by
    simpa [uniformCornerAOneB3LargeMargin, A, b, c] using hmargin
  have hid : 4*A*(A*Y^2-b*Y+c) = (2*A*Y-b)^2+(4*A*c-b^2) := by ring
  have hscaled : 0 ≤ 4*A*(A*Y^2-b*Y+c) := by
    rw [hid]
    nlinarith [sq_nonneg (2*A*Y-b)]
  have hcore : 0 ≤ A*Y^2-b*Y+c :=
    (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*A)).mp hscaled
  dsimp [A, b, c] at hcore ⊢
  linarith

theorem uniformCornerAOneB3_large_nonneg
    (m z Y : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerAOneB3 (m+4) (m+3+z) Y := by
  have hcore := uniformCornerAOneB3LargeCore_nonneg m z Y hm hz
  have hrest := uniformCornerAOneB3LargeRest_nonneg m z Y hm hz hY
  unfold uniformCornerAOneB3LargeRest at hrest
  linarith

theorem uniformCornerAOneB3_nonneg_of_T_ge
    (n T Y : ℝ) (hn : 4 ≤ n) (hT1 : n-1 ≤ T) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerAOneB3 n T Y := by
  let m := n-4
  let z := T-(n-1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hnid : m+4 = n := by dsimp [m]; ring
  have hTid : m+3+z = T := by dsimp [m, z]; ring
  rw [← hnid, ← hTid]
  exact uniformCornerAOneB3_large_nonneg m z Y hm hz hY

theorem uniformCornerQOne_T_ge_nonneg
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hT1 : n-1 ≤ T) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerQOne n a T Y := by
  apply uniformCornerQOne_nonneg_of_a_bernstein n a T Y hn ha ha1
    (by linarith)
  · exact uniformCornerAOneB1_nonneg_of_T_ge n T Y hn hT1 hY
  · exact uniformCornerAOneB2_nonneg_of_T_ge n T Y hn hT1 hY
  · exact uniformCornerAOneB3_nonneg_of_T_ge n T Y hn hT1 hY

/-- The sole remaining `q = 1` sharp-corner endpoint is nonnegative on its
entire parameter box. -/
theorem uniformCornerQOne_nonneg
    (n a T Y : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hY : 0 ≤ Y) :
    0 ≤ uniformCornerQOne n a T Y := by
  by_cases hT1 : T ≤ n-1
  · exact uniformCornerQOne_T_le_nonneg n a T Y hn ha ha1 hT hT1 hY
  · exact uniformCornerQOne_T_ge_nonneg n a T Y hn ha ha1 (by linarith) hY

/-- Complete sharp-corner inequality for every stage parameter `n ≥ 4` and
every admissible pair of mixture weights. -/
theorem uniformSharpGap_nonneg
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1) :
    0 ≤ uniformSharpGap n a T Y q := by
  apply uniformSharpGap_nonneg_of_q_one n a T Y q hn ha ha1 hT hY hq hq1
  exact uniformCornerQOne_nonneg n a T Y hn ha ha1 hT.le hY.le

end SSP.K3AllStages
