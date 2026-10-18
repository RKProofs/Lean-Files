import SSPLean.K3FourthRenewal

/-!
# The `k = 3` renewal polynomial at order three

The `k = 3` all-stage certificates of `SSPLean.K3AllStages*` require `4 ≤ n`.  The order-three
instance therefore needs its own certificate, exactly as the `k = 2` development needed
`SSPLean.K2S3Direct` for its own `n = 3` instance.

This file proves the scalar polynomial facts.  All quantities are the moments of the two
state-return excursions, which at `n = 3` have order at most two, so the available inputs are:

* Aldous--Shepp at order two: `A ≥ (3/2) u²` (written `3u² ≤ 2A`);
* the `k = 2` bound at `s = 2`: `3uC ≥ 4A²`;
* the `k = 3` bound at `s = 2`: `4AE ≥ 5C²`.

The target is nonnegativity of the order-three `k = 3` gap `5 m₂ m₄ - 6 m₃²`.

Numerical exploration shows the bound is *exactly tight* on the no-return face `p = 0` with
all three input inequalities active, and strictly slack in the interior, so the no-return face
is proved separately and sharply below.
-/

namespace SSP.K3S3

/-! ## The certified kernel face

The hard two-variable face of the reduction below, proved by an explicit
Positivstellensatz certificate (18 terms, exact rational coefficients) found with
`cvxpy`/LP in the chart `B = U/(1+U)`, `x = Y` and verified here by `ring` + `positivity`.
The certificate construction is recorded in the module docstring. -/

set_option maxHeartbeats 2000000 in
/-- The kernel inequality in the `(U,Y)` chart, by an explicit Positivstellensatz
certificate found by SDP/LP and verified exactly over `ℚ`. -/
theorem kernelUY_nonneg (U Y : ℝ) (hU : 0 ≤ U) (hY : 0 ≤ Y) :
    0 ≤ 9*U^4 + 300*U^3*Y^2 + 12*U^3*Y + 36*U^3 - 384*U^2*Y^3 + 570*U^2*Y^2
      + 36*U^2*Y + 54*U^2 + 144*U*Y^4 - 624*U*Y^3 + 240*U*Y^2 + 36*U*Y + 36*U
      + 96*Y^6 + 192*Y^5 + 240*Y^4 - 240*Y^3 - 30*Y^2 + 12*Y + 9 := by
  have e : 9*U^4 + 300*U^3*Y^2 + 12*U^3*Y + 36*U^3 - 384*U^2*Y^3 + 570*U^2*Y^2
      + 36*U^2*Y + 54*U^2 + 144*U*Y^4 - 624*U*Y^3 + 240*U*Y^2 + 36*U*Y + 36*U
      + 96*Y^6 + 192*Y^5 + 240*Y^4 - 240*Y^3 - 30*Y^2 + 12*Y + 9
      = (51/11)*U + (888/11)*(U*Y) + (1119/11)*U^2 + (152/11)*(U^3*Y)
        + (4876/55)*(U^3*Y^2) + (271/11)*(U^3*(2*Y-1)^2)
        + 6*(Y^2*((2*Y-1)^2)^2)
        + 9*(U + (2*Y-1))^2
        + 48*(Y*(U - (2*Y-1))^2)
        + (4656/55)*(Y^2*(U - (2*Y-1))^2)
        + (288/5)*(Y^3*(U - (2*Y-1))^2)
        + (543/11)*(U*(U + (2*Y-1))^2)
        + (228/11)*(U*Y*(U + (2*Y-1))^2)
        + (564/5)*(U*Y^2*(U - (2*Y-1))^2)
        + (486/55)*(Y^2*(U - 2*(2*Y-1))^2)
        + (48/5)*(Y^3*(U - 2*(2*Y-1))^2)
        + (17/2)*(U^2*(U + 2*(2*Y-1))^2)
        + (1/2)*(U^2*(U + 4*(2*Y-1))^2) := by ring
  rw [e]
  have h2 : (0:ℝ) ≤ Y^2 := sq_nonneg Y
  have h3 : (0:ℝ) ≤ Y^3 := by positivity
  positivity

set_option maxHeartbeats 2000000 in
/-- The `(B,x)` form.  Taking `U = B/(1-B)` in `kernelUY_nonneg` and multiplying by
`(1-B)^4 > 0` recovers the target exactly. -/
theorem kernelBx_nonneg (B x : ℝ) (hB : 0 ≤ B) (hB1 : B < 1) (hx : 0 ≤ x) :
    0 ≤ 96*(1-B)^4*x^6 + 192*(1-B)^4*x^5 + 96*(1-B)^4*x^4
      + 144*(1-B)^3*x^4 + 144*(1-B)^3*x^3 + 54*(1-B)^2*x^2
      - 384*(1-B)^2*x^3 - 384*(1-B)^2*x^2 - 288*(1-B)*x
      + 300*(1-B)*x^2 + 300*(1-B)*x + 9 := by
  have h1B : 0 < 1 - B := by linarith
  have hU : 0 ≤ B / (1 - B) := by positivity
  have hcert := kernelUY_nonneg (B / (1 - B)) x hU hx
  have h4 : (0:ℝ) < (1 - B)^4 := by positivity
  -- the (U,Y) polynomial times (1-B)^4 equals the target
  have key : ((1 - B)^4) *
      (9*(B/(1-B))^4 + 300*(B/(1-B))^3*x^2 + 12*(B/(1-B))^3*x + 36*(B/(1-B))^3
        - 384*(B/(1-B))^2*x^3 + 570*(B/(1-B))^2*x^2 + 36*(B/(1-B))^2*x
        + 54*(B/(1-B))^2 + 144*(B/(1-B))*x^4 - 624*(B/(1-B))*x^3
        + 240*(B/(1-B))*x^2 + 36*(B/(1-B))*x + 36*(B/(1-B))
        + 96*x^6 + 192*x^5 + 240*x^4 - 240*x^3 - 30*x^2 + 12*x + 9)
      = 96*(1-B)^4*x^6 + 192*(1-B)^4*x^5 + 96*(1-B)^4*x^4
        + 144*(1-B)^3*x^4 + 144*(1-B)^3*x^3 + 54*(1-B)^2*x^2
        - 384*(1-B)^2*x^3 - 384*(1-B)^2*x^2 - 288*(1-B)*x
        + 300*(1-B)*x^2 + 300*(1-B)*x + 9 := by
    field_simp
    ring
  rw [← key]
  exact mul_nonneg h4.le hcert

open SSP.K3S4Renewal

/-- The order-three `k = 3` gap of a kernel `(m₁,m₂,m₃,m₄)`. -/
noncomputable def gap3 (m₂ m₃ m₄ : ℝ) : ℝ := 5 * m₂ * m₄ - 6 * m₃ ^ 2

/-- Abbreviations for the `D`-quadratic coefficients of the `F = 0` face. -/
private noncomputable def Sfac (B x : ℝ) : ℝ := 4*B*x^2 + 4*B*x - 4*x^2 - 4*x - 3

set_option maxHeartbeats 2000000 in
/-- `S < 0` on the box. -/
private theorem Sfac_neg (B x : ℝ) (hB1 : B ≤ 1) (hx : 0 < x) : Sfac B x < 0 := by
  unfold Sfac
  nlinarith [sub_nonneg.mpr hB1, hx.le, mul_nonneg (sub_nonneg.mpr hB1) hx.le,
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hB1) hx.le) hx.le]

set_option maxHeartbeats 2000000 in
/-- If `S + 8 > 0` then the `D`-linear coefficient's cofactor `T` is nonpositive. -/
private theorem T_nonpos_of (B x : ℝ) (hB : 0 ≤ B) (hB1 : B ≤ 1) (hx : 0 < x)
    (hS2 : 0 < Sfac B x + 8) :
    4*B^2*x^3 + 4*B^2*x^2 - 8*B*x^3 - 8*B*x^2 - 3*B*x + 4*x^3 + 4*x^2 + 3*x - 8 ≤ 0 := by
  unfold Sfac at hS2
  nlinarith [hB, hx.le, sub_nonneg.mpr hB1, hS2, mul_pos hx hx,
    mul_nonneg hB hx.le, mul_nonneg (sub_nonneg.mpr hB1) hx.le,
    mul_nonneg (mul_nonneg hB hx.le) hx.le,
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hB1) hx.le) hx.le,
    sq_nonneg (2*x-1), sq_nonneg (B*x - x), mul_nonneg hB hB]

set_option maxHeartbeats 2000000 in
/-- **The `F = 0` face.**  The `k=3` order-three kernel with the third input slack maximal,
for `B, D ∈ [0,1]`, `x > 0`.  Convex in `D`; the dichotomy is on the sign of `S + 8`.

* If `S + 8 ≤ 0` the discriminant `c₁² − 4c₂c₀` is `≤ 0`, so `4c₂·P` is a perfect square
  plus a nonnegative term and `P ≥ 0` for **every** real `D`.
* If `S + 8 > 0` then `T ≤ 0`, hence `c₁ ≥ 0`, so `P` is increasing on `D ≥ 0` and
  `P(D) ≥ P(0)`, which is `kernelBx_nonneg`. -/
theorem face_F0_nonneg (B D x : ℝ) (hB : 0 ≤ B) (hB1 : B ≤ 1)
    (hD : 0 ≤ D) (_hD1 : D ≤ 1) (hx : 0 < x) :
    0 ≤ 96*(1-B)^4*(1-D)^2*x^6 + 192*(1-B)^4*(1-D)^2*x^5 + 96*(1-B)^4*(1-D)^2*x^4
      + 144*(1-B)^3*(1-D)^2*x^4 + 144*(1-B)^3*(1-D)^2*x^3 + 54*(1-B)^2*(1-D)^2*x^2
      - 384*(1-B)^2*(1-D)*x^3 - 384*(1-B)^2*(1-D)*x^2 - 288*(1-B)*(1-D)*x
      + 300*(1-B)*x^2 + 300*(1-B)*x + 9 := by
  rcases eq_or_lt_of_le hB1 with hB1e | hBlt
  · subst hB1e; norm_num
  have hker := kernelBx_nonneg B x hB hBlt hx.le
  set S : ℝ := 4*B*x^2 + 4*B*x - 4*x^2 - 4*x - 3 with hSd
  set T : ℝ := 4*B^2*x^3 + 4*B^2*x^2 - 8*B*x^3 - 8*B*x^2 - 3*B*x
                 + 4*x^3 + 4*x^2 + 3*x - 8 with hTd
  set c2 : ℝ := 6*x^2*(1-B)^2*S^2 with hc2d
  set c1 : ℝ := 12*x*(1-B)*S*T with hc1d
  set c0 : ℝ := 96*(1-B)^4*x^6 + 192*(1-B)^4*x^5 + 96*(1-B)^4*x^4
      + 144*(1-B)^3*x^4 + 144*(1-B)^3*x^3 + 54*(1-B)^2*x^2
      - 384*(1-B)^2*x^3 - 384*(1-B)^2*x^2 - 288*(1-B)*x
      + 300*(1-B)*x^2 + 300*(1-B)*x + 9 with hc0d
  have hc0 : 0 ≤ c0 := by rw [hc0d]; exact hker
  -- the target is exactly c0 + D*(c1 + c2*D)
  have hPeq : 96*(1-B)^4*(1-D)^2*x^6 + 192*(1-B)^4*(1-D)^2*x^5
        + 96*(1-B)^4*(1-D)^2*x^4 + 144*(1-B)^3*(1-D)^2*x^4
        + 144*(1-B)^3*(1-D)^2*x^3 + 54*(1-B)^2*(1-D)^2*x^2
        - 384*(1-B)^2*(1-D)*x^3 - 384*(1-B)^2*(1-D)*x^2 - 288*(1-B)*(1-D)*x
        + 300*(1-B)*x^2 + 300*(1-B)*x + 9
      = c0 + D * (c1 + c2 * D) := by
    rw [hc0d, hc1d, hc2d, hSd, hTd]; ring
  rw [hPeq]
  have hc2nn : 0 ≤ c2 := by rw [hc2d]; positivity
  rcases le_or_gt (S + 8) 0 with hS2 | hS2
  · -- discriminant branch: 4*c2*(c0 + D*(c1+c2*D)) = (2*c2*D+c1)^2 + (4*c2*c0 - c1^2)
    have hdisc : 0 ≤ 4*c2*c0 - c1^2 := by
      have hid : 4*c2*c0 - c1^2 = -1800*x^2*(1-B)^2*S^2*(S+8) := by
        rw [hc2d, hc1d, hc0d, hSd, hTd]; ring
      rw [hid]
      have h1 : (0:ℝ) ≤ 1800*x^2*(1-B)^2*S^2 := by positivity
      nlinarith [h1, hS2]
    have hkey : 4*c2*(c0 + D*(c1 + c2*D)) = (2*c2*D + c1)^2 + (4*c2*c0 - c1^2) := by ring
    rcases eq_or_lt_of_le hc2nn with hc2z | hc2p
    · -- c2 = 0 forces S = 0, impossible since S < 0
      exfalso
      have hSneg : S < 0 := by
        rw [hSd]
        nlinarith [sub_nonneg.mpr hB1, hx.le, mul_nonneg (sub_nonneg.mpr hB1) hx.le,
          mul_nonneg (mul_nonneg (sub_nonneg.mpr hB1) hx.le) hx.le]
      have h1B : 0 < 1 - B := by linarith
      have hSne : S ≠ 0 := ne_of_lt hSneg
      have hpos : (0:ℝ) < 6*x^2*(1-B)^2*S^2 := by positivity
      rw [← hc2d] at hpos; linarith
    · nlinarith [hkey, sq_nonneg (2*c2*D + c1), hdisc, hc2p]
  · -- monotone branch: T ≤ 0 and S < 0 give c1 ≥ 0
    have hT : 4*B^2*x^3 + 4*B^2*x^2 - 8*B*x^3 - 8*B*x^2 - 3*B*x
          + 4*x^3 + 4*x^2 + 3*x - 8 ≤ 0 := by
      apply T_nonpos_of B x hB hB1 hx
      unfold Sfac
      rw [hSd] at hS2
      linarith
    have hSneg : S < 0 := by
      rw [hSd]
      nlinarith [sub_nonneg.mpr hB1, hx.le, mul_nonneg (sub_nonneg.mpr hB1) hx.le,
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hB1) hx.le) hx.le]
    have hc1nn : 0 ≤ c1 := by
      rw [hc1d]
      have h1B : 0 < 1 - B := by linarith
      have hTle : T ≤ 0 := by rw [hTd]; linarith
      have : 0 ≤ (-S) * (-T) := mul_nonneg (by linarith) (by linarith)
      nlinarith [this, mul_pos hx h1B]
    have : 0 ≤ D * (c1 + c2 * D) :=
      mul_nonneg hD (by nlinarith [hc1nn, hc2nn, mul_nonneg hc2nn hD])
    linarith

set_option maxHeartbeats 2000000 in
/-- The `F = 1` face (`f = 0`): the whole expression collapses to `225 - 300B(x²+x) + 300(x²+x)`
up to the factored form below, immediate for `B ≤ 1`. -/
theorem face_F1_nonneg (B _D x : ℝ) (hB1 : B ≤ 1) (hx : 0 < x) :
    0 ≤ 300*(1-B)*x^2 + 300*(1-B)*x + 225 := by
  nlinarith [hx.le, sub_nonneg.mpr hB1, mul_nonneg (sub_nonneg.mpr hB1) hx.le,
    mul_nonneg (mul_nonneg hx.le hx.le) (sub_nonneg.mpr hB1)]

set_option maxHeartbeats 2000000 in
/-- A quantity affine in `t` and nonnegative at both endpoints of `[0,1]` is nonnegative. -/
theorem affine_nonneg_of_endpoints (g h t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (h0 : 0 ≤ g) (h1 : 0 ≤ g + h) : 0 ≤ g + t * h := by
  rcases le_total 0 h with hp | hn
  · exact add_nonneg h0 (mul_nonneg ht hp)
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (neg_nonneg.mpr hn)]

set_option maxHeartbeats 2000000 in
/-- **The full three-slack kernel inequality.**  For `B, D, F ∈ [0,1]` and `x > 0`, the
13-term reparametrised `k = 3` order-three gap numerator is nonnegative.  Affine in `F`, so
the two faces `F = 0` (`face_F0_nonneg`) and `F = 1` (`face_F1_nonneg`) suffice. -/
theorem kernel13_nonneg (B D F x : ℝ) (hB : 0 ≤ B) (hB1 : B ≤ 1)
    (hD : 0 ≤ D) (hD1 : D ≤ 1) (hF : 0 ≤ F) (hF1 : F ≤ 1) (hx : 0 < x) :
    0 ≤ 96*(1-B)^4*(1-D)^2*(1-F)*x^6 + 192*(1-B)^4*(1-D)^2*(1-F)*x^5
      + 96*(1-B)^4*(1-D)^2*(1-F)*x^4 + 144*(1-B)^3*(1-D)^2*(1-F)*x^4
      + 144*(1-B)^3*(1-D)^2*(1-F)*x^3 + 54*(1-B)^2*(1-D)^2*(1-F)*x^2
      - 384*(1-B)^2*(1-D)*(1-F)*x^3 - 384*(1-B)^2*(1-D)*(1-F)*x^2
      - 288*(1-B)*(1-D)*(1-F)*x + 300*(1-B)*x^2 + 300*(1-B)*x
      - 216*(1-F) + 225 := by
  have h0 := face_F0_nonneg B D x hB hB1 hD hD1 hx
  have h1 := face_F1_nonneg B D x hB1 hx
  have hsplit : 96*(1-B)^4*(1-D)^2*(1-F)*x^6 + 192*(1-B)^4*(1-D)^2*(1-F)*x^5
      + 96*(1-B)^4*(1-D)^2*(1-F)*x^4 + 144*(1-B)^3*(1-D)^2*(1-F)*x^4
      + 144*(1-B)^3*(1-D)^2*(1-F)*x^3 + 54*(1-B)^2*(1-D)^2*(1-F)*x^2
      - 384*(1-B)^2*(1-D)*(1-F)*x^3 - 384*(1-B)^2*(1-D)*(1-F)*x^2
      - 288*(1-B)*(1-D)*(1-F)*x + 300*(1-B)*x^2 + 300*(1-B)*x
      - 216*(1-F) + 225
      = (96*(1-B)^4*(1-D)^2*x^6 + 192*(1-B)^4*(1-D)^2*x^5 + 96*(1-B)^4*(1-D)^2*x^4
        + 144*(1-B)^3*(1-D)^2*x^4 + 144*(1-B)^3*(1-D)^2*x^3 + 54*(1-B)^2*(1-D)^2*x^2
        - 384*(1-B)^2*(1-D)*x^3 - 384*(1-B)^2*(1-D)*x^2 - 288*(1-B)*(1-D)*x
        + 300*(1-B)*x^2 + 300*(1-B)*x + 9)
      + F * ((300*(1-B)*x^2 + 300*(1-B)*x + 225)
        - (96*(1-B)^4*(1-D)^2*x^6 + 192*(1-B)^4*(1-D)^2*x^5 + 96*(1-B)^4*(1-D)^2*x^4
          + 144*(1-B)^3*(1-D)^2*x^4 + 144*(1-B)^3*(1-D)^2*x^3 + 54*(1-B)^2*(1-D)^2*x^2
          - 384*(1-B)^2*(1-D)*x^3 - 384*(1-B)^2*(1-D)*x^2 - 288*(1-B)*(1-D)*x
          + 300*(1-B)*x^2 + 300*(1-B)*x + 9)) := by ring
  rw [hsplit]
  exact affine_nonneg_of_endpoints _ _ F hF hF1 h0 (by linarith)

set_option maxHeartbeats 2000000 in
/-- **The no-return face, proved.**  Substituting the slack ratios
`B = (3/2)v²/b`, `D = (4/3)B²/(vd)`, `F = (5/4)D²/(Bf)` with `b,d,f ∈ (0,1]` turns the
hypotheses into exactly those bounds, and the gap into `K13/(4b⁴d²f)` where `K13` is the
13-term numerator proved nonnegative in `kernel13_nonneg`. -/
theorem gap3_noReturn_nonneg' (x v B D F : ℝ)
    (hx : 0 < x) (hv : 0 < v)
    (hAS : 3 * v ^ 2 ≤ 2 * B)
    (hk2 : 4 * B ^ 2 ≤ 3 * v * D)
    (hk3 : 5 * D ^ 2 ≤ 4 * B * F) :
    0 ≤ gap3 (kernelM2 x v B) (kernelM3 x v B D) (kernelM4 x v B D F) := by
  have hBpos : 0 < B := by nlinarith [sq_nonneg v]
  have hDpos : 0 < D := by nlinarith [sq_nonneg B]
  have hFpos : 0 < F := by nlinarith [sq_nonneg D]
  -- the slack ratios
  set bb : ℝ := 3*v^2/(2*B) with hbb
  set dd : ℝ := 4*B^2/(3*v*D) with hdd
  set ff : ℝ := 5*D^2/(4*B*F) with hff
  have hbb0 : 0 < bb := by rw [hbb]; positivity
  have hbb1 : bb ≤ 1 := by rw [hbb, div_le_one (by positivity)]; linarith
  have hdd0 : 0 < dd := by rw [hdd]; positivity
  have hdd1 : dd ≤ 1 := by rw [hdd, div_le_one (by positivity)]; linarith
  have hff0 : 0 < ff := by rw [hff]; positivity
  have hff1 : ff ≤ 1 := by rw [hff, div_le_one (by positivity)]; linarith
  -- apply the kernel inequality at B = 1-bb etc.
  have hker := kernel13_nonneg (1-bb) (1-dd) (1-ff) x (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) hx
  simp only [sub_sub_cancel] at hker
  -- `hker` is K13 at (bb,dd,ff); the gap is K13/(4 bb^4 dd^2 ff).
  have hden : (0:ℝ) < 4*bb^4*dd^2*ff := by positivity
  have hkey : (4*bb^4*dd^2*ff) *
      gap3 (kernelM2 x v B) (kernelM3 x v B D) (kernelM4 x v B D F)
      = 96*bb^4*dd^2*ff*v^2*x^4 + 192*bb^4*dd^2*ff*v*x^5 + 96*bb^4*dd^2*ff*x^6
        + 144*bb^3*dd^2*ff*v^3*x^3 + 144*bb^3*dd^2*ff*v^2*x^4
        + 54*bb^2*dd^2*ff*v^4*x^2 - 384*bb^2*dd*ff*v^4*x^2
        - 384*bb^2*dd*ff*v^3*x^3 - 288*bb*dd*ff*v^5*x
        + 300*bb*v^5*x + 300*bb*v^4*x^2 - 216*ff*v^6 + 225*v^6 := by
    unfold gap3 kernelM2 kernelM3 kernelM4
    rw [hbb, hdd, hff]
    field_simp
    ring
  have hRHS : (0:ℝ) ≤ 96*bb^4*dd^2*ff*v^2*x^4 + 192*bb^4*dd^2*ff*v*x^5
      + 96*bb^4*dd^2*ff*x^6 + 144*bb^3*dd^2*ff*v^3*x^3 + 144*bb^3*dd^2*ff*v^2*x^4
      + 54*bb^2*dd^2*ff*v^4*x^2 - 384*bb^2*dd*ff*v^4*x^2
      - 384*bb^2*dd*ff*v^3*x^3 - 288*bb*dd*ff*v^5*x
      + 300*bb*v^5*x + 300*bb*v^4*x^2 - 216*ff*v^6 + 225*v^6 := by
    -- K13 is homogeneous of degree 6 in (x,v); rescale to v = 1 via x ↦ x/v
    have h1 := kernel13_nonneg (1-bb) (1-dd) (1-ff) (x/v)
      (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by positivity)
    simp only [sub_sub_cancel] at h1
    have hv6 : (0:ℝ) < v^6 := by positivity
    have hscale : 96*bb^4*dd^2*ff*v^2*x^4 + 192*bb^4*dd^2*ff*v*x^5
        + 96*bb^4*dd^2*ff*x^6 + 144*bb^3*dd^2*ff*v^3*x^3 + 144*bb^3*dd^2*ff*v^2*x^4
        + 54*bb^2*dd^2*ff*v^4*x^2 - 384*bb^2*dd*ff*v^4*x^2
        - 384*bb^2*dd*ff*v^3*x^3 - 288*bb*dd*ff*v^5*x
        + 300*bb*v^5*x + 300*bb*v^4*x^2 - 216*ff*v^6 + 225*v^6
        = v^6 * (96*bb^4*dd^2*ff*(x/v)^6 + 192*bb^4*dd^2*ff*(x/v)^5
          + 96*bb^4*dd^2*ff*(x/v)^4 + 144*bb^3*dd^2*ff*(x/v)^4
          + 144*bb^3*dd^2*ff*(x/v)^3 + 54*bb^2*dd^2*ff*(x/v)^2
          - 384*bb^2*dd*ff*(x/v)^3 - 384*bb^2*dd*ff*(x/v)^2
          - 288*bb*dd*ff*(x/v) + 300*bb*(x/v)^2 + 300*bb*(x/v)
          - 216*ff + 225) := by
      field_simp
      ring
    rw [hscale]
    exact mul_nonneg hv6.le h1
  nlinarith [hkey, hRHS, hden]

set_option maxHeartbeats 2000000 in
/-- **The no-return face.**  When absorption occurs on the first excursion, the law is the
independent sum of one exponential holding time of mean `x` and a terminal excursion of order
at most two.  Given Aldous--Shepp and the two order-two hierarchy inputs for that excursion,
the order-three `k = 3` gap is nonnegative.

This is the tight case: equality is approached as `(A,C,E)` meet their three bounds
simultaneously with `v = 2x`, which is the three-stage Erlang law. -/
theorem gap3_noReturn_nonneg (x v B D F : ℝ)
    (hx : 0 < x) (hv : 0 < v)
    (hAS : 3 * v ^ 2 ≤ 2 * B)
    (hk2 : 4 * B ^ 2 ≤ 3 * v * D)
    (hk3 : 5 * D ^ 2 ≤ 4 * B * F) :
    0 ≤ gap3 (kernelM2 x v B) (kernelM3 x v B D) (kernelM4 x v B D F) := by
  exact gap3_noReturn_nonneg' x v B D F hx hv hAS hk2 hk3

/-! ## Reduction of `gap3_noReturn_nonneg`, and what remains

Reparametrising by the *slack ratios* rather than the slacks themselves gives a far more
compact target.  Writing

  `B = (3/2) v² / b`,  `D = (4/3) B² / (v d)`,  `F = (5/4) D² / (B f)`,

the three input hypotheses become exactly `b, d, f ∈ (0,1]`, and clearing denominators (the
denominator is `4 b⁴ d² f > 0`) turns the gap into a polynomial with only **thirteen** terms,
homogeneous of degree six in `(x, v)`:

  `96b⁴d²f v²x⁴ + 192b⁴d²f vx⁵ + 96b⁴d²f x⁶`
  `+ 144b³d²f v³x³ + 144b³d²f v²x⁴ + 54b²d²f v⁴x²`
  `− 384b²df v⁴x² − 384b²df v³x³ − 288bdf v⁵x`
  `+ 300b v⁵x + 300b v⁴x² − 216f v⁶ + 225v⁶ ≥ 0.`

Normalising `v = 1` and substituting `b = 1−B`, `d = 1−D`, `f = 1−F` with `B, D, F ∈ [0,1)`,
the polynomial is **affine in `F`**, so by `affine_nonneg_of_endpoints` it suffices to treat
the two faces `F = 0` and `F = 1`; the same argument in `D` (degree two there, but the
endpoint values are what matter) leaves four faces.  Three of the four are discharged
automatically by `nlinarith`:

* `F = 1` (the `k = 3` input slack maximal): minimum `225`;
* `F = 0, D = 1`: minimum `9`, and the polynomial is only linear in `B` there;
* `F = 1, D = 0`: likewise immediate.

The `F = 0` face is still quadratic in `D` (not affine, as an earlier note here wrongly
said).  Its structure is now fully determined:

* the `D²` coefficient is `6x²(1−B)²S²` with `S = 4Bx²+4Bx−4x²−4x−3`, hence `≥ 0`, so the
  face is **convex** in `D`.  Convexity means it lies *below* its chord, so the two
  endpoints `D = 0, 1` do **not** suffice;
* the `D = 0` endpoint is *exactly* `kernelBx_nonneg` above — certified;
* the `D = 1` endpoint is `−3(100Bx²+100Bx−100x²−100x−3)`, immediate;
* the vertex `−c₁/(2c₂)` never lies in `[0,1]` where the discriminant is positive
  (checked over 2·10⁶ samples: it is `< 0` in all but a `1.6·10⁻⁶` fraction, where it is
  `> 1`), so the minimum over `D ∈ [0,1]` is always at `D = 0`.  But `c₁` itself changes
  sign, so "increasing on `[0,1]`" is not available as a one-line argument.

So what remains is exactly: a Lean-checkable proof that the vertex of this convex quadratic
lies outside `[0,1]`, or equivalently a direct certificate for the three-variable `F = 0`
face.  LP searches over generator sets in the cleared chart `B = U/(1+U)`, `D = V/(1+V)`,
`x = Y` (49 terms, degree 7, zero isolated at `U = V = 0, Y = 1/2`) came back infeasible at
the bases tried, including ones where every generator vanishes at that zero.

`verify_k3_s3_kernel.sing` continues to settle the whole inequality by exact root isolation,
so nonnegativity is not in doubt; only this last reduction step lacks a Lean certificate. -/

open SSP.K3S4Renewal

end SSP.K3S3
