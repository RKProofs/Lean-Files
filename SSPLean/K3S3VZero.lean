import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic

/-!
# The `v = 0` (direct-absorption) branch of the order-three `k = 3` base case

In the state-return decomposition at `n = 3`, one branch has the terminal excursion equal to
an atom at zero (absorption happens on the first departure).  There the parent moments are
those of a geometric number of return cycles followed by a bare holding time.

In the slack-ratio chart of `SSPLean.K3S3` (`A = (3/2)u²/b`, `C = (4/3)A²/(ub)`,
`E = (5/4)C²/(Af)`, normalised to `u = 1`), the gap numerator is a degree-6 polynomial in
`r = p/q` whose coefficients are **separately** nonnegative.  Only the `r²` and `r³`
coefficients have any negative terms, and each closes by two elementary pairings:

* `200bx − 192bdfx = bx(200 − 192df) ≥ 8bx` using `df ≤ 1`;
* `75 − 72f ≥ 3` using `f ≤ 1`;
* `100 − 192df + 135d²f ≥ 31` on the unit square;

with an all-positive-coefficient remainder in each case.  The two lemmas below are those
coefficients; the remaining `r`-coefficients have no negative terms at all.
-/

set_option maxHeartbeats 800000 in
/-- The `r²` coefficient of the `v = 0` branch: two pairings plus a positive remainder. -/
theorem vzero_r2_nonneg (x b d f : ℝ) (hx : 0 ≤ x) (hb : 0 ≤ b)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hf : 0 ≤ f) (hf1 : f ≤ 1) :
    0 ≤ 480*b^4*d^2*f*x^6 + 960*b^4*d^2*f*x^5 + 480*b^4*d^2*f*x^4
      + 384*b^3*d^2*f*x^4 + 384*b^3*d^2*f*x^3 + 72*b^2*d^2*f*x^2
      + 96*b^2*d*f*x^3 + 96*b^2*d*f*x^2 - 192*b*d*f*x
      + 200*b*x^2 + 200*b*x - 72*f + 75 := by
  have hdf : d * f ≤ 1 := by nlinarith
  have hpair1 : 0 ≤ 200*b*x - 192*b*d*f*x := by nlinarith [mul_nonneg hb hx, hdf]
  have hpair2 : 0 ≤ 75 - 72*f := by linarith
  have hrest : 0 ≤ 480*b^4*d^2*f*x^6 + 960*b^4*d^2*f*x^5 + 480*b^4*d^2*f*x^4
      + 384*b^3*d^2*f*x^4 + 384*b^3*d^2*f*x^3 + 72*b^2*d^2*f*x^2
      + 96*b^2*d*f*x^3 + 96*b^2*d*f*x^2 + 200*b*x^2 := by positivity
  linarith

set_option maxHeartbeats 800000 in
/-- The `r³` coefficient of the `v = 0` branch (divided by `3b`). -/
theorem vzero_r3_nonneg (x b d f : ℝ) (hx : 0 ≤ x) (hb : 0 ≤ b)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hf : 0 ≤ f) (hf1 : f ≤ 1) :
    0 ≤ 640*b^3*d^2*f*x^6 + 1920*b^3*d^2*f*x^5 + 1920*b^3*d^2*f*x^4
      + 640*b^3*d^2*f*x^3 + 576*b^2*d^2*f*x^4 + 1152*b^2*d^2*f*x^3
      + 576*b^2*d^2*f*x^2 + 144*b*d^2*f*x^2 + 144*b*d^2*f*x
      + 96*b*d*f*x^3 + 192*b*d*f*x^2 + 96*b*d*f*x
      + 135*d^2*f - 192*d*f*x - 192*d*f + 100*x^2 + 200*x + 100 := by
  have hdf : d * f ≤ 1 := by nlinarith
  have hpair1 : 0 ≤ 200*x - 192*d*f*x := by nlinarith [hx, hdf]
  have hpair2 : 0 ≤ 100 - 192*d*f + 135*d^2*f := by
    nlinarith [hd, hf, sub_nonneg.mpr hd1, sub_nonneg.mpr hf1,
      mul_nonneg hd hf, sq_nonneg (d - 1), mul_nonneg hf (sq_nonneg (d-1)),
      mul_nonneg hd (sub_nonneg.mpr hf1)]
  have hrest : 0 ≤ 640*b^3*d^2*f*x^6 + 1920*b^3*d^2*f*x^5 + 1920*b^3*d^2*f*x^4
      + 640*b^3*d^2*f*x^3 + 576*b^2*d^2*f*x^4 + 1152*b^2*d^2*f*x^3
      + 576*b^2*d^2*f*x^2 + 144*b*d^2*f*x^2 + 144*b*d^2*f*x
      + 96*b*d*f*x^3 + 192*b*d*f*x^2 + 96*b*d*f*x + 100*x^2 := by positivity
  linarith

set_option maxHeartbeats 800000 in
/-- **The `v = 0` branch at order three.**  The gap numerator in the slack-ratio chart,
normalised to `u = 1`, is nonnegative: its `r`-coefficients split into four with no negative
terms at all and the two handled by `vzero_r2_nonneg` / `vzero_r3_nonneg`. -/
theorem vzero_branch_nonneg (r x bu du fu : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x)
    (hb : 0 ≤ bu) (hd : 0 ≤ du) (hd1 : du ≤ 1) (hf : 0 ≤ fu) (hf1 : fu ≤ 1) :
    0 ≤ 96*bu^4*du^2*fu*r^6*x^6 + 576*bu^4*du^2*fu*r^6*x^5 + 1440*bu^4*du^2*fu*r^6*x^4 + 1920*bu^4*du^2*fu*r^6*x^3 + 1440*bu^4*du^2*fu*r^6*x^2 + 576*bu^4*du^2*fu*r^6*x + 96*bu^4*du^2*fu*r^6 + 576*bu^4*du^2*fu*r^5*x^6 + 2880*bu^4*du^2*fu*r^5*x^5 + 5760*bu^4*du^2*fu*r^5*x^4 + 5760*bu^4*du^2*fu*r^5*x^3 + 2880*bu^4*du^2*fu*r^5*x^2 + 576*bu^4*du^2*fu*r^5*x + 1440*bu^4*du^2*fu*r^4*x^6 + 5760*bu^4*du^2*fu*r^4*x^5 + 8640*bu^4*du^2*fu*r^4*x^4 + 5760*bu^4*du^2*fu*r^4*x^3 + 1440*bu^4*du^2*fu*r^4*x^2 + 1920*bu^4*du^2*fu*r^3*x^6 + 5760*bu^4*du^2*fu*r^3*x^5 + 5760*bu^4*du^2*fu*r^3*x^4 + 1920*bu^4*du^2*fu*r^3*x^3 + 1440*bu^4*du^2*fu*r^2*x^6 + 2880*bu^4*du^2*fu*r^2*x^5 + 1440*bu^4*du^2*fu*r^2*x^4 + 576*bu^4*du^2*fu*r*x^6 + 576*bu^4*du^2*fu*r*x^5 + 96*bu^4*du^2*fu*x^6 + 288*bu^3*du^2*fu*r^5*x^4 + 1152*bu^3*du^2*fu*r^5*x^3 + 1728*bu^3*du^2*fu*r^5*x^2 + 1152*bu^3*du^2*fu*r^5*x + 288*bu^3*du^2*fu*r^5 + 1152*bu^3*du^2*fu*r^4*x^4 + 3456*bu^3*du^2*fu*r^4*x^3 + 3456*bu^3*du^2*fu*r^4*x^2 + 1152*bu^3*du^2*fu*r^4*x + 1728*bu^3*du^2*fu*r^3*x^4 + 3456*bu^3*du^2*fu*r^3*x^3 + 1728*bu^3*du^2*fu*r^3*x^2 + 1152*bu^3*du^2*fu*r^2*x^4 + 1152*bu^3*du^2*fu*r^2*x^3 + 288*bu^3*du^2*fu*r*x^4 + 216*bu^2*du^2*fu*r^4*x^2 + 432*bu^2*du^2*fu*r^4*x + 216*bu^2*du^2*fu*r^4 + 432*bu^2*du^2*fu*r^3*x^2 + 432*bu^2*du^2*fu*r^3*x + 216*bu^2*du^2*fu*r^2*x^2 + 96*bu^2*du*fu*r^4*x^3 + 288*bu^2*du*fu*r^4*x^2 + 288*bu^2*du*fu*r^4*x + 96*bu^2*du*fu*r^4 + 288*bu^2*du*fu*r^3*x^3 + 576*bu^2*du*fu*r^3*x^2 + 288*bu^2*du*fu*r^3*x + 288*bu^2*du*fu*r^2*x^3 + 288*bu^2*du*fu*r^2*x^2 + 96*bu^2*du*fu*r*x^3 + 405*bu*du^2*fu*r^3 - 576*bu*du*fu*r^3*x - 576*bu*du*fu*r^3 - 576*bu*du*fu*r^2*x + 300*bu*r^3*x^2 + 600*bu*r^3*x + 300*bu*r^3 + 600*bu*r^2*x^2 + 600*bu*r^2*x + 300*bu*r*x^2 - 216*fu*r^2 + 225*r^2 := by
  have h2 := vzero_r2_nonneg x bu du fu hx hb hd hd1 hf hf1
  have h3 := vzero_r3_nonneg x bu du fu hx hb hd hd1 hf hf1
  have hpos : (0:ℝ) ≤ (96*bu^4*du^2*fu*x^6 + 576*bu^4*du^2*fu*x^5 + 1440*bu^4*du^2*fu*x^4 + 1920*bu^4*du^2*fu*x^3 + 1440*bu^4*du^2*fu*x^2 + 576*bu^4*du^2*fu*x + 96*bu^4*du^2*fu)*r^6 + (576*bu^4*du^2*fu*x^6 + 2880*bu^4*du^2*fu*x^5 + 5760*bu^4*du^2*fu*x^4 + 5760*bu^4*du^2*fu*x^3 + 2880*bu^4*du^2*fu*x^2 + 576*bu^4*du^2*fu*x + 288*bu^3*du^2*fu*x^4 + 1152*bu^3*du^2*fu*x^3 + 1728*bu^3*du^2*fu*x^2 + 1152*bu^3*du^2*fu*x + 288*bu^3*du^2*fu)*r^5 + (1440*bu^4*du^2*fu*x^6 + 5760*bu^4*du^2*fu*x^5 + 8640*bu^4*du^2*fu*x^4 + 5760*bu^4*du^2*fu*x^3 + 1440*bu^4*du^2*fu*x^2 + 1152*bu^3*du^2*fu*x^4 + 3456*bu^3*du^2*fu*x^3 + 3456*bu^3*du^2*fu*x^2 + 1152*bu^3*du^2*fu*x + 216*bu^2*du^2*fu*x^2 + 432*bu^2*du^2*fu*x + 216*bu^2*du^2*fu + 96*bu^2*du*fu*x^3 + 288*bu^2*du*fu*x^2 + 288*bu^2*du*fu*x + 96*bu^2*du*fu)*r^4 + (576*bu^4*du^2*fu*x^6 + 576*bu^4*du^2*fu*x^5 + 288*bu^3*du^2*fu*x^4 + 96*bu^2*du*fu*x^3 + 300*bu*x^2)*r^1 + (96*bu^4*du^2*fu*x^6)*r^0 := by positivity
  have hr2 : (0:ℝ) ≤ r^2 := sq_nonneg r
  have hr3 : (0:ℝ) ≤ r^3 := by positivity
  nlinarith [hpos, mul_nonneg hr2 h2, mul_nonneg (mul_nonneg hr3 hb) h3, hr, hb]
